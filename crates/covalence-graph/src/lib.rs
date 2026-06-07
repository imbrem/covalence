//! Ordered, typed, payload-polymorphic graph.
//!
//! See `wit/graph.wit` for the canonical interface. The Rust side is
//! generic in the payload type `P`; the WIT side fixes `P = Bytes`.
//!
//! # Order and the premonoidal reading
//!
//! Nodes form an *ordered sequence* — first added, first initialized.
//! Two graphs with the same `(nodes-as-set, edges-as-set)` but a
//! different *insertion order* are not equal. This is deliberate:
//! the intended interpretation is a symmetric **premonoidal** category
//! (Power & Robinson 1997). In a strict-monoidal world parallel
//! composition `A ⊗ B` would be reorderable; with effects (any
//! initializer can have side-effects: open a file, allocate a port,
//! start a worker), reordering `A ⊗ B` and `B ⊗ A` changes the
//! observable program. The graph keeps the order so that
//! WASM-component initialization, string-diagram evaluation, and any
//! other consumer can run nodes in the order the author wrote.
//!
//! # Node kinds
//!
//! Every node carries a [`NodeKind`] — a *fixed*, built-in enum
//! distinguishing pure (commuting) nodes from ordered (effectful)
//! nodes. The graph machinery treats [`NodeKind::Ordered`] specially:
//! consecutive ordered nodes are connected by an implicit "state
//! wire" (rendered in red in the string-diagram view). The kind is
//! not a per-instance attribute — it's a structural property of the
//! node, and the encoding reserves one byte so the set can grow with
//! more built-in kinds later without breaking the wire format.
//!
//! # Graph-level ordered/unordered tag via keyed hash
//!
//! There is no `ordered` field on `Graph` itself. Instead, the *same*
//! canonical bytes can be hashed under two different BLAKE3 domains:
//! [`Graph::ordered_hash`] (treat the graph as a premonoidal — order
//! significant) and [`Graph::unordered_hash`] (treat it as symmetric
//! monoidal — order is incidental). Same content, two identities. A
//! consumer chooses how to read the graph by choosing which hash to
//! compare against.
//!
//! # Linearity at the input side
//!
//! Input ports are *linear*: each may be wired at most once. Output
//! ports fan out freely. A consumer that wants strict cartesian
//! semantics inserts explicit copy nodes; one that wants strict linear
//! semantics enforces a single outgoing edge per output at its own
//! layer.

use bytes::Bytes;
use covalence_hash::{Blake3Ctx, HashCtx, O256};
use covalence_parse::leb128::{decode_u32, decode_u64, encode_u32, encode_u64};

/// Opaque type identifier. The graph only checks `==`.
#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug, Default, PartialOrd, Ord)]
pub struct TypeId(pub u64);

/// Stable, 0-based index into the node insertion order.
#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)]
pub struct NodeId(pub u32);

/// Stable, 0-based index into a node's port list.
#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)]
pub struct PortId(pub u32);

#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub enum PortKind {
    Input,
    Output,
}

impl PortKind {
    fn as_byte(self) -> u8 {
        match self {
            PortKind::Input => 0,
            PortKind::Output => 1,
        }
    }
    fn from_byte(b: u8) -> Result<Self, DecodeError> {
        match b {
            0 => Ok(PortKind::Input),
            1 => Ok(PortKind::Output),
            _ => Err(DecodeError::BadEnumTag {
                what: "port-kind",
                got: b,
            }),
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Port {
    pub name: String,
    pub type_id: TypeId,
    pub kind: PortKind,
}

/// A fixed, built-in classification of a node.
///
/// This is deliberately an enum (not a bool, not user-extensible).
/// The graph treats each variant differently — currently:
/// - [`NodeKind::Pure`] : pure / commuting; no implicit ordering.
/// - [`NodeKind::Ordered`] : effectful; consecutive ordered nodes are
///   linked by an implicit "state wire" in the string-diagram view.
///
/// More built-in kinds may be added (e.g. `BoxedBox`, `Frame`,
/// `Mark`). The canonical encoding reserves a full byte so additions
/// don't break the wire format.
#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug, Default)]
pub enum NodeKind {
    #[default]
    Pure,
    Ordered,
}

impl NodeKind {
    fn as_byte(self) -> u8 {
        match self {
            NodeKind::Pure => 0,
            NodeKind::Ordered => 1,
        }
    }
    fn from_byte(b: u8) -> Result<Self, DecodeError> {
        match b {
            0 => Ok(NodeKind::Pure),
            1 => Ok(NodeKind::Ordered),
            _ => Err(DecodeError::BadEnumTag {
                what: "node-kind",
                got: b,
            }),
        }
    }

    /// Whether this kind admits a user-visible label. Currently true
    /// for every kind, but the gate is in place so future structural
    /// kinds (e.g. a state-delimiter marker) can opt out without a
    /// data migration. Validation in [`Graph::from_parts`] and
    /// [`GraphBuilder::add_node`] rejects `(kind, Some(label))` pairs
    /// where this returns false.
    pub fn supports_label(self) -> bool {
        match self {
            NodeKind::Pure | NodeKind::Ordered => true,
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Node<P> {
    pub kind: NodeKind,
    /// Free-form human-readable label, optional. Only valid when
    /// `kind.supports_label()`. The canonical encoding stores it
    /// after the payload; the visualizer prefers it over the payload
    /// string when present.
    pub label: Option<String>,
    pub ports: Vec<Port>,
    pub payload: P,
}

#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub struct Edge {
    pub from_node: NodeId,
    pub from_port: PortId,
    pub to_node: NodeId,
    pub to_port: PortId,
}

#[derive(Debug, Clone, thiserror::Error, PartialEq, Eq)]
pub enum WireError {
    #[error("unknown node id: {0:?}")]
    UnknownNode(NodeId),
    #[error("unknown port: node {0:?} port {1:?}")]
    UnknownPort(NodeId, PortId),
    #[error("port kind mismatch: edges must go output → input")]
    KindMismatch,
    #[error("port type mismatch: from {0:?} to {1:?}")]
    TypeMismatch(TypeId, TypeId),
    #[error("input port already wired: node {0:?} port {1:?}")]
    AlreadyWired(NodeId, PortId),
}

#[derive(Debug, Clone, thiserror::Error, PartialEq, Eq)]
pub enum BuildError {
    #[error("input port not wired: node {0:?} port {1:?}")]
    UnwiredInput(NodeId, PortId),
    #[error("node {0:?} kind {1:?} does not support labels")]
    LabelNotAllowed(NodeId, NodeKind),
}

#[derive(Debug, Clone, thiserror::Error, PartialEq, Eq)]
pub enum DecodeError {
    #[error("bad magic: expected 'COVG', got {got:?}")]
    BadMagic { got: [u8; 4] },
    #[error("unsupported version: {got} (this build understands v{supported})")]
    UnsupportedVersion { got: u8, supported: u8 },
    #[error("truncated: expected {expected} bytes, only {have} available")]
    Truncated { expected: usize, have: usize },
    #[error("bad enum tag for {what}: {got}")]
    BadEnumTag { what: &'static str, got: u8 },
    #[error("invalid UTF-8 in {what}")]
    BadUtf8 { what: &'static str },
    #[error("LEB128 decode error: {0}")]
    Leb(#[from] covalence_parse::leb128::DecodeError),
    #[error("trailing bytes: {0} extra bytes after canonical encoding")]
    TrailingBytes(usize),
}

/// Canonical encoding magic. ASCII "COVG".
pub const CANONICAL_MAGIC: [u8; 4] = *b"COVG";
/// Canonical encoding version. Bump only on format break.
pub const CANONICAL_VERSION: u8 = 1;

/// BLAKE3 derivation context for the "graph as symmetric premonoidal"
/// reading. Used by [`Graph::ordered_hash`].
pub const ORDERED_HASH_CTX: &str = "cov:graph@0.1.0 ordered";
/// BLAKE3 derivation context for the "graph as symmetric monoidal"
/// reading. Used by [`Graph::unordered_hash`].
pub const UNORDERED_HASH_CTX: &str = "cov:graph@0.1.0 unordered";

/// Frozen, fully-built graph. Insertion order preserved everywhere.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Graph<P> {
    nodes: Vec<Node<P>>,
    edges: Vec<Edge>,
}

impl<P> Graph<P> {
    /// Reconstruct from raw nodes + edges (e.g. a snapshot). Validates
    /// the same invariants as `GraphBuilder::finish`.
    pub fn from_parts(nodes: Vec<Node<P>>, edges: Vec<Edge>) -> Result<Self, FromPartsError> {
        for (ni, node) in nodes.iter().enumerate() {
            if !node.kind.supports_label() && node.label.is_some() {
                return Err(FromPartsError::Build(BuildError::LabelNotAllowed(
                    NodeId(ni as u32),
                    node.kind,
                )));
            }
        }
        for (i, e) in edges.iter().enumerate() {
            let from = nodes
                .get(e.from_node.0 as usize)
                .ok_or(FromPartsError::Wire(i, WireError::UnknownNode(e.from_node)))?;
            let to = nodes
                .get(e.to_node.0 as usize)
                .ok_or(FromPartsError::Wire(i, WireError::UnknownNode(e.to_node)))?;
            let fp = from.ports.get(e.from_port.0 as usize).ok_or(
                FromPartsError::Wire(i, WireError::UnknownPort(e.from_node, e.from_port)),
            )?;
            let tp = to.ports.get(e.to_port.0 as usize).ok_or(FromPartsError::Wire(
                i,
                WireError::UnknownPort(e.to_node, e.to_port),
            ))?;
            if fp.kind != PortKind::Output || tp.kind != PortKind::Input {
                return Err(FromPartsError::Wire(i, WireError::KindMismatch));
            }
            if fp.type_id != tp.type_id {
                return Err(FromPartsError::Wire(
                    i,
                    WireError::TypeMismatch(fp.type_id, tp.type_id),
                ));
            }
        }
        let mut seen_inputs = std::collections::HashSet::new();
        for (i, e) in edges.iter().enumerate() {
            if !seen_inputs.insert((e.to_node, e.to_port)) {
                return Err(FromPartsError::Wire(
                    i,
                    WireError::AlreadyWired(e.to_node, e.to_port),
                ));
            }
        }
        for (ni, node) in nodes.iter().enumerate() {
            for (pi, port) in node.ports.iter().enumerate() {
                if port.kind == PortKind::Input {
                    let id = (NodeId(ni as u32), PortId(pi as u32));
                    if !seen_inputs.contains(&id) {
                        return Err(FromPartsError::Build(BuildError::UnwiredInput(id.0, id.1)));
                    }
                }
            }
        }
        Ok(Self { nodes, edges })
    }

    pub fn nodes(&self) -> &[Node<P>] {
        &self.nodes
    }
    pub fn edges(&self) -> &[Edge] {
        &self.edges
    }
    pub fn node_count(&self) -> u32 {
        self.nodes.len() as u32
    }
    pub fn edge_count(&self) -> u32 {
        self.edges.len() as u32
    }
    pub fn get_node(&self, id: NodeId) -> Option<&Node<P>> {
        self.nodes.get(id.0 as usize)
    }

    pub fn edges_from(
        &self,
        n: NodeId,
        port: Option<PortId>,
    ) -> impl Iterator<Item = &Edge> + '_ {
        self.edges
            .iter()
            .filter(move |e| e.from_node == n && port.map_or(true, |p| e.from_port == p))
    }

    pub fn edges_into(
        &self,
        n: NodeId,
        port: Option<PortId>,
    ) -> impl Iterator<Item = &Edge> + '_ {
        self.edges
            .iter()
            .filter(move |e| e.to_node == n && port.map_or(true, |p| e.to_port == p))
    }

    pub fn equal(&self, other: &Self) -> bool
    where
        P: PartialEq,
    {
        self == other
    }

    /// Iterator of node ids whose [`NodeKind`] is [`NodeKind::Ordered`],
    /// in insertion order. Consumers visualize the implicit "state
    /// wire" by pairing consecutive ids.
    pub fn ordered_nodes(&self) -> impl Iterator<Item = NodeId> + '_ {
        self.nodes
            .iter()
            .enumerate()
            .filter(|(_, n)| n.kind == NodeKind::Ordered)
            .map(|(i, _)| NodeId(i as u32))
    }
}

impl<P: AsRef<[u8]>> Graph<P> {
    /// Canonical byte encoding. Same content → same bytes.
    ///
    /// Format (v1):
    /// ```text
    /// "COVG"               4 bytes  magic
    /// version              1 byte   = 1
    /// node-count           LEB128
    /// for each node:
    ///   kind               1 byte   0=pure, 1=ordered, …
    ///   port-count         LEB128
    ///   for each port:
    ///     kind             1 byte   0=input, 1=output
    ///     type-id          LEB128 u64
    ///     name-len         LEB128
    ///     name             utf-8 bytes
    ///   payload-len        LEB128
    ///   payload            bytes
    ///   label-present      1 byte   0 = absent, 1 = present
    ///   if label-present:
    ///     label-len        LEB128
    ///     label            utf-8 bytes
    /// edge-count           LEB128
    /// for each edge:
    ///   from-node          LEB128 u32
    ///   from-port          LEB128 u32
    ///   to-node            LEB128 u32
    ///   to-port            LEB128 u32
    /// ```
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut buf = Vec::with_capacity(64 + self.nodes.len() * 16);
        buf.extend_from_slice(&CANONICAL_MAGIC);
        buf.push(CANONICAL_VERSION);
        encode_u32(self.nodes.len() as u32, &mut buf);
        for node in &self.nodes {
            buf.push(node.kind.as_byte());
            encode_u32(node.ports.len() as u32, &mut buf);
            for port in &node.ports {
                buf.push(port.kind.as_byte());
                encode_u64(port.type_id.0, &mut buf);
                let name = port.name.as_bytes();
                encode_u32(name.len() as u32, &mut buf);
                buf.extend_from_slice(name);
            }
            let payload = node.payload.as_ref();
            encode_u32(payload.len() as u32, &mut buf);
            buf.extend_from_slice(payload);
            match &node.label {
                None => buf.push(0),
                Some(s) => {
                    buf.push(1);
                    let bytes = s.as_bytes();
                    encode_u32(bytes.len() as u32, &mut buf);
                    buf.extend_from_slice(bytes);
                }
            }
        }
        encode_u32(self.edges.len() as u32, &mut buf);
        for e in &self.edges {
            encode_u32(e.from_node.0, &mut buf);
            encode_u32(e.from_port.0, &mut buf);
            encode_u32(e.to_node.0, &mut buf);
            encode_u32(e.to_port.0, &mut buf);
        }
        buf
    }

    /// BLAKE3 content hash under the "ordered" domain — the graph as
    /// a symmetric premonoidal entity. Use this when node insertion
    /// order is part of identity.
    pub fn ordered_hash(&self) -> O256 {
        Blake3Ctx::new(ORDERED_HASH_CTX).tag(&self.to_bytes())
    }

    /// BLAKE3 content hash under the "unordered" domain — the graph
    /// as a symmetric monoidal entity. Same canonical bytes, different
    /// derivation context. Use this when you want commuting nodes to
    /// be identified up to your own external canonicalization.
    ///
    /// Note: the bytes are still order-preserving (canonical bytes
    /// don't sort). The domain change just tags the consumer's
    /// *intent* to treat the graph as unordered. If you need an
    /// order-independent identity, normalize first, then hash.
    pub fn unordered_hash(&self) -> O256 {
        Blake3Ctx::new(UNORDERED_HASH_CTX).tag(&self.to_bytes())
    }
}

impl Graph<Bytes> {
    /// Inverse of [`Graph::to_bytes`] for the `Graph<Bytes>` (WIT)
    /// flavor. Validates both the encoding and the graph invariants.
    pub fn from_bytes(data: &[u8]) -> Result<Self, DecodeError> {
        let mut d = Cursor::new(data);
        let magic = d.take(4)?;
        let mut magic_arr = [0u8; 4];
        magic_arr.copy_from_slice(magic);
        if magic_arr != CANONICAL_MAGIC {
            return Err(DecodeError::BadMagic { got: magic_arr });
        }
        let version = d.take(1)?[0];
        if version != CANONICAL_VERSION {
            return Err(DecodeError::UnsupportedVersion {
                got: version,
                supported: CANONICAL_VERSION,
            });
        }
        let node_count = d.read_u32()?;
        let mut nodes = Vec::with_capacity(node_count as usize);
        for _ in 0..node_count {
            let kind = NodeKind::from_byte(d.take(1)?[0])?;
            let port_count = d.read_u32()?;
            let mut ports = Vec::with_capacity(port_count as usize);
            for _ in 0..port_count {
                let kind = PortKind::from_byte(d.take(1)?[0])?;
                let type_id = TypeId(d.read_u64()?);
                let name_len = d.read_u32()? as usize;
                let name_bytes = d.take(name_len)?.to_vec();
                let name = String::from_utf8(name_bytes)
                    .map_err(|_| DecodeError::BadUtf8 { what: "port name" })?;
                ports.push(Port { name, type_id, kind });
            }
            let payload_len = d.read_u32()? as usize;
            let payload = Bytes::copy_from_slice(d.take(payload_len)?);
            // Label: 1 byte presence flag, then LEB128-len-prefixed UTF-8 if present.
            let label_present = d.take(1)?[0];
            let label = match label_present {
                0 => None,
                1 => {
                    let len = d.read_u32()? as usize;
                    let bytes = d.take(len)?.to_vec();
                    Some(
                        String::from_utf8(bytes)
                            .map_err(|_| DecodeError::BadUtf8 { what: "node label" })?,
                    )
                }
                got => {
                    return Err(DecodeError::BadEnumTag {
                        what: "label-present",
                        got,
                    });
                }
            };
            nodes.push(Node {
                kind,
                label,
                ports,
                payload,
            });
        }
        let edge_count = d.read_u32()?;
        let mut edges = Vec::with_capacity(edge_count as usize);
        for _ in 0..edge_count {
            let from_node = NodeId(d.read_u32()?);
            let from_port = PortId(d.read_u32()?);
            let to_node = NodeId(d.read_u32()?);
            let to_port = PortId(d.read_u32()?);
            edges.push(Edge {
                from_node,
                from_port,
                to_node,
                to_port,
            });
        }
        if d.remaining() > 0 {
            return Err(DecodeError::TrailingBytes(d.remaining()));
        }
        Self::from_parts(nodes, edges).map_err(|e| match e {
            FromPartsError::Wire(i, w) => DecodeError::BadEnumTag {
                what: "wire validation",
                got: i as u8,
            }
            .or_actual(w),
            FromPartsError::Build(b) => DecodeError::BadEnumTag {
                what: "build validation",
                got: 0,
            }
            .or_actual(b),
        })
    }
}

impl DecodeError {
    fn or_actual<E: std::fmt::Display>(self, actual: E) -> Self {
        // The validation paths in from_parts produce richer errors
        // than DecodeError; we squash to a generic BadEnumTag with
        // the message in trailing-bytes shape. Future: add a dedicated
        // variant. For MVP: don't lose the message.
        Self::BadUtf8 {
            what: Box::leak(format!("graph validation: {actual}").into_boxed_str()),
        }
    }
}

#[derive(Debug, Clone, thiserror::Error, PartialEq, Eq)]
pub enum FromPartsError {
    #[error("edge {0}: {1}")]
    Wire(usize, #[source] WireError),
    #[error(transparent)]
    Build(#[from] BuildError),
}

/// Mutable graph under construction.
#[derive(Clone, Debug, Default)]
pub struct GraphBuilder<P> {
    nodes: Vec<Node<P>>,
    edges: Vec<Edge>,
    wired_inputs: std::collections::HashMap<(NodeId, PortId), usize>,
}

impl<P> GraphBuilder<P> {
    pub fn new() -> Self {
        Self {
            nodes: Vec::new(),
            edges: Vec::new(),
            wired_inputs: std::collections::HashMap::new(),
        }
    }

    /// Append a node. Its `NodeId` equals the current node count, so
    /// insertion order = id order.
    ///
    /// `label` is optional and only valid when `kind.supports_label()`
    /// — pass `None` if you don't want one, or for kinds that don't
    /// admit labels. Mismatch is checked at [`Self::finish`] /
    /// [`Graph::from_parts`].
    pub fn add_node(
        &mut self,
        kind: NodeKind,
        label: Option<String>,
        ports: Vec<Port>,
        payload: P,
    ) -> NodeId {
        let id = NodeId(self.nodes.len() as u32);
        self.nodes.push(Node {
            kind,
            label,
            ports,
            payload,
        });
        id
    }

    pub fn wire(&mut self, edge: Edge) -> Result<(), WireError> {
        let from = self
            .nodes
            .get(edge.from_node.0 as usize)
            .ok_or(WireError::UnknownNode(edge.from_node))?;
        let to = self
            .nodes
            .get(edge.to_node.0 as usize)
            .ok_or(WireError::UnknownNode(edge.to_node))?;
        let fp = from
            .ports
            .get(edge.from_port.0 as usize)
            .ok_or(WireError::UnknownPort(edge.from_node, edge.from_port))?;
        let tp = to
            .ports
            .get(edge.to_port.0 as usize)
            .ok_or(WireError::UnknownPort(edge.to_node, edge.to_port))?;
        if fp.kind != PortKind::Output || tp.kind != PortKind::Input {
            return Err(WireError::KindMismatch);
        }
        if fp.type_id != tp.type_id {
            return Err(WireError::TypeMismatch(fp.type_id, tp.type_id));
        }
        let input_key = (edge.to_node, edge.to_port);
        if self.wired_inputs.contains_key(&input_key) {
            return Err(WireError::AlreadyWired(edge.to_node, edge.to_port));
        }
        let idx = self.edges.len();
        self.edges.push(edge);
        self.wired_inputs.insert(input_key, idx);
        Ok(())
    }

    pub fn peek_nodes(&self) -> &[Node<P>] {
        &self.nodes
    }
    pub fn peek_edges(&self) -> &[Edge] {
        &self.edges
    }

    pub fn finish(self) -> Result<Graph<P>, BuildError> {
        for (ni, node) in self.nodes.iter().enumerate() {
            if !node.kind.supports_label() && node.label.is_some() {
                return Err(BuildError::LabelNotAllowed(NodeId(ni as u32), node.kind));
            }
            for (pi, port) in node.ports.iter().enumerate() {
                if port.kind == PortKind::Input {
                    let id = (NodeId(ni as u32), PortId(pi as u32));
                    if !self.wired_inputs.contains_key(&id) {
                        return Err(BuildError::UnwiredInput(id.0, id.1));
                    }
                }
            }
        }
        Ok(Graph {
            nodes: self.nodes,
            edges: self.edges,
        })
    }
}

/// Alias for the WIT-bridged form. `payload = list<u8>` over the wire.
pub type BytesGraph = Graph<Bytes>;
pub type BytesGraphBuilder = GraphBuilder<Bytes>;

// ----------------------------------------------------------------------
// Helpers
// ----------------------------------------------------------------------

struct Cursor<'a> {
    data: &'a [u8],
    pos: usize,
}

impl<'a> Cursor<'a> {
    fn new(data: &'a [u8]) -> Self {
        Self { data, pos: 0 }
    }
    fn remaining(&self) -> usize {
        self.data.len() - self.pos
    }
    fn take(&mut self, n: usize) -> Result<&'a [u8], DecodeError> {
        if self.remaining() < n {
            return Err(DecodeError::Truncated {
                expected: n,
                have: self.remaining(),
            });
        }
        let out = &self.data[self.pos..self.pos + n];
        self.pos += n;
        Ok(out)
    }
    fn read_u32(&mut self) -> Result<u32, DecodeError> {
        let (v, n) = decode_u32(&self.data[self.pos..])?;
        self.pos += n;
        Ok(v)
    }
    fn read_u64(&mut self) -> Result<u64, DecodeError> {
        let (v, n) = decode_u64(&self.data[self.pos..])?;
        self.pos += n;
        Ok(v)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn out(name: &str, ty: u64) -> Port {
        Port {
            name: name.into(),
            type_id: TypeId(ty),
            kind: PortKind::Output,
        }
    }
    fn inp(name: &str, ty: u64) -> Port {
        Port {
            name: name.into(),
            type_id: TypeId(ty),
            kind: PortKind::Input,
        }
    }

    fn simple_pair() -> Graph<&'static str> {
        let mut b = GraphBuilder::new();
        let src = b.add_node(NodeKind::Pure, None, vec![out("o", 1)], "src");
        let snk = b.add_node(NodeKind::Pure, None, vec![inp("i", 1)], "snk");
        b.wire(Edge {
            from_node: src,
            from_port: PortId(0),
            to_node: snk,
            to_port: PortId(0),
        })
        .unwrap();
        b.finish().unwrap()
    }

    #[test]
    fn build_and_inspect() {
        let g = simple_pair();
        assert_eq!(g.node_count(), 2);
        assert_eq!(g.edge_count(), 1);
        assert_eq!(g.get_node(NodeId(0)).unwrap().payload, "src");
        assert_eq!(g.get_node(NodeId(1)).unwrap().payload, "snk");
        assert_eq!(g.edges_from(NodeId(0), None).count(), 1);
        assert_eq!(g.edges_into(NodeId(1), None).count(), 1);
        assert_eq!(g.edges_from(NodeId(1), None).count(), 0);
    }

    #[test]
    fn insertion_order_matters() {
        let g1 = simple_pair();
        let g2 = {
            let mut b = GraphBuilder::new();
            let snk = b.add_node(NodeKind::Pure, None, vec![inp("i", 1)], "snk");
            let src = b.add_node(NodeKind::Pure, None, vec![out("o", 1)], "src");
            b.wire(Edge {
                from_node: src,
                from_port: PortId(0),
                to_node: snk,
                to_port: PortId(0),
            })
            .unwrap();
            b.finish().unwrap()
        };
        assert!(!g1.equal(&g2));
    }

    #[test]
    fn type_mismatch_rejected() {
        let mut b = GraphBuilder::<()>::new();
        let src = b.add_node(NodeKind::Pure, None, vec![out("o", 1)], ());
        let snk = b.add_node(NodeKind::Pure, None, vec![inp("i", 2)], ());
        let err = b
            .wire(Edge {
                from_node: src,
                from_port: PortId(0),
                to_node: snk,
                to_port: PortId(0),
            })
            .unwrap_err();
        assert_eq!(err, WireError::TypeMismatch(TypeId(1), TypeId(2)));
    }

    #[test]
    fn kind_mismatch_rejected() {
        let mut b = GraphBuilder::<()>::new();
        let a = b.add_node(NodeKind::Pure, None, vec![inp("i", 1)], ());
        let c = b.add_node(NodeKind::Pure, None, vec![out("o", 1)], ());
        let err = b
            .wire(Edge {
                from_node: a,
                from_port: PortId(0),
                to_node: c,
                to_port: PortId(0),
            })
            .unwrap_err();
        assert_eq!(err, WireError::KindMismatch);
    }

    #[test]
    fn input_linearity() {
        let mut b = GraphBuilder::<()>::new();
        let s1 = b.add_node(NodeKind::Pure, None, vec![out("o", 1)], ());
        let s2 = b.add_node(NodeKind::Pure, None, vec![out("o", 1)], ());
        let k = b.add_node(NodeKind::Pure, None, vec![inp("i", 1)], ());
        b.wire(Edge {
            from_node: s1,
            from_port: PortId(0),
            to_node: k,
            to_port: PortId(0),
        })
        .unwrap();
        let err = b
            .wire(Edge {
                from_node: s2,
                from_port: PortId(0),
                to_node: k,
                to_port: PortId(0),
            })
            .unwrap_err();
        assert_eq!(err, WireError::AlreadyWired(k, PortId(0)));
    }

    #[test]
    fn output_fans_out() {
        let mut b = GraphBuilder::<()>::new();
        let src = b.add_node(NodeKind::Pure, None, vec![out("o", 1)], ());
        let k1 = b.add_node(NodeKind::Pure, None, vec![inp("i", 1)], ());
        let k2 = b.add_node(NodeKind::Pure, None, vec![inp("i", 1)], ());
        b.wire(Edge {
            from_node: src,
            from_port: PortId(0),
            to_node: k1,
            to_port: PortId(0),
        })
        .unwrap();
        b.wire(Edge {
            from_node: src,
            from_port: PortId(0),
            to_node: k2,
            to_port: PortId(0),
        })
        .unwrap();
        let g = b.finish().unwrap();
        assert_eq!(g.edges_from(src, None).count(), 2);
    }

    #[test]
    fn finish_rejects_unwired_inputs() {
        let mut b = GraphBuilder::<()>::new();
        b.add_node(NodeKind::Pure, None, vec![inp("i", 1)], ());
        let err = b.finish().unwrap_err();
        assert_eq!(err, BuildError::UnwiredInput(NodeId(0), PortId(0)));
    }

    fn kind(o: bool) -> NodeKind {
        if o { NodeKind::Ordered } else { NodeKind::Pure }
    }

    fn bytes_pair(o1: bool, o2: bool) -> BytesGraph {
        let mut b = BytesGraphBuilder::new();
        let src = b.add_node(kind(o1), None, vec![out("o", 1)], Bytes::from_static(b"src"));
        let snk = b.add_node(kind(o2), None, vec![inp("i", 1)], Bytes::from_static(b"snk"));
        b.wire(Edge {
            from_node: src,
            from_port: PortId(0),
            to_node: snk,
            to_port: PortId(0),
        })
        .unwrap();
        b.finish().unwrap()
    }

    #[test]
    fn canonical_roundtrip() {
        let g = bytes_pair(true, false);
        let bytes = g.to_bytes();
        let g2 = BytesGraph::from_bytes(&bytes).unwrap();
        assert!(g.equal(&g2));
        // First node is Ordered, second is Pure — both round-trip.
        assert_eq!(g2.get_node(NodeId(0)).unwrap().kind, NodeKind::Ordered);
        assert_eq!(g2.get_node(NodeId(1)).unwrap().kind, NodeKind::Pure);
    }

    #[test]
    fn canonical_starts_with_magic() {
        let bytes = bytes_pair(false, false).to_bytes();
        assert_eq!(&bytes[..4], &CANONICAL_MAGIC);
        assert_eq!(bytes[4], CANONICAL_VERSION);
    }

    #[test]
    fn ordered_and_unordered_hashes_differ() {
        let g = bytes_pair(true, true);
        let a = g.ordered_hash();
        let b = g.unordered_hash();
        assert_ne!(a, b, "domain-keyed hashes must differ");
    }

    #[test]
    fn hash_changes_with_node_kind() {
        let g1 = bytes_pair(true, false);
        let g2 = bytes_pair(false, false);
        assert_ne!(g1.ordered_hash(), g2.ordered_hash());
        assert_ne!(g1.unordered_hash(), g2.unordered_hash());
    }

    #[test]
    fn ordered_nodes_iter() {
        let g = bytes_pair(true, false);
        let ids: Vec<_> = g.ordered_nodes().collect();
        assert_eq!(ids, vec![NodeId(0)]);
    }

    #[test]
    fn bad_magic_rejected() {
        let err = BytesGraph::from_bytes(b"NOPE\x01\x00").unwrap_err();
        assert!(matches!(err, DecodeError::BadMagic { .. }));
    }

    #[test]
    fn label_roundtrips() {
        let mut b = BytesGraphBuilder::new();
        let src = b.add_node(
            NodeKind::Pure,
            Some("source".to_string()),
            vec![out("o", 1)],
            Bytes::from_static(b""),
        );
        let snk = b.add_node(
            NodeKind::Ordered,
            None,
            vec![inp("i", 1)],
            Bytes::from_static(b""),
        );
        b.wire(Edge {
            from_node: src,
            from_port: PortId(0),
            to_node: snk,
            to_port: PortId(0),
        })
        .unwrap();
        let g = b.finish().unwrap();
        let g2 = BytesGraph::from_bytes(&g.to_bytes()).unwrap();
        assert_eq!(
            g2.get_node(NodeId(0)).unwrap().label.as_deref(),
            Some("source")
        );
        assert!(g2.get_node(NodeId(1)).unwrap().label.is_none());
    }

    #[test]
    fn truncated_rejected() {
        let err = BytesGraph::from_bytes(b"COV").unwrap_err();
        assert!(matches!(err, DecodeError::Truncated { .. }));
    }
}
