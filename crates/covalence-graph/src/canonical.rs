//! Canonical byte encoding for [`Graph`] (`GRAPH_DATA`).
//!
//! Pure topology — no labels, no per-node "ordered/pure" classification.
//! Those live in overlay blobs (see [`crate::overlay`] and
//! [`crate::string_diagram::StringDiagram`]) so the same topology can be
//! tagged with different labels / classifications by different consumers.
//!
//! All multi-byte integers use unsigned LEB128.

use bytes::Bytes;
use covalence_hash::O256;
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

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Node<P> {
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
    #[error("validation: {0}")]
    Validation(String),
}

#[derive(Debug, Clone, thiserror::Error, PartialEq, Eq)]
pub enum FromPartsError {
    #[error("edge {0}: {1}")]
    Wire(usize, #[source] WireError),
    #[error(transparent)]
    Build(#[from] BuildError),
}

/// Canonical encoding magic. ASCII "COVG".
pub const CANONICAL_MAGIC: [u8; 4] = *b"COVG";
/// Canonical encoding version. Bumped only on format break.
pub const CANONICAL_VERSION: u8 = 1;

/// BLAKE3 derivation context for the "graph as ordered DAG" reading.
/// Also used as the *tag* for cov:graph topology objects in a tagged
/// content store: `keyed_identity = O256::context(ORDERED_HASH_CTX, content_hash)`,
/// i.e. `BLAKE3-keyed(derive_key(TAG), BLAKE3(graph_bytes))`.
pub const ORDERED_HASH_CTX: &str = "cov:graph@0.1.0 ordered";
/// BLAKE3 derivation context for the "graph as set-of-nodes-and-edges" reading.
pub const UNORDERED_HASH_CTX: &str = "cov:graph@0.1.0 unordered";

/// Frozen, fully-built graph. Insertion order preserved everywhere.
///
/// `Graph` is pure topology + ports + payloads. Labels and per-node
/// "ordered/pure" classification live in overlay blobs — see
/// [`crate::string_diagram::StringDiagram`].
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Graph<P> {
    nodes: Vec<Node<P>>,
    edges: Vec<Edge>,
}

impl<P> Graph<P> {
    pub fn from_parts(nodes: Vec<Node<P>>, edges: Vec<Edge>) -> Result<Self, FromPartsError> {
        for (i, e) in edges.iter().enumerate() {
            let from = nodes
                .get(e.from_node.0 as usize)
                .ok_or(FromPartsError::Wire(i, WireError::UnknownNode(e.from_node)))?;
            let to = nodes
                .get(e.to_node.0 as usize)
                .ok_or(FromPartsError::Wire(i, WireError::UnknownNode(e.to_node)))?;
            let fp = from.ports.get(e.from_port.0 as usize).ok_or_else(|| {
                FromPartsError::Wire(i, WireError::UnknownPort(e.from_node, e.from_port))
            })?;
            let tp = to.ports.get(e.to_port.0 as usize).ok_or_else(|| {
                FromPartsError::Wire(i, WireError::UnknownPort(e.to_node, e.to_port))
            })?;
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

    pub fn edges_from(&self, n: NodeId, port: Option<PortId>) -> impl Iterator<Item = &Edge> + '_ {
        self.edges
            .iter()
            .filter(move |e| e.from_node == n && port.is_none_or(|p| e.from_port == p))
    }

    pub fn edges_into(&self, n: NodeId, port: Option<PortId>) -> impl Iterator<Item = &Edge> + '_ {
        self.edges
            .iter()
            .filter(move |e| e.to_node == n && port.is_none_or(|p| e.to_port == p))
    }

    pub fn equal(&self, other: &Self) -> bool
    where
        P: PartialEq,
    {
        self == other
    }
}

impl<P: AsRef<[u8]>> Graph<P> {
    /// Canonical byte encoding.
    ///
    /// ```text
    /// "COVG"               4 bytes  magic
    /// version              1 byte
    /// node-count           LEB128
    /// for each node:
    ///   port-count         LEB128
    ///   for each port:
    ///     kind             1 byte   0=input, 1=output
    ///     type-id          LEB128 u64
    ///     name-len         LEB128
    ///     name             utf-8 bytes
    ///   payload-len        LEB128
    ///   payload            bytes
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

    /// Unkeyed BLAKE3 hash of the canonical bytes. This is the
    /// content-addressed identity of the topology blob in a plain blob
    /// store. Use [`Self::ordered_hash`] / [`Self::unordered_hash`] for
    /// the *typed* identity used by a tagged store.
    pub fn content_hash(&self) -> O256 {
        O256::blob(self.to_bytes())
    }

    /// Tagged identity under the "ordered" domain — the keyed hash
    /// `BLAKE3-keyed(derive_key(ORDERED_HASH_CTX), content_hash)`.
    /// Stable across alternative serialisations of equal-content
    /// graphs, and recoverable from the content hash alone without
    /// needing the raw bytes.
    pub fn ordered_hash(&self) -> O256 {
        O256::context(ORDERED_HASH_CTX, self.content_hash().as_bytes())
    }

    /// Tagged identity under the "unordered" domain. Same content
    /// hash, different tag.
    pub fn unordered_hash(&self) -> O256 {
        O256::context(UNORDERED_HASH_CTX, self.content_hash().as_bytes())
    }
}

impl Graph<Bytes> {
    /// Decode the canonical bytes.
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
            let ports = decode_ports(&mut d)?;
            let payload_len = d.read_u32()? as usize;
            let payload = Bytes::copy_from_slice(d.take(payload_len)?);
            nodes.push(Node { ports, payload });
        }
        let edges = decode_edges(&mut d)?;
        if d.remaining() > 0 {
            return Err(DecodeError::TrailingBytes(d.remaining()));
        }
        Graph::from_parts(nodes, edges).map_err(|e| DecodeError::Validation(e.to_string()))
    }
}

fn decode_ports(d: &mut Cursor<'_>) -> Result<Vec<Port>, DecodeError> {
    let port_count = d.read_u32()?;
    let mut ports = Vec::with_capacity(port_count as usize);
    for _ in 0..port_count {
        let kind = PortKind::from_byte(d.take(1)?[0])?;
        let type_id = TypeId(d.read_u64()?);
        let name_len = d.read_u32()? as usize;
        let name_bytes = d.take(name_len)?.to_vec();
        let name =
            String::from_utf8(name_bytes).map_err(|_| DecodeError::BadUtf8 { what: "port name" })?;
        ports.push(Port {
            name,
            type_id,
            kind,
        });
    }
    Ok(ports)
}

fn decode_edges(d: &mut Cursor<'_>) -> Result<Vec<Edge>, DecodeError> {
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
    Ok(edges)
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

    /// Append a node. Its `NodeId` equals the current node count.
    pub fn add_node(&mut self, ports: Vec<Port>, payload: P) -> NodeId {
        let id = NodeId(self.nodes.len() as u32);
        self.nodes.push(Node { ports, payload });
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
    pub fn node_count(&self) -> u32 {
        self.nodes.len() as u32
    }

    pub fn finish(self) -> Result<Graph<P>, BuildError> {
        for (ni, node) in self.nodes.iter().enumerate() {
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
// Internal cursor (also used by overlay decoders)
// ----------------------------------------------------------------------

pub(crate) struct Cursor<'a> {
    data: &'a [u8],
    pos: usize,
}

impl<'a> Cursor<'a> {
    pub(crate) fn new(data: &'a [u8]) -> Self {
        Self { data, pos: 0 }
    }
    pub(crate) fn remaining(&self) -> usize {
        self.data.len() - self.pos
    }
    pub(crate) fn take(&mut self, n: usize) -> Result<&'a [u8], DecodeError> {
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
    pub(crate) fn read_u32(&mut self) -> Result<u32, DecodeError> {
        let (v, n) = decode_u32(&self.data[self.pos..])?;
        self.pos += n;
        Ok(v)
    }
    pub(crate) fn read_u64(&mut self) -> Result<u64, DecodeError> {
        let (v, n) = decode_u64(&self.data[self.pos..])?;
        self.pos += n;
        Ok(v)
    }
}
