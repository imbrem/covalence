//! String diagram: a [`Graph`](crate::Graph) plus optional overlays
//! ([`LabelList`], [`KindFlags`]).
//!
//! Three slots, each holding a reference to an overlay blob. Slots
//! reserve sentinel values for compact "uniform" cases so that diagrams
//! with no labels (or all-pure / all-ordered kinds) don't have to
//! materialise an overlay blob.
//!
//! Two views on the same composite:
//!
//! - [`StringDiagram`] : **canonical references only** — three
//!   [`SlotRef`]s plus the underlying [`Graph`] hash. This is what
//!   gets hashed and stored; this is the stable surface.
//! - [`ResolvedDiagram`] : the three overlays inlined alongside the
//!   topology. This is what renderers consume.
//!
//! Going from references to a resolved diagram requires looking up
//! blobs in some store; the [`Resolver`] trait abstracts over that so
//! the same string-diagram can be resolved against any backend.

use covalence_hash::O256;
use covalence_parse::leb128::encode_u32;

use crate::canonical::{Cursor, DecodeError, Graph};
use crate::overlay::{KindFlags, LabelList, NodeKind};

// ----------------------------------------------------------------------
// SlotRef + sentinels
// ----------------------------------------------------------------------

/// What sits in one slot of a [`StringDiagram`]: either an overlay
/// hash, the absent sentinel, or a "uniform" sentinel.
#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub enum SlotRef {
    /// No overlay. Renderers fall back to defaults
    /// (`None` label per node; all-pure kind).
    Absent,
    /// One of the reserved "all the same value" sentinels.
    Uniform(UniformTag),
    /// A real overlay blob, addressed by content hash.
    Hash(O256),
}

/// Reserved sentinel values used inside a [`SlotRef::Uniform`].
#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub enum UniformTag {
    AllPure = 1,
    AllOrdered = 2,
}

impl UniformTag {
    fn as_byte(self) -> u8 {
        self as u8
    }
    fn from_byte(b: u8) -> Option<Self> {
        match b {
            1 => Some(UniformTag::AllPure),
            2 => Some(UniformTag::AllOrdered),
            _ => None,
        }
    }
}

const SENTINEL_TAG_PREFIX: u8 = 0xFF;

impl SlotRef {
    /// Encode a slot into a fixed 32-byte field for inclusion in the
    /// canonical bytes. Sentinels use a high-entropy `0xFF` prefix that
    /// real BLAKE3 outputs effectively never produce, plus the absent
    /// case is the all-zero hash. This keeps slot decoding constant-time.
    pub fn to_o256_bytes(self) -> [u8; 32] {
        match self {
            SlotRef::Absent => [0u8; 32],
            SlotRef::Uniform(t) => {
                let mut buf = [0u8; 32];
                buf[0] = SENTINEL_TAG_PREFIX;
                buf[1] = t.as_byte();
                buf
            }
            SlotRef::Hash(h) => *h.as_bytes(),
        }
    }

    /// Decode a 32-byte slot field back into the typed `SlotRef`.
    /// Inverse of [`Self::to_o256_bytes`]. Used both by the
    /// [`StringDiagram`] decoder and by REPL code that wants to take a
    /// raw `O256` off the stack and recover its sentinel meaning.
    pub fn from_o256_bytes(buf: [u8; 32]) -> Result<Self, DecodeError> {
        if buf == [0u8; 32] {
            return Ok(SlotRef::Absent);
        }
        if buf[0] == SENTINEL_TAG_PREFIX {
            let tag = UniformTag::from_byte(buf[1]).ok_or(DecodeError::BadEnumTag {
                what: "slot-uniform-tag",
                got: buf[1],
            })?;
            // Bytes 2.. must be zero so different sentinels never alias.
            if buf[2..].iter().any(|&b| b != 0) {
                return Err(DecodeError::Validation(
                    "uniform-sentinel slot has non-zero trailing bytes".into(),
                ));
            }
            return Ok(SlotRef::Uniform(tag));
        }
        Ok(SlotRef::Hash(O256::from_bytes(buf)))
    }
}

// ----------------------------------------------------------------------
// StringDiagram (canonical refs)
// ----------------------------------------------------------------------

const STRING_DIAGRAM_MAGIC: [u8; 4] = *b"SDGM";
const STRING_DIAGRAM_VERSION: u8 = 1;
/// BLAKE3 derivation context — also the tag for string-diagram
/// composites in a tagged store.
pub const STRING_DIAGRAM_HASH_CTX: &str = "cov:graph@0.1.0 string-diagram";

/// Canonical, by-reference form of a string diagram. Just enough to
/// compute a content hash and look up the pieces.
///
/// Format: `"SDGM" + version + ordered_graph_hash(32) + LEB(slots) + slot(32)*`.
/// `slots` is always 2 for v1 (labels, kinds) and is encoded for
/// forward compatibility — additional slots (e.g. edge-data) just
/// extend the list.
#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub struct StringDiagram {
    /// Tagged identity of the underlying [`Graph`] under the
    /// `ORDERED_HASH_CTX` domain (see [`Graph::ordered_hash`]).
    /// Committing to this hash commits to the premonoidal reading.
    pub graph: O256,
    pub labels: SlotRef,
    pub kinds: SlotRef,
}

impl StringDiagram {
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut buf = Vec::with_capacity(5 + 32 + 1 + 32 * 2);
        buf.extend_from_slice(&STRING_DIAGRAM_MAGIC);
        buf.push(STRING_DIAGRAM_VERSION);
        buf.extend_from_slice(self.graph.as_bytes());
        encode_u32(2, &mut buf);
        buf.extend_from_slice(&self.labels.to_o256_bytes());
        buf.extend_from_slice(&self.kinds.to_o256_bytes());
        buf
    }

    pub fn from_bytes(data: &[u8]) -> Result<Self, DecodeError> {
        let mut d = Cursor::new(data);
        let magic = d.take(4)?;
        if magic != STRING_DIAGRAM_MAGIC {
            let mut got = [0u8; 4];
            got.copy_from_slice(magic);
            return Err(DecodeError::BadMagic { got });
        }
        let version = d.take(1)?[0];
        if version != STRING_DIAGRAM_VERSION {
            return Err(DecodeError::UnsupportedVersion {
                got: version,
                supported: STRING_DIAGRAM_VERSION,
            });
        }
        let mut graph_buf = [0u8; 32];
        graph_buf.copy_from_slice(d.take(32)?);
        let graph = O256::from_bytes(graph_buf);
        let slot_count = d.read_u32()?;
        if slot_count < 2 {
            return Err(DecodeError::Validation(format!(
                "string-diagram needs at least 2 slots (labels, kinds), got {slot_count}"
            )));
        }
        let mut labels_buf = [0u8; 32];
        labels_buf.copy_from_slice(d.take(32)?);
        let labels = SlotRef::from_o256_bytes(labels_buf)?;
        let mut kinds_buf = [0u8; 32];
        kinds_buf.copy_from_slice(d.take(32)?);
        let kinds = SlotRef::from_o256_bytes(kinds_buf)?;
        // Skip any extra forward-compat slots silently.
        for _ in 2..slot_count {
            let _ = d.take(32)?;
        }
        if d.remaining() > 0 {
            return Err(DecodeError::TrailingBytes(d.remaining()));
        }
        Ok(StringDiagram {
            graph,
            labels,
            kinds,
        })
    }

    /// Unkeyed BLAKE3 hash of the canonical bytes.
    pub fn content_hash(&self) -> O256 {
        O256::blob(self.to_bytes())
    }

    /// Tagged identity under the `STRING_DIAGRAM_HASH_CTX` domain:
    /// `O256::context(tag, BLAKE3(bytes))`.
    pub fn hash(&self) -> O256 {
        O256::context(STRING_DIAGRAM_HASH_CTX, self.content_hash().as_bytes())
    }
}

// ----------------------------------------------------------------------
// Builder
// ----------------------------------------------------------------------

/// Build a [`StringDiagram`] from a graph plus optional overlay data.
///
/// The builder accepts inline overlays (`LabelList`, `KindFlags`) and
/// hashes them lazily; if a [`Resolver`] is also handed in, the
/// builder stores them at finalisation. Otherwise it just records the
/// hash and assumes the caller stores them separately.
pub struct StringDiagramBuilder<'a, P> {
    graph: &'a Graph<P>,
    labels: Option<LabelList>,
    kinds: Option<KindFlags>,
    uniform_kind: Option<NodeKind>,
}

impl<'a, P: AsRef<[u8]>> StringDiagramBuilder<'a, P> {
    pub fn new(graph: &'a Graph<P>) -> Self {
        Self {
            graph,
            labels: None,
            kinds: None,
            uniform_kind: None,
        }
    }

    pub fn with_labels(mut self, labels: LabelList) -> Self {
        assert_eq!(
            labels.len() as u32,
            self.graph.node_count(),
            "label-list length ({}) must match graph node count ({})",
            labels.len(),
            self.graph.node_count()
        );
        self.labels = Some(labels);
        self
    }

    pub fn with_kinds(mut self, kinds: KindFlags) -> Self {
        assert_eq!(
            kinds.len() as u32,
            self.graph.node_count(),
            "kind-flags length ({}) must match graph node count ({})",
            kinds.len(),
            self.graph.node_count()
        );
        self.kinds = Some(kinds);
        self.uniform_kind = None;
        self
    }

    /// Shorthand for "every node is the same kind". Compiles to a
    /// `SlotRef::Uniform` sentinel — no overlay blob is materialised.
    pub fn with_uniform_kind(mut self, kind: NodeKind) -> Self {
        self.uniform_kind = Some(kind);
        self.kinds = None;
        self
    }

    /// Materialise the canonical [`StringDiagram`] without storing the
    /// overlay blobs anywhere. Use [`Self::build_with`] to also persist
    /// them through an [`OverlayStorage`].
    pub fn build(self) -> StringDiagram {
        self.build_into(&mut NoStorage)
    }

    /// Materialise the canonical [`StringDiagram`] and persist any
    /// inline overlay blobs through `storage`.
    pub fn build_with(self, storage: &mut dyn OverlayStorage) -> StringDiagram {
        self.build_into(storage)
    }

    fn build_into(self, storage: &mut dyn OverlayStorage) -> StringDiagram {
        let labels = match self.labels {
            None => SlotRef::Absent,
            Some(ll) => {
                let h = ll.hash();
                storage.store(&ll.to_bytes(), h);
                SlotRef::Hash(h)
            }
        };
        let kinds = match (self.kinds, self.uniform_kind) {
            (Some(kf), _) => match kf.is_uniform_as() {
                Some(NodeKind::Pure) => SlotRef::Uniform(UniformTag::AllPure),
                Some(NodeKind::Ordered) => SlotRef::Uniform(UniformTag::AllOrdered),
                None => {
                    let h = kf.hash();
                    storage.store(&kf.to_bytes(), h);
                    SlotRef::Hash(h)
                }
            },
            (None, Some(NodeKind::Pure)) => SlotRef::Uniform(UniformTag::AllPure),
            (None, Some(NodeKind::Ordered)) => SlotRef::Uniform(UniformTag::AllOrdered),
            (None, None) => SlotRef::Absent,
        };
        StringDiagram {
            graph: self.graph.ordered_hash(),
            labels,
            kinds,
        }
    }
}

/// `OverlayStorage` that drops every blob — used by
/// [`StringDiagramBuilder::build`] when the caller doesn't want a
/// concrete sink. The hash is still computed (and embedded in the
/// resulting [`StringDiagram`]); the bytes are simply not retained.
struct NoStorage;

impl OverlayStorage for NoStorage {
    fn store(&mut self, _bytes: &[u8], hash: O256) -> O256 {
        hash
    }
}

/// Sink for overlay blobs. Implementations are free to deduplicate or
/// ignore — the contract is just "given these bytes, produce the hash
/// at which they live". Implementations should verify that the
/// computed hash matches `expected_hash` if they hash themselves; the
/// builder always passes `expected_hash`.
pub trait OverlayStorage {
    fn store(&mut self, bytes: &[u8], expected_hash: O256) -> O256;
}

/// Convenience: an in-memory map for tests and the REPL.
#[derive(Default)]
pub struct OverlayMap {
    pub blobs: std::collections::HashMap<O256, Vec<u8>>,
}

impl OverlayStorage for OverlayMap {
    fn store(&mut self, bytes: &[u8], expected_hash: O256) -> O256 {
        self.blobs.insert(expected_hash, bytes.to_vec());
        expected_hash
    }
}

// ----------------------------------------------------------------------
// Resolver + ResolvedDiagram
// ----------------------------------------------------------------------

/// Look up overlay blobs by hash. The same store that has the
/// graph bytes typically also has the labels and kinds blobs.
pub trait Resolver {
    fn get(&self, hash: &O256) -> Option<Vec<u8>>;
}

impl Resolver for OverlayMap {
    fn get(&self, hash: &O256) -> Option<Vec<u8>> {
        self.blobs.get(hash).cloned()
    }
}

#[derive(Debug, thiserror::Error)]
pub enum ResolveError {
    #[error("overlay blob {0} not found")]
    Missing(O256),
    #[error(transparent)]
    Decode(#[from] DecodeError),
    #[error("{what} length {got} does not match graph node count {expected}")]
    LengthMismatch {
        what: &'static str,
        expected: u32,
        got: u32,
    },
}

/// A string diagram with all overlay slots resolved. Renderers consume
/// this — they never have to think about hashes or sentinels.
pub struct ResolvedDiagram<'a, P> {
    pub graph: &'a Graph<P>,
    pub labels: Option<LabelList>,
    pub kinds: KindFlags,
}

impl<P> ResolvedDiagram<'_, P> {
    /// Per-node label fallback chain: explicit label → `#i`.
    pub fn label_for(&self, i: u32) -> String {
        if let Some(ll) = &self.labels
            && let Some(s) = ll.get(i as usize)
        {
            return s.to_string();
        }
        format!("#{i}")
    }

    pub fn kind_of(&self, i: u32) -> NodeKind {
        self.kinds.get(i as usize).unwrap_or_default()
    }
}

impl StringDiagram {
    /// Resolve overlay slots against `resolver` and return a diagram
    /// suitable for rendering. `graph` must hash to `self.graph` —
    /// callers are responsible for fetching the right topology.
    pub fn resolve<'a, P: AsRef<[u8]>, R: Resolver + ?Sized>(
        &self,
        graph: &'a Graph<P>,
        resolver: &R,
    ) -> Result<ResolvedDiagram<'a, P>, ResolveError> {
        let n = graph.node_count();
        let labels = match self.labels {
            SlotRef::Absent | SlotRef::Uniform(_) => None,
            SlotRef::Hash(h) => {
                let bytes = resolver.get(&h).ok_or(ResolveError::Missing(h))?;
                let ll = LabelList::from_bytes(&bytes)?;
                if ll.len() as u32 != n {
                    return Err(ResolveError::LengthMismatch {
                        what: "label-list",
                        expected: n,
                        got: ll.len() as u32,
                    });
                }
                Some(ll)
            }
        };
        let kinds = match self.kinds {
            SlotRef::Absent => KindFlags::uniform(n, NodeKind::Pure),
            SlotRef::Uniform(UniformTag::AllPure) => KindFlags::uniform(n, NodeKind::Pure),
            SlotRef::Uniform(UniformTag::AllOrdered) => KindFlags::uniform(n, NodeKind::Ordered),
            SlotRef::Hash(h) => {
                let bytes = resolver.get(&h).ok_or(ResolveError::Missing(h))?;
                let kf = KindFlags::from_bytes(&bytes)?;
                if kf.len() as u32 != n {
                    return Err(ResolveError::LengthMismatch {
                        what: "kind-flags",
                        expected: n,
                        got: kf.len() as u32,
                    });
                }
                kf
            }
        };
        Ok(ResolvedDiagram {
            graph,
            labels,
            kinds,
        })
    }
}
