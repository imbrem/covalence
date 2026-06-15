//! Overlay blobs that decorate a [`Graph`](crate::Graph) without
//! changing its identity: per-node labels and per-node "ordered/pure"
//! classification.
//!
//! Both blobs are content-addressed. The wire format is internal —
//! consumers should go through [`LabelList`] / [`KindFlags`] methods
//! and never reach for the bytes directly. The hashing convention is
//! BLAKE3 keyed under a per-blob context string.

use covalence_hash::O256;
use covalence_parse::leb128::encode_u32;

use crate::canonical::{Cursor, DecodeError};

// ----------------------------------------------------------------------
// NodeKind
// ----------------------------------------------------------------------

/// Built-in per-node classification, *not* part of graph identity.
/// Lives in [`KindFlags`] overlays only.
///
/// - `Pure`    : commutes with siblings.
/// - `Ordered` : effectful; consecutive `Ordered` nodes are linked by
///   an implicit "state wire" in the string-diagram view.
#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug, Default)]
pub enum NodeKind {
    #[default]
    Pure,
    Ordered,
}

impl NodeKind {
    pub fn is_ordered(self) -> bool {
        matches!(self, NodeKind::Ordered)
    }
    pub fn as_str(self) -> &'static str {
        match self {
            NodeKind::Pure => "pure",
            NodeKind::Ordered => "ordered",
        }
    }
    pub fn parse(s: &str) -> Option<Self> {
        match s {
            "pure" => Some(NodeKind::Pure),
            "ordered" => Some(NodeKind::Ordered),
            _ => None,
        }
    }
}

// ----------------------------------------------------------------------
// LabelList
// ----------------------------------------------------------------------

const LABEL_LIST_MAGIC: [u8; 4] = *b"LBLS";
const LABEL_LIST_VERSION: u8 = 1;
/// BLAKE3 derivation context — also the tag for label-list overlays
/// in a tagged store.
pub const LABEL_LIST_HASH_CTX: &str = "cov:graph@0.1.0 label-list";

/// One label per node. `None` = no label for that slot. Length-prefixed
/// UTF-8 over the wire. Hash domain: `"cov:graph@0.1.0 label-list"`.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct LabelList {
    labels: Vec<Option<String>>,
}

impl LabelList {
    pub fn new(labels: Vec<Option<String>>) -> Self {
        Self { labels }
    }
    pub fn from_strings(labels: impl IntoIterator<Item = String>) -> Self {
        Self {
            labels: labels.into_iter().map(Some).collect(),
        }
    }
    pub fn empty() -> Self {
        Self::default()
    }
    pub fn len(&self) -> usize {
        self.labels.len()
    }
    pub fn is_empty(&self) -> bool {
        self.labels.is_empty()
    }
    pub fn get(&self, i: usize) -> Option<&str> {
        self.labels.get(i).and_then(|s| s.as_deref())
    }
    pub fn iter(&self) -> impl Iterator<Item = Option<&str>> + '_ {
        self.labels.iter().map(|s| s.as_deref())
    }

    /// Canonical bytes. Format:
    /// `"LBLS" + version + LEB(count) + (presence(0/1) + LEB(len) + utf-8)*`.
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut buf = Vec::with_capacity(8 + self.labels.len() * 8);
        buf.extend_from_slice(&LABEL_LIST_MAGIC);
        buf.push(LABEL_LIST_VERSION);
        encode_u32(self.labels.len() as u32, &mut buf);
        for label in &self.labels {
            match label {
                None => buf.push(0),
                Some(s) => {
                    buf.push(1);
                    let bytes = s.as_bytes();
                    encode_u32(bytes.len() as u32, &mut buf);
                    buf.extend_from_slice(bytes);
                }
            }
        }
        buf
    }

    pub fn from_bytes(data: &[u8]) -> Result<Self, DecodeError> {
        let mut d = Cursor::new(data);
        let magic = d.take(4)?;
        if magic != LABEL_LIST_MAGIC {
            let mut got = [0u8; 4];
            got.copy_from_slice(magic);
            return Err(DecodeError::BadMagic { got });
        }
        let version = d.take(1)?[0];
        if version != LABEL_LIST_VERSION {
            return Err(DecodeError::UnsupportedVersion {
                got: version,
                supported: LABEL_LIST_VERSION,
            });
        }
        let count = d.read_u32()? as usize;
        let mut labels = Vec::with_capacity(count);
        for _ in 0..count {
            let presence = d.take(1)?[0];
            let label = match presence {
                0 => None,
                1 => {
                    let len = d.read_u32()? as usize;
                    let bytes = d.take(len)?.to_vec();
                    Some(
                        String::from_utf8(bytes)
                            .map_err(|_| DecodeError::BadUtf8 { what: "label" })?,
                    )
                }
                got => {
                    return Err(DecodeError::BadEnumTag {
                        what: "label-presence",
                        got,
                    });
                }
            };
            labels.push(label);
        }
        if d.remaining() > 0 {
            return Err(DecodeError::TrailingBytes(d.remaining()));
        }
        Ok(Self { labels })
    }

    /// Unkeyed BLAKE3 hash of the canonical bytes — the
    /// content-addressed identity for a plain blob store.
    pub fn content_hash(&self) -> O256 {
        O256::blob(self.to_bytes())
    }

    /// Tagged identity under the `LABEL_LIST_HASH_CTX` domain:
    /// `O256::context(tag, BLAKE3(bytes))`.
    pub fn hash(&self) -> O256 {
        O256::context(LABEL_LIST_HASH_CTX, self.content_hash().as_bytes())
    }
}

// ----------------------------------------------------------------------
// KindFlags
// ----------------------------------------------------------------------

const KIND_FLAGS_MAGIC: [u8; 4] = *b"KFLG";
const KIND_FLAGS_VERSION: u8 = 1;
/// BLAKE3 derivation context — also the tag for kind-flags overlays
/// in a tagged store.
pub const KIND_FLAGS_HASH_CTX: &str = "cov:graph@0.1.0 kind-flags";

/// One bit per node: 0 = [`NodeKind::Pure`], 1 = [`NodeKind::Ordered`].
/// Bits are packed LSB-first within each byte.
///
/// Format: `"KFLG" + version + LEB(count) + ceil(count/8) bytes`.
/// Hash domain: `"cov:graph@0.1.0 kind-flags"`.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct KindFlags {
    count: u32,
    bits: Vec<u8>,
}

impl KindFlags {
    pub fn new(kinds: impl IntoIterator<Item = NodeKind>) -> Self {
        let kinds: Vec<NodeKind> = kinds.into_iter().collect();
        let count = kinds.len() as u32;
        let mut bits = vec![0u8; count.div_ceil(8) as usize];
        for (i, k) in kinds.iter().enumerate() {
            if k.is_ordered() {
                bits[i / 8] |= 1 << (i % 8);
            }
        }
        Self { count, bits }
    }

    /// All `n` nodes uniformly classified.
    pub fn uniform(n: u32, kind: NodeKind) -> Self {
        let mut bits = vec![0u8; n.div_ceil(8) as usize];
        if kind.is_ordered() {
            for i in 0..n as usize {
                bits[i / 8] |= 1 << (i % 8);
            }
        }
        Self { count: n, bits }
    }

    pub fn len(&self) -> usize {
        self.count as usize
    }
    pub fn is_empty(&self) -> bool {
        self.count == 0
    }

    pub fn get(&self, i: usize) -> Option<NodeKind> {
        if i >= self.count as usize {
            return None;
        }
        let bit = self.bits[i / 8] & (1 << (i % 8));
        Some(if bit != 0 {
            NodeKind::Ordered
        } else {
            NodeKind::Pure
        })
    }

    pub fn iter(&self) -> impl Iterator<Item = NodeKind> + '_ {
        (0..self.count as usize).map(move |i| self.get(i).unwrap())
    }

    /// True if every flag is the same value (or the list is empty).
    pub fn is_uniform_as(&self) -> Option<NodeKind> {
        let mut it = self.iter();
        let first = it.next()?;
        if it.all(|k| k == first) {
            Some(first)
        } else {
            None
        }
    }

    pub fn ordered_node_indices(&self) -> impl Iterator<Item = u32> + '_ {
        (0..self.count).filter(move |i| self.get(*i as usize) == Some(NodeKind::Ordered))
    }

    pub fn to_bytes(&self) -> Vec<u8> {
        let mut buf = Vec::with_capacity(8 + self.bits.len());
        buf.extend_from_slice(&KIND_FLAGS_MAGIC);
        buf.push(KIND_FLAGS_VERSION);
        encode_u32(self.count, &mut buf);
        // Mask out any trailing bits past `count` so the byte form is canonical.
        let mut bits = self.bits.clone();
        if let Some(last) = bits.last_mut() {
            let used = (self.count % 8) as u8;
            if used != 0 {
                *last &= (1 << used) - 1;
            }
        }
        buf.extend_from_slice(&bits);
        buf
    }

    pub fn from_bytes(data: &[u8]) -> Result<Self, DecodeError> {
        let mut d = Cursor::new(data);
        let magic = d.take(4)?;
        if magic != KIND_FLAGS_MAGIC {
            let mut got = [0u8; 4];
            got.copy_from_slice(magic);
            return Err(DecodeError::BadMagic { got });
        }
        let version = d.take(1)?[0];
        if version != KIND_FLAGS_VERSION {
            return Err(DecodeError::UnsupportedVersion {
                got: version,
                supported: KIND_FLAGS_VERSION,
            });
        }
        let count = d.read_u32()?;
        let bytes = count.div_ceil(8) as usize;
        let bits = d.take(bytes)?.to_vec();
        if d.remaining() > 0 {
            return Err(DecodeError::TrailingBytes(d.remaining()));
        }
        Ok(Self { count, bits })
    }

    /// Unkeyed BLAKE3 hash of the canonical bytes.
    pub fn content_hash(&self) -> O256 {
        O256::blob(self.to_bytes())
    }

    /// Tagged identity under the `KIND_FLAGS_HASH_CTX` domain:
    /// `O256::context(tag, BLAKE3(bytes))`.
    pub fn hash(&self) -> O256 {
        O256::context(KIND_FLAGS_HASH_CTX, self.content_hash().as_bytes())
    }
}
