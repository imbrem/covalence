use bytes::Bytes;

/// A bit string of arbitrary length.
///
/// Stored as packed bytes plus an explicit bit length. Within each
/// byte, bits are little-endian: bit `i` of the bit string lives at
/// `(data[i / 8] >> (i % 8)) & 1`. Any bits in the final byte beyond
/// `len` are required to be zero; constructors enforce this.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Bits {
    len: u64,
    data: Bytes,
}

impl Bits {
    /// The empty bit string.
    pub fn empty() -> Self {
        Self {
            len: 0,
            data: Bytes::new(),
        }
    }

    /// Wrap `len` low-order bits of `data` as a bit string.
    ///
    /// Returns `None` if `data` is shorter than `ceil(len / 8)` bytes,
    /// or if `data` has trailing bits set beyond `len`.
    pub fn from_bytes(data: Bytes, len: u64) -> Option<Self> {
        let needed = len.div_ceil(8) as usize;
        if data.len() != needed {
            return None;
        }
        if !len.is_multiple_of(8) && !data.is_empty() {
            let last = *data.last()?;
            let shift = (len % 8) as u8;
            let mask = (1u8 << shift) - 1;
            if last & !mask != 0 {
                return None;
            }
        }
        Some(Self { len, data })
    }

    /// Number of bits.
    pub fn len(&self) -> u64 {
        self.len
    }

    /// True iff zero bits.
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Packed-byte representation.
    pub fn as_bytes(&self) -> &Bytes {
        &self.data
    }

    /// Read bit `i` (0-indexed). Returns `None` if `i >= len`.
    pub fn get(&self, i: u64) -> Option<bool> {
        if i >= self.len {
            return None;
        }
        let byte = self.data[(i / 8) as usize];
        Some((byte >> (i % 8)) & 1 == 1)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty() {
        let b = Bits::empty();
        assert_eq!(b.len(), 0);
        assert!(b.is_empty());
        assert!(b.get(0).is_none());
    }

    #[test]
    fn from_bytes_exact() {
        let b = Bits::from_bytes(Bytes::from_static(&[0b1010_0011]), 8).unwrap();
        assert_eq!(b.len(), 8);
        assert_eq!(b.get(0), Some(true));
        assert_eq!(b.get(1), Some(true));
        assert_eq!(b.get(2), Some(false));
        assert_eq!(b.get(5), Some(true));
        assert_eq!(b.get(7), Some(true));
        assert!(b.get(8).is_none());
    }

    #[test]
    fn from_bytes_partial() {
        // 5 bits stored in 1 byte: high 3 bits of byte must be zero.
        let b = Bits::from_bytes(Bytes::from_static(&[0b0001_0101]), 5).unwrap();
        assert_eq!(b.len(), 5);
        assert_eq!(b.get(0), Some(true));
        assert_eq!(b.get(2), Some(true));
        assert_eq!(b.get(4), Some(true));
        assert!(b.get(5).is_none());
    }

    #[test]
    fn from_bytes_rejects_garbage_in_padding() {
        // High bit set beyond declared length — rejected.
        assert!(Bits::from_bytes(Bytes::from_static(&[0b1000_0001]), 5).is_none());
    }

    #[test]
    fn from_bytes_rejects_wrong_length() {
        assert!(Bits::from_bytes(Bytes::from_static(&[0, 0]), 5).is_none());
        assert!(Bits::from_bytes(Bytes::new(), 5).is_none());
    }
}
