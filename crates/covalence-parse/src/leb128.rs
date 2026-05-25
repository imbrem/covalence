#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum DecodeError {
    #[error("unexpected end of input")]
    UnexpectedEof,
    #[error("LEB128 overflow: value exceeds {max_bits} bits")]
    Overflow { max_bits: u32 },
}

macro_rules! impl_leb128 {
    ($encode:ident, $decode:ident, $T:ty, $bits:expr) => {
        /// Encode a value as unsigned LEB128, appending to `buf`.
        pub fn $encode(value: $T, buf: &mut Vec<u8>) {
            let mut v = value;
            loop {
                let byte = (v & 0x7F) as u8;
                v >>= 7;
                if v == 0 {
                    buf.push(byte);
                    return;
                }
                buf.push(byte | 0x80);
            }
        }

        /// Decode an unsigned LEB128 value from `data`.
        /// Returns `(value, bytes_consumed)`.
        pub fn $decode(data: &[u8]) -> Result<($T, usize), DecodeError> {
            let mut result: $T = 0;
            let mut shift: u32 = 0;
            for (i, &byte) in data.iter().enumerate() {
                if shift >= $bits {
                    return Err(DecodeError::Overflow { max_bits: $bits });
                }
                let low7 = (byte & 0x7F) as $T;
                // Check that the data bits fit in the remaining space.
                if shift > 0 && low7 > (<$T>::MAX >> shift) {
                    return Err(DecodeError::Overflow { max_bits: $bits });
                }
                result |= low7 << shift;
                if byte & 0x80 == 0 {
                    return Ok((result, i + 1));
                }
                shift += 7;
            }
            Err(DecodeError::UnexpectedEof)
        }
    };
}

impl_leb128!(encode_u8, decode_u8, u8, 8);
impl_leb128!(encode_u16, decode_u16, u16, 16);
impl_leb128!(encode_u32, decode_u32, u32, 32);
impl_leb128!(encode_u64, decode_u64, u64, 64);
impl_leb128!(encode_u128, decode_u128, u128, 128);

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn roundtrip_u64_small() {
        for v in [0u64, 1, 42, 127] {
            let mut buf = Vec::new();
            encode_u64(v, &mut buf);
            assert_eq!(buf.len(), 1);
            assert_eq!(decode_u64(&buf), Ok((v, 1)));
        }
    }

    #[test]
    fn roundtrip_u64_medium() {
        for v in [128u64, 192, 255, 300, 16383] {
            let mut buf = Vec::new();
            encode_u64(v, &mut buf);
            assert_eq!(buf.len(), 2);
            assert_eq!(decode_u64(&buf), Ok((v, 2)));
        }
    }

    #[test]
    fn roundtrip_u64_large() {
        let v = 1_000_000u64;
        let mut buf = Vec::new();
        encode_u64(v, &mut buf);
        assert_eq!(decode_u64(&buf), Ok((v, buf.len())));
    }

    #[test]
    fn roundtrip_u64_max() {
        let mut buf = Vec::new();
        encode_u64(u64::MAX, &mut buf);
        assert_eq!(decode_u64(&buf), Ok((u64::MAX, buf.len())));
    }

    #[test]
    fn decode_u64_truncated() {
        assert_eq!(decode_u64(&[0x80]), Err(DecodeError::UnexpectedEof));
        assert_eq!(decode_u64(&[]), Err(DecodeError::UnexpectedEof));
    }

    #[test]
    fn decode_u64_with_trailing() {
        let mut buf = Vec::new();
        encode_u64(42, &mut buf);
        buf.push(0xFF); // trailing byte
        assert_eq!(decode_u64(&buf), Ok((42, 1)));
    }

    #[test]
    fn roundtrip_u32() {
        for v in [0u32, 1, 127, 128, 16383, 16384, u32::MAX] {
            let mut buf = Vec::new();
            encode_u32(v, &mut buf);
            assert_eq!(decode_u32(&buf), Ok((v, buf.len())));
        }
    }

    #[test]
    fn roundtrip_u16() {
        for v in [0u16, 1, 127, 128, u16::MAX] {
            let mut buf = Vec::new();
            encode_u16(v, &mut buf);
            assert_eq!(decode_u16(&buf), Ok((v, buf.len())));
        }
    }

    #[test]
    fn roundtrip_u8() {
        for v in [0u8, 1, 127, 128, u8::MAX] {
            let mut buf = Vec::new();
            encode_u8(v, &mut buf);
            assert_eq!(decode_u8(&buf), Ok((v, buf.len())));
        }
    }

    #[test]
    fn roundtrip_u128() {
        for v in [0u128, 1, u64::MAX as u128, u128::MAX] {
            let mut buf = Vec::new();
            encode_u128(v, &mut buf);
            assert_eq!(decode_u128(&buf), Ok((v, buf.len())));
        }
    }

    #[test]
    fn decode_u8_overflow() {
        // 256 encoded as LEB128: 0x80, 0x02
        let data = [0x80, 0x02];
        assert_eq!(decode_u8(&data), Err(DecodeError::Overflow { max_bits: 8 }));
    }

    #[test]
    fn decode_u16_overflow() {
        let mut buf = Vec::new();
        encode_u32(u16::MAX as u32 + 1, &mut buf);
        assert_eq!(
            decode_u16(&buf),
            Err(DecodeError::Overflow { max_bits: 16 })
        );
    }
}
