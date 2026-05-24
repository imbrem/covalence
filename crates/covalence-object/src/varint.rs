/// Encode a u64 as unsigned LEB128, appending to `buf`.
pub fn encode(value: u64, buf: &mut Vec<u8>) {
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

/// Decode an unsigned LEB128 varint from `data`.
/// Returns `(value, bytes_consumed)` or `None` if truncated.
pub fn decode(data: &[u8]) -> Option<(u64, usize)> {
    let mut result: u64 = 0;
    let mut shift: u32 = 0;
    for (i, &byte) in data.iter().enumerate() {
        if shift >= 64 {
            return None; // overflow
        }
        result |= ((byte & 0x7F) as u64) << shift;
        if byte & 0x80 == 0 {
            return Some((result, i + 1));
        }
        shift += 7;
    }
    None // truncated
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn roundtrip_small() {
        for v in [0u64, 1, 42, 127] {
            let mut buf = Vec::new();
            encode(v, &mut buf);
            assert_eq!(buf.len(), 1);
            assert_eq!(decode(&buf), Some((v, 1)));
        }
    }

    #[test]
    fn roundtrip_medium() {
        for v in [128u64, 192, 255, 300, 16383] {
            let mut buf = Vec::new();
            encode(v, &mut buf);
            assert_eq!(buf.len(), 2);
            assert_eq!(decode(&buf), Some((v, 2)));
        }
    }

    #[test]
    fn roundtrip_large() {
        let v = 1_000_000u64;
        let mut buf = Vec::new();
        encode(v, &mut buf);
        assert_eq!(decode(&buf), Some((v, buf.len())));
    }

    #[test]
    fn roundtrip_u64_max() {
        let mut buf = Vec::new();
        encode(u64::MAX, &mut buf);
        assert_eq!(decode(&buf), Some((u64::MAX, buf.len())));
    }

    #[test]
    fn decode_truncated() {
        assert_eq!(decode(&[0x80]), None);
        assert_eq!(decode(&[]), None);
    }

    #[test]
    fn decode_with_trailing() {
        let mut buf = Vec::new();
        encode(42, &mut buf);
        buf.push(0xFF); // trailing byte
        assert_eq!(decode(&buf), Some((42, 1)));
    }
}
