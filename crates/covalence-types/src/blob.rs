//! Operations of the byte-string (`bytes`) primitive type.
//!
//! `bytes` is `list u8` at the type level, but stored and computed as
//! a flat buffer for efficiency. These are the byte operations the
//! kernel commits to denotationally — `cat`, `cons`, `at`, `slice`;
//! `covalence-core`'s `reduce_prim` dispatches its `bytes*` specs here
//! so there is a single, tested implementation rather than byte
//! fiddling inlined across the kernel.
//!
//! Index/length arguments are `usize`; callers convert from the
//! kernel's arbitrary-precision `nat`, mapping out-of-range values to
//! `usize::MAX`, which these functions then clip.

use bytes::Bytes;

/// Concatenation: `cat a b = a ++ b`.
pub fn cat(a: &[u8], b: &[u8]) -> Bytes {
    let mut out = Vec::with_capacity(a.len() + b.len());
    out.extend_from_slice(a);
    out.extend_from_slice(b);
    Bytes::from(out)
}

/// Prepend a byte: `cons byte rest = [byte, ..rest]`.
pub fn cons(byte: u8, rest: &[u8]) -> Bytes {
    let mut out = Vec::with_capacity(1 + rest.len());
    out.push(byte);
    out.extend_from_slice(rest);
    Bytes::from(out)
}

/// Byte at `index`, or `0` if out of bounds.
pub fn at(bs: &[u8], index: usize) -> u8 {
    bs.get(index).copied().unwrap_or(0)
}

/// The sub-string `[start, start + len)`, clipped to the buffer
/// (saturating: an out-of-range `start` yields the empty slice, an
/// over-long `len` stops at the end).
pub fn slice(bs: &[u8], start: usize, len: usize) -> Bytes {
    let start = start.min(bs.len());
    let end = start.saturating_add(len).min(bs.len());
    Bytes::copy_from_slice(&bs[start..end])
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn cat_concatenates() {
        assert_eq!(&cat(&[1, 2], &[3, 4])[..], &[1, 2, 3, 4]);
        assert_eq!(&cat(&[], &[3])[..], &[3]);
        assert_eq!(&cat(&[1], &[])[..], &[1]);
        assert_eq!(&cat(&[], &[])[..], &[] as &[u8]);
    }

    #[test]
    fn cat_is_associative_on_samples() {
        let (a, b, c) = ([1u8, 2], [3u8], [4u8, 5, 6]);
        assert_eq!(cat(&cat(&a, &b), &c), cat(&a, &cat(&b, &c)));
    }

    #[test]
    fn cons_prepends() {
        assert_eq!(&cons(9, &[1, 2])[..], &[9, 1, 2]);
        assert_eq!(&cons(9, &[])[..], &[9]);
    }

    #[test]
    fn at_indexes_with_zero_default() {
        let bs = [7, 8, 9];
        assert_eq!(at(&bs, 0), 7);
        assert_eq!(at(&bs, 2), 9);
        assert_eq!(at(&bs, 3), 0);
        assert_eq!(at(&bs, usize::MAX), 0);
        assert_eq!(at(&[], 0), 0);
    }

    #[test]
    fn slice_saturates() {
        let bs = [1, 2, 3, 4, 5];
        assert_eq!(&slice(&bs, 1, 2)[..], &[2, 3]);
        assert_eq!(&slice(&bs, 0, 5)[..], &[1, 2, 3, 4, 5]);
        assert_eq!(&slice(&bs, 3, 99)[..], &[4, 5]);
        assert_eq!(&slice(&bs, 99, 1)[..], &[] as &[u8]);
        assert_eq!(&slice(&bs, 2, usize::MAX)[..], &[3, 4, 5]);
        assert_eq!(&slice(&bs, usize::MAX, usize::MAX)[..], &[] as &[u8]);
    }
}
