//! HTTP-shaped range types shared by the sync and async store traits.
//!
//! Mirrors RFC 9110 `Range:` / `Content-Range:` so:
//! * the HTTP server parses a request header directly into a trait call,
//! * an HTTP-backed implementation emits the same value back without
//!   lossy translation,
//! * FUSE / WASM / local consumers all speak the same vocabulary.
//!
//! The types carry no external deps (no `bytes`, no `async-trait`) so
//! they're available regardless of the `async` feature.
//!
//! Single-range only — multi-range is unsupported here; reject with `416`
//! at the HTTP boundary.

use std::ops::Range;

use crate::StoreError;

/// Metadata about a stored blob — what an HTTP `HEAD` returns.
///
/// Add fields here for forward extensions (chunk-tree root, signature,
/// mime guess); keep all of them cheaply retrievable so backends can
/// answer without reading the body.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BlobInfo {
    /// Size in bytes — corresponds to HTTP `Content-Length`.
    pub size: u64,
}

/// A byte-range request, mirroring HTTP `Range: bytes=...` (RFC 9110 §14.1.2).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ByteRange {
    /// `bytes=A-B` — closed, inclusive both ends.
    Closed { start: u64, end: u64 },
    /// `bytes=A-` — open-ended from `start` to end of blob.
    From { start: u64 },
    /// `bytes=-N` — last `length` bytes. `length == 0` is unsatisfiable.
    Suffix { length: u64 },
}

impl ByteRange {
    /// `ByteRange::From { start: 0 }` — the entire blob.
    pub fn full() -> Self {
        Self::From { start: 0 }
    }

    /// Format as the *value* of an HTTP `Range:` header.
    ///
    /// Returns e.g. `"bytes=0-99"`, `"bytes=100-"`, `"bytes=-500"`.
    pub fn to_http_header(&self) -> String {
        match self {
            Self::Closed { start, end } => format!("bytes={start}-{end}"),
            Self::From { start } => format!("bytes={start}-"),
            Self::Suffix { length } => format!("bytes=-{length}"),
        }
    }

    /// Parse from the *value* of an HTTP `Range:` header — single range only.
    ///
    /// Accepts e.g. `"bytes=0-99"`, `"bytes=100-"`, `"bytes=-500"`.
    /// Returns `None` for malformed input, multi-range, or a unit other
    /// than `bytes`. Use [`parse_http_header_multi`](Self::parse_http_header_multi)
    /// for `bytes=A-B, C-D` form.
    pub fn parse_http_header(s: &str) -> Option<Self> {
        let s = s.strip_prefix("bytes=")?;
        if s.contains(',') {
            return None;
        }
        Self::parse_spec(s)
    }

    /// Parse from the *value* of an HTTP `Range:` header that may contain
    /// multiple ranges (`bytes=0-50, 100-150, 200-`).
    ///
    /// Single-range input is accepted (returns a `Vec` of length 1).
    /// Returns `None` for malformed input or an empty range list.
    ///
    /// Multi-range batching is a higher-level concern — see
    /// [`fetch_ranges`](crate::fetch_ranges) for the fetch primitive
    /// and `multipart/byteranges` serialization for the wire format.
    pub fn parse_http_header_multi(s: &str) -> Option<Vec<Self>> {
        let body = s.strip_prefix("bytes=")?;
        let parts: Vec<_> = body
            .split(',')
            .map(str::trim)
            .filter(|p| !p.is_empty())
            .collect();
        if parts.is_empty() {
            return None;
        }
        let mut out = Vec::with_capacity(parts.len());
        for part in parts {
            out.push(Self::parse_spec(part)?);
        }
        Some(out)
    }

    /// Parse a single range spec without the `bytes=` prefix.
    fn parse_spec(s: &str) -> Option<Self> {
        let (lhs, rhs) = s.split_once('-')?;
        let lhs = lhs.trim();
        let rhs = rhs.trim();
        match (lhs.is_empty(), rhs.is_empty()) {
            (false, false) => {
                let a: u64 = lhs.parse().ok()?;
                let b: u64 = rhs.parse().ok()?;
                if a > b {
                    return None;
                }
                Some(Self::Closed { start: a, end: b })
            }
            (false, true) => Some(Self::From {
                start: lhs.parse().ok()?,
            }),
            (true, false) => Some(Self::Suffix {
                length: rhs.parse().ok()?,
            }),
            (true, true) => None,
        }
    }

    /// Resolve against a known blob size into concrete bounds.
    ///
    /// HTTP rules: out-of-range `Closed`/`From` and zero-length `Suffix`
    /// produce [`StoreError::RangeNotSatisfiable`] (HTTP 416); over-long
    /// `Suffix` clamps to the entire blob (RFC 9110 §14.1.2); over-long
    /// `Closed.end` clamps to `total-1`.
    pub fn resolve(self, total: u64) -> Result<ResolvedRange, StoreError> {
        let unsat = || StoreError::RangeNotSatisfiable { total };
        match self {
            Self::Closed { start, end } => {
                if start > end || start >= total {
                    return Err(unsat());
                }
                Ok(ResolvedRange {
                    start,
                    end: end.min(total.saturating_sub(1)),
                    total,
                })
            }
            Self::From { start } => {
                if total == 0 || start >= total {
                    return Err(unsat());
                }
                Ok(ResolvedRange {
                    start,
                    end: total - 1,
                    total,
                })
            }
            Self::Suffix { length } => {
                if length == 0 || total == 0 {
                    return Err(unsat());
                }
                Ok(ResolvedRange {
                    start: total.saturating_sub(length),
                    end: total - 1,
                    total,
                })
            }
        }
    }
}

/// Clip a half-open byte range against a known total, returning the
/// concrete `[start, end)` indices to slice with, or the appropriate
/// `ContentStore` semantics (`Ok(None)` for an empty result, `Err` for
/// unsatisfiable).
///
/// POSIX `read(2)` semantics: `start >= end` is an empty request,
/// `end > total` clamps silently to `total`, `start >= total` (on a
/// non-empty blob) is `RangeNotSatisfiable`. The special case for empty
/// blobs is: any range starting at 0 returns empty; any range starting
/// after 0 is unsatisfiable.
///
/// Use this from every `ContentStore::get_slice` override — it's the
/// authoritative range-clipping logic.
pub fn clip_slice(total: u64, range: Range<u64>) -> Result<Option<Range<usize>>, StoreError> {
    if range.start >= range.end {
        return Ok(None);
    }
    if total == 0 {
        return if range.start == 0 {
            Ok(None)
        } else {
            Err(StoreError::RangeNotSatisfiable { total })
        };
    }
    if range.start >= total {
        return Err(StoreError::RangeNotSatisfiable { total });
    }
    let end = range.end.min(total) as usize;
    Ok(Some(range.start as usize..end))
}

/// Convenience: `clip_slice` + slice + `to_vec`. Returns the slice as a
/// fresh `Vec<u8>` sized exactly to the clipped range — never to the
/// whole input. Use when the data is already in memory; otherwise use
/// [`clip_slice`] to compute bounds and then read just those bytes from
/// the backend.
pub fn slice_range(data: &[u8], range: Range<u64>) -> Result<Vec<u8>, StoreError> {
    match clip_slice(data.len() as u64, range)? {
        Some(r) => Ok(data[r].to_vec()),
        None => Ok(Vec::new()),
    }
}

impl From<Range<u64>> for ByteRange {
    /// Convert a Rust half-open `Range<u64>` into a closed [`ByteRange`].
    ///
    /// `start..end` becomes `Closed { start, end: end - 1 }`. Empty
    /// (`start >= end`) maps to `Closed { start, end: start }`, which
    /// resolves to `RangeNotSatisfiable` for any blob shorter than
    /// `start+1` — matches HTTP semantics.
    fn from(r: Range<u64>) -> Self {
        Self::Closed {
            start: r.start,
            end: r.end.saturating_sub(1).max(r.start),
        }
    }
}

/// A range resolved against a known total size — mirrors HTTP
/// `Content-Range: bytes A-B/total`. Both `start` and `end` are inclusive.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ResolvedRange {
    pub start: u64,
    pub end: u64,
    pub total: u64,
}

impl ResolvedRange {
    /// Format as the *value* of an HTTP `Content-Range:` header.
    /// Returns e.g. `"bytes 0-99/1000"`.
    pub fn to_content_range(&self) -> String {
        format!("bytes {}-{}/{}", self.start, self.end, self.total)
    }

    /// Number of bytes in this range — HTTP `Content-Length`.
    pub fn content_length(&self) -> u64 {
        self.end - self.start + 1
    }

    /// Whether this range covers the whole blob (i.e. `200`, not `206`).
    pub fn is_full(&self) -> bool {
        self.start == 0 && self.end + 1 == self.total
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn byte_range_to_http_header() {
        assert_eq!(
            ByteRange::Closed { start: 0, end: 99 }.to_http_header(),
            "bytes=0-99"
        );
        assert_eq!(ByteRange::From { start: 100 }.to_http_header(), "bytes=100-");
        assert_eq!(
            ByteRange::Suffix { length: 500 }.to_http_header(),
            "bytes=-500"
        );
        assert_eq!(ByteRange::full().to_http_header(), "bytes=0-");
    }

    #[test]
    fn byte_range_parse_http_header() {
        assert_eq!(
            ByteRange::parse_http_header("bytes=0-99"),
            Some(ByteRange::Closed { start: 0, end: 99 })
        );
        assert_eq!(
            ByteRange::parse_http_header("bytes=100-"),
            Some(ByteRange::From { start: 100 })
        );
        assert_eq!(
            ByteRange::parse_http_header("bytes=-500"),
            Some(ByteRange::Suffix { length: 500 })
        );
    }

    #[test]
    fn byte_range_parse_rejects_malformed() {
        assert_eq!(ByteRange::parse_http_header("0-99"), None);
        assert_eq!(ByteRange::parse_http_header("bytes=0-99,200-299"), None);
        assert_eq!(ByteRange::parse_http_header("bytes=-"), None);
        assert_eq!(ByteRange::parse_http_header("bytes=99-0"), None);
        assert_eq!(ByteRange::parse_http_header("bytes=abc-def"), None);
        assert_eq!(ByteRange::parse_http_header("items=0-99"), None);
    }

    #[test]
    fn byte_range_parse_multi_single_range() {
        assert_eq!(
            ByteRange::parse_http_header_multi("bytes=0-99"),
            Some(vec![ByteRange::Closed { start: 0, end: 99 }])
        );
    }

    #[test]
    fn byte_range_parse_multi_three_ranges() {
        assert_eq!(
            ByteRange::parse_http_header_multi("bytes=0-50, 100-150, 200-"),
            Some(vec![
                ByteRange::Closed { start: 0, end: 50 },
                ByteRange::Closed { start: 100, end: 150 },
                ByteRange::From { start: 200 },
            ])
        );
    }

    #[test]
    fn byte_range_parse_multi_with_suffix() {
        assert_eq!(
            ByteRange::parse_http_header_multi("bytes=0-99,-500"),
            Some(vec![
                ByteRange::Closed { start: 0, end: 99 },
                ByteRange::Suffix { length: 500 },
            ])
        );
    }

    #[test]
    fn byte_range_parse_multi_rejects_malformed() {
        assert_eq!(ByteRange::parse_http_header_multi("0-99,200-299"), None);
        assert_eq!(ByteRange::parse_http_header_multi("bytes="), None);
        // One bad part poisons the whole parse:
        assert_eq!(
            ByteRange::parse_http_header_multi("bytes=0-99,abc-def"),
            None
        );
    }

    #[test]
    fn byte_range_http_round_trip() {
        for r in [
            ByteRange::Closed { start: 0, end: 99 },
            ByteRange::Closed { start: 10, end: 10 },
            ByteRange::From { start: 0 },
            ByteRange::From { start: 1000 },
            ByteRange::Suffix { length: 1 },
            ByteRange::Suffix { length: 1024 },
        ] {
            assert_eq!(ByteRange::parse_http_header(&r.to_http_header()), Some(r));
        }
    }

    #[test]
    fn resolve_closed_within() {
        let r = ByteRange::Closed { start: 10, end: 19 }.resolve(100).unwrap();
        assert_eq!(
            r,
            ResolvedRange {
                start: 10,
                end: 19,
                total: 100
            }
        );
        assert_eq!(r.content_length(), 10);
        assert_eq!(r.to_content_range(), "bytes 10-19/100");
        assert!(!r.is_full());
    }

    #[test]
    fn resolve_closed_clamps_end_to_blob() {
        let r = ByteRange::Closed {
            start: 50,
            end: 999,
        }
        .resolve(100)
        .unwrap();
        assert_eq!(r.end, 99);
    }

    #[test]
    fn resolve_closed_start_past_end_is_416() {
        match (ByteRange::Closed {
            start: 100,
            end: 200,
        })
        .resolve(50)
        {
            Err(StoreError::RangeNotSatisfiable { total }) => assert_eq!(total, 50),
            other => panic!("expected RangeNotSatisfiable, got {other:?}"),
        }
    }

    #[test]
    fn resolve_from_within() {
        let r = ByteRange::From { start: 0 }.resolve(100).unwrap();
        assert_eq!(
            r,
            ResolvedRange {
                start: 0,
                end: 99,
                total: 100
            }
        );
        assert!(r.is_full());
    }

    #[test]
    fn resolve_from_past_end_is_416() {
        assert!(matches!(
            ByteRange::From { start: 100 }.resolve(100),
            Err(StoreError::RangeNotSatisfiable { .. })
        ));
    }

    #[test]
    fn resolve_suffix_within() {
        let r = ByteRange::Suffix { length: 10 }.resolve(100).unwrap();
        assert_eq!(r.start, 90);
        assert_eq!(r.end, 99);
        assert_eq!(r.content_length(), 10);
    }

    #[test]
    fn resolve_suffix_oversize_clamps_to_full() {
        let r = ByteRange::Suffix { length: 9999 }.resolve(100).unwrap();
        assert_eq!(r.start, 0);
        assert_eq!(r.end, 99);
        assert!(r.is_full());
    }

    #[test]
    fn resolve_suffix_zero_is_416() {
        assert!(matches!(
            ByteRange::Suffix { length: 0 }.resolve(100),
            Err(StoreError::RangeNotSatisfiable { .. })
        ));
    }

    #[test]
    fn resolve_empty_blob() {
        assert!(matches!(
            ByteRange::From { start: 0 }.resolve(0),
            Err(StoreError::RangeNotSatisfiable { .. })
        ));
        assert!(matches!(
            ByteRange::Suffix { length: 1 }.resolve(0),
            Err(StoreError::RangeNotSatisfiable { .. })
        ));
    }
}
