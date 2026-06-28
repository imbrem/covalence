//! Self-describing content identifiers.
//!
//! Wire form: `multicodec(content-type) ++ multihash(blake3, 32, digest)`.
//! Text form: multibase `'f'` (base16, lower) over that wire form.

use covalence_hash::ContentHash;
use covalence_parse::leb128::{decode_u64, encode_u64};

use crate::codec::{self, Codec};
use crate::error::ParseError;

/// Registered multihash code for BLAKE3.
pub const MULTIHASH_BLAKE3: u64 = 0x1e;
/// BLAKE3 digest length, in bytes.
pub const DIGEST_LEN: usize = 32;
/// Multibase prefix for base16-lower.
pub const MULTIBASE_BASE16: char = 'f';

/// A content identifier: a content-type [`Codec`] plus a BLAKE3 multihash.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Cid {
    /// What the addressed object is.
    pub codec: Codec,
    /// BLAKE3-256 digest of the object's canonical bytes.
    pub digest: [u8; DIGEST_LEN],
}

impl Cid {
    /// Content-address `content` under `codec`, using neutral plain BLAKE3 —
    /// i.e. covalence's `O256::blob` primitive. The neutral (non-domain-keyed)
    /// hash is what lets a peer re-verify and re-key to its own internal id.
    pub fn of(codec: Codec, content: &[u8]) -> Cid {
        Cid {
            codec,
            digest: *content.to_id().as_bytes(),
        }
    }

    /// Build a CID from an already-known digest.
    pub fn from_digest(codec: Codec, digest: [u8; DIGEST_LEN]) -> Cid {
        Cid { codec, digest }
    }

    /// Encode to wire bytes.
    pub fn encode(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(4 + DIGEST_LEN);
        self.encode_into(&mut out);
        out
    }

    /// Encode to wire bytes, appending to `out`.
    pub fn encode_into(&self, out: &mut Vec<u8>) {
        encode_u64(self.codec, out); // multicodec content-type
        encode_u64(MULTIHASH_BLAKE3, out); // multihash function
        encode_u64(DIGEST_LEN as u64, out); // multihash length
        out.extend_from_slice(&self.digest);
    }

    /// Parse a CID off the front of `buf`, returning it and the remainder.
    pub fn parse(buf: &[u8]) -> Result<(Cid, &[u8]), ParseError> {
        let (codec, n) = decode_u64(buf)?;
        let buf = &buf[n..];
        let (mh, n) = decode_u64(buf)?;
        if mh != MULTIHASH_BLAKE3 {
            return Err(ParseError::UnsupportedMultihash(mh));
        }
        let buf = &buf[n..];
        let (len, n) = decode_u64(buf)?;
        if len != DIGEST_LEN as u64 {
            return Err(ParseError::BadDigestLength(len));
        }
        let buf = &buf[n..];
        if buf.len() < DIGEST_LEN {
            return Err(ParseError::Eof);
        }
        let mut digest = [0u8; DIGEST_LEN];
        digest.copy_from_slice(&buf[..DIGEST_LEN]);
        Ok((Cid { codec, digest }, &buf[DIGEST_LEN..]))
    }

    /// Parse a CID consuming the whole buffer (no trailing bytes allowed).
    pub fn decode(buf: &[u8]) -> Result<Cid, ParseError> {
        let (cid, rest) = Cid::parse(buf)?;
        if !rest.is_empty() {
            return Err(ParseError::Trailing(rest.len()));
        }
        Ok(cid)
    }

    /// Multibase `'f'` (base16-lower) text form.
    pub fn to_text(&self) -> String {
        let mut s = String::with_capacity(1 + (4 + DIGEST_LEN) * 2);
        s.push(MULTIBASE_BASE16);
        push_hex(&mut s, &self.encode());
        s
    }

    /// Parse a multibase text form (only base16-lower `'f'` is supported).
    pub fn from_text(s: &str) -> Result<Cid, ParseError> {
        let mut chars = s.chars();
        let base = chars.next().ok_or(ParseError::EmptyMultibase)?;
        if base != MULTIBASE_BASE16 {
            return Err(ParseError::BadMultibase(base));
        }
        let bytes = decode_hex(chars.as_str())?;
        Cid::decode(&bytes)
    }
}

impl std::fmt::Display for Cid {
    /// Readable abbreviation: `codec-name#aaaaaaaa…zzzz`. Use [`Cid::to_text`]
    /// for the round-trippable wire form.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut h = String::with_capacity(DIGEST_LEN * 2);
        push_hex(&mut h, &self.digest);
        write!(
            f,
            "{}#{}…{}",
            codec::name(self.codec),
            &h[..8],
            &h[h.len() - 4..]
        )
    }
}

impl std::fmt::Debug for Cid {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Cid({})", self.to_text())
    }
}

fn push_hex(s: &mut String, bytes: &[u8]) {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    for &b in bytes {
        s.push(HEX[(b >> 4) as usize] as char);
        s.push(HEX[(b & 0xf) as usize] as char);
    }
}

fn decode_hex(s: &str) -> Result<Vec<u8>, ParseError> {
    let bytes = s.as_bytes();
    if bytes.len() % 2 != 0 {
        return Err(ParseError::BadHex);
    }
    let nibble = |c: u8| -> Result<u8, ParseError> {
        match c {
            b'0'..=b'9' => Ok(c - b'0'),
            b'a'..=b'f' => Ok(c - b'a' + 10),
            _ => Err(ParseError::BadHex),
        }
    };
    let mut out = Vec::with_capacity(bytes.len() / 2);
    for pair in bytes.chunks_exact(2) {
        out.push((nibble(pair[0])? << 4) | nibble(pair[1])?);
    }
    Ok(out)
}
