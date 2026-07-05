//! Git packfile parser with delta resolution.
//!
//! Parses the PACK format (version 2) including:
//! - Non-delta objects: commit, tree, blob, tag (types 1–4)
//! - Offset deltas (type 6) — resolved against earlier objects in the pack
//! - Reference deltas (type 7) — resolved against objects in the store
//!
//! Objects are stored directly into a [`GitBackend`]
//! as they are resolved.

use std::collections::HashMap;
use std::io::{self, Cursor, Read};

use covalence_hash::gix_hash;
use flate2::read::ZlibDecoder;

use crate::store::{GitBackend, GitObjectKind};

/// Result of parsing a complete packfile.
#[derive(Debug)]
pub struct PackResult {
    /// Number of objects successfully stored.
    pub objects_stored: usize,
}

/// An object resolved during pack parsing (before storage).
struct ResolvedObject {
    kind: GitObjectKind,
    data: Vec<u8>,
}

/// Parse a packfile and store all objects into the given backend.
pub fn parse_pack(pack_data: &[u8], backend: &impl GitBackend) -> io::Result<PackResult> {
    if pack_data.len() < 12 {
        return Err(invalid("packfile too short for header"));
    }

    // Header: PACK + version(4) + object_count(4)
    if &pack_data[..4] != b"PACK" {
        return Err(invalid("missing PACK signature"));
    }

    let version = u32::from_be_bytes([pack_data[4], pack_data[5], pack_data[6], pack_data[7]]);
    if version != 2 && version != 3 {
        return Err(invalid(format!("unsupported pack version: {version}")));
    }

    let object_count =
        u32::from_be_bytes([pack_data[8], pack_data[9], pack_data[10], pack_data[11]]);

    // Verify trailing checksum (SHA-1 over everything except the last 20 bytes).
    if pack_data.len() < 20 {
        return Err(invalid("packfile too short for checksum"));
    }
    let (content, checksum) = pack_data.split_at(pack_data.len() - 20);
    let mut hasher = gix_hash::hasher(gix_hash::Kind::Sha1);
    hasher.update(content);
    let computed = hasher.try_finalize().expect("sha1 finalize");
    if computed.as_bytes() != checksum {
        return Err(invalid("pack checksum mismatch"));
    }

    // Maps pack offset → resolved object (for ofs_delta resolution).
    let mut offset_map: HashMap<usize, ResolvedObject> = HashMap::new();
    let mut objects_stored: usize = 0;
    let mut pos = 12; // after header

    for _ in 0..object_count {
        let entry_offset = pos;
        let (obj_type, size, header_end) = read_type_and_size(content, pos)?;
        pos = header_end;

        match obj_type {
            // Non-delta: commit(1), tree(2), blob(3), tag(4)
            1..=4 => {
                let kind = type_to_kind(obj_type)?;
                let (data, consumed) = zlib_decompress(content, pos, size)?;
                pos += consumed;

                backend
                    .write_object(kind, &data)
                    .map_err(|e| invalid(format!("store write: {e}")))?;
                objects_stored += 1;

                offset_map.insert(entry_offset, ResolvedObject { kind, data });
            }
            // ofs_delta (6)
            6 => {
                let (neg_offset, ofs_end) = read_ofs_delta_offset(content, pos)?;
                pos = ofs_end;

                let base_offset = entry_offset
                    .checked_sub(neg_offset)
                    .ok_or_else(|| invalid("ofs_delta offset underflow"))?;

                let (delta_data, consumed) = zlib_decompress(content, pos, size)?;
                pos += consumed;

                let base = offset_map.get(&base_offset).ok_or_else(|| {
                    invalid(format!("ofs_delta: base not found at offset {base_offset}"))
                })?;

                let resolved = apply_delta(&base.data, &delta_data)?;

                backend
                    .write_object(base.kind, &resolved)
                    .map_err(|e| invalid(format!("store write: {e}")))?;
                objects_stored += 1;

                offset_map.insert(
                    entry_offset,
                    ResolvedObject {
                        kind: base.kind,
                        data: resolved,
                    },
                );
            }
            // ref_delta (7)
            7 => {
                if content.len() < pos + 20 {
                    return Err(invalid("ref_delta: truncated base OID"));
                }
                let base_oid = gix_hash::ObjectId::from_bytes_or_panic(&content[pos..pos + 20]);
                pos += 20;

                let (delta_data, consumed) = zlib_decompress(content, pos, size)?;
                pos += consumed;

                let base_obj = backend.read_object(&base_oid).map_err(|e| {
                    invalid(format!("ref_delta: base {base_oid} not in store: {e}"))
                })?;

                let resolved = apply_delta(&base_obj.data, &delta_data)?;

                backend
                    .write_object(base_obj.kind, &resolved)
                    .map_err(|e| invalid(format!("store write: {e}")))?;
                objects_stored += 1;

                offset_map.insert(
                    entry_offset,
                    ResolvedObject {
                        kind: base_obj.kind,
                        data: resolved,
                    },
                );
            }
            _ => {
                return Err(invalid(format!("unknown pack object type: {obj_type}")));
            }
        }
    }

    Ok(PackResult { objects_stored })
}

/// Read the type+size varint from a pack entry header.
///
/// Returns (object_type, uncompressed_size, position_after_header).
fn read_type_and_size(data: &[u8], start: usize) -> io::Result<(u8, usize, usize)> {
    if start >= data.len() {
        return Err(invalid("unexpected end of pack data"));
    }

    let first = data[start];
    let obj_type = (first >> 4) & 0x07;
    let mut size = (first & 0x0f) as usize;
    let mut shift = 4;
    let mut pos = start + 1;

    if first & 0x80 != 0 {
        loop {
            if pos >= data.len() {
                return Err(invalid("truncated type+size varint"));
            }
            let byte = data[pos];
            pos += 1;
            size |= ((byte & 0x7f) as usize) << shift;
            shift += 7;
            if byte & 0x80 == 0 {
                break;
            }
        }
    }

    Ok((obj_type, size, pos))
}

/// Read the negative offset varint used by ofs_delta entries.
fn read_ofs_delta_offset(data: &[u8], start: usize) -> io::Result<(usize, usize)> {
    if start >= data.len() {
        return Err(invalid("truncated ofs_delta offset"));
    }

    let mut pos = start;
    let mut byte = data[pos];
    pos += 1;
    let mut offset = (byte & 0x7f) as usize;

    while byte & 0x80 != 0 {
        if pos >= data.len() {
            return Err(invalid("truncated ofs_delta offset"));
        }
        offset += 1;
        byte = data[pos];
        pos += 1;
        offset = (offset << 7) | (byte & 0x7f) as usize;
    }

    Ok((offset, pos))
}

/// Decompress zlib data from `data[start..]`.
///
/// Returns (decompressed_bytes, bytes_consumed_from_input).
fn zlib_decompress(
    data: &[u8],
    start: usize,
    expected_size: usize,
) -> io::Result<(Vec<u8>, usize)> {
    let mut decoder = ZlibDecoder::new(Cursor::new(&data[start..]));
    let mut buf = Vec::with_capacity(expected_size);
    decoder.read_to_end(&mut buf)?;

    // How many compressed bytes were consumed?
    let consumed = decoder.total_in() as usize;
    Ok((buf, consumed))
}

/// Map pack type number (1–4) to [`GitObjectKind`].
fn type_to_kind(t: u8) -> io::Result<GitObjectKind> {
    match t {
        1 => Ok(GitObjectKind::Commit),
        2 => Ok(GitObjectKind::Tree),
        3 => Ok(GitObjectKind::Blob),
        4 => Ok(GitObjectKind::Tag),
        _ => Err(invalid(format!("not a base type: {t}"))),
    }
}

/// Apply a git delta instruction stream to a base object.
///
/// Delta format:
/// - Source size (varint)
/// - Target size (varint)
/// - Instructions:
///   - `0xxxxxxx` (1 ≤ x ≤ 127): insert next x literal bytes
///   - `1oooosss`: copy from base at offset/size encoded in following bytes
fn apply_delta(base: &[u8], delta: &[u8]) -> io::Result<Vec<u8>> {
    let mut pos = 0;

    // Read source size varint.
    let (_src_size, new_pos) = read_delta_varint(delta, pos)?;
    pos = new_pos;

    // Read target size varint.
    let (tgt_size, new_pos) = read_delta_varint(delta, pos)?;
    pos = new_pos;

    let mut result = Vec::with_capacity(tgt_size);

    while pos < delta.len() {
        let cmd = delta[pos];
        pos += 1;

        if cmd == 0 {
            return Err(invalid("delta: reserved instruction 0"));
        }

        if cmd & 0x80 != 0 {
            // Copy instruction
            let mut offset: u32 = 0;
            let mut size: u32 = 0;

            if cmd & 0x01 != 0 {
                offset |= (delta
                    .get(pos)
                    .copied()
                    .ok_or_else(|| invalid("delta: truncated copy"))?)
                    as u32;
                pos += 1;
            }
            if cmd & 0x02 != 0 {
                offset |= ((delta
                    .get(pos)
                    .copied()
                    .ok_or_else(|| invalid("delta: truncated copy"))?)
                    as u32)
                    << 8;
                pos += 1;
            }
            if cmd & 0x04 != 0 {
                offset |= ((delta
                    .get(pos)
                    .copied()
                    .ok_or_else(|| invalid("delta: truncated copy"))?)
                    as u32)
                    << 16;
                pos += 1;
            }
            if cmd & 0x08 != 0 {
                offset |= ((delta
                    .get(pos)
                    .copied()
                    .ok_or_else(|| invalid("delta: truncated copy"))?)
                    as u32)
                    << 24;
                pos += 1;
            }

            if cmd & 0x10 != 0 {
                size |= (delta
                    .get(pos)
                    .copied()
                    .ok_or_else(|| invalid("delta: truncated copy"))?)
                    as u32;
                pos += 1;
            }
            if cmd & 0x20 != 0 {
                size |= ((delta
                    .get(pos)
                    .copied()
                    .ok_or_else(|| invalid("delta: truncated copy"))?)
                    as u32)
                    << 8;
                pos += 1;
            }
            if cmd & 0x40 != 0 {
                size |= ((delta
                    .get(pos)
                    .copied()
                    .ok_or_else(|| invalid("delta: truncated copy"))?)
                    as u32)
                    << 16;
                pos += 1;
            }

            if size == 0 {
                size = 0x10000;
            }

            let off = offset as usize;
            let sz = size as usize;
            if off + sz > base.len() {
                return Err(invalid(format!(
                    "delta copy out of bounds: offset={off}, size={sz}, base_len={}",
                    base.len()
                )));
            }
            result.extend_from_slice(&base[off..off + sz]);
        } else {
            // Insert instruction: cmd is the number of literal bytes.
            let n = cmd as usize;
            if pos + n > delta.len() {
                return Err(invalid("delta: truncated insert data"));
            }
            result.extend_from_slice(&delta[pos..pos + n]);
            pos += n;
        }
    }

    if result.len() != tgt_size {
        return Err(invalid(format!(
            "delta: result size mismatch: got {}, expected {tgt_size}",
            result.len()
        )));
    }

    Ok(result)
}

/// Read a delta-style varint (little-endian, 7 bits per byte, MSB continuation).
fn read_delta_varint(data: &[u8], start: usize) -> io::Result<(usize, usize)> {
    let mut pos = start;
    let mut value: usize = 0;
    let mut shift = 0;

    loop {
        if pos >= data.len() {
            return Err(invalid("truncated delta varint"));
        }
        let byte = data[pos];
        pos += 1;
        value |= ((byte & 0x7f) as usize) << shift;
        shift += 7;
        if byte & 0x80 == 0 {
            break;
        }
    }

    Ok((value, pos))
}

fn invalid(msg: impl std::fmt::Display) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, msg.to_string())
}

#[cfg(test)]
mod tests {
    use super::*;
    use flate2::Compression;
    use flate2::write::ZlibEncoder;
    use std::io::Write;

    /// Build a minimal valid packfile containing a single non-delta blob.
    fn make_single_blob_pack(data: &[u8]) -> Vec<u8> {
        let mut pack = Vec::new();
        // Header: PACK, version 2, 1 object
        pack.extend_from_slice(b"PACK");
        pack.extend_from_slice(&2u32.to_be_bytes());
        pack.extend_from_slice(&1u32.to_be_bytes());

        // Entry: type=3 (blob), size varint, zlib-compressed data
        let size = data.len();
        let mut header_bytes = Vec::new();
        // First byte: MSB=0 if size fits, type in bits 6-4, size in bits 3-0
        let type_bits: u8 = 3; // blob
        if size < 16 {
            header_bytes.push((type_bits << 4) | (size as u8));
        } else {
            header_bytes.push(0x80 | (type_bits << 4) | (size as u8 & 0x0f));
            let mut remaining = size >> 4;
            loop {
                if remaining < 128 {
                    header_bytes.push(remaining as u8);
                    break;
                } else {
                    header_bytes.push(0x80 | (remaining as u8 & 0x7f));
                    remaining >>= 7;
                }
            }
        }
        pack.extend_from_slice(&header_bytes);

        // Zlib-compress the data
        let mut encoder = ZlibEncoder::new(Vec::new(), Compression::default());
        encoder.write_all(data).unwrap();
        let compressed = encoder.finish().unwrap();
        pack.extend_from_slice(&compressed);

        // SHA-1 checksum over everything so far
        let mut hasher = gix_hash::hasher(gix_hash::Kind::Sha1);
        hasher.update(&pack);
        let checksum = hasher.try_finalize().unwrap();
        pack.extend_from_slice(checksum.as_bytes());

        pack
    }

    /// Simple in-memory backend for testing.
    struct MemBackend {
        objects: std::sync::Mutex<HashMap<gix_hash::ObjectId, (GitObjectKind, Vec<u8>)>>,
    }

    impl MemBackend {
        fn new() -> Self {
            Self {
                objects: std::sync::Mutex::new(HashMap::new()),
            }
        }
    }

    impl GitBackend for MemBackend {
        fn read_object(
            &self,
            id: &gix_hash::ObjectId,
        ) -> Result<crate::store::GitObject, covalence_store::StoreError> {
            let map = self.objects.lock().unwrap();
            let (kind, data) = map
                .get(id)
                .ok_or_else(|| covalence_store::StoreError::Io(format!("not found: {id}")))?;
            Ok(crate::store::GitObject {
                kind: *kind,
                data: data.clone(),
            })
        }

        fn write_object(
            &self,
            kind: GitObjectKind,
            data: &[u8],
        ) -> Result<gix_hash::ObjectId, covalence_store::StoreError> {
            let mut hasher = gix_hash::hasher(gix_hash::Kind::Sha1);
            let header = format!("{} {}\0", kind.as_str(), data.len());
            hasher.update(header.as_bytes());
            hasher.update(data);
            let oid = hasher.try_finalize().unwrap();
            self.objects
                .lock()
                .unwrap()
                .insert(oid, (kind, data.to_vec()));
            Ok(oid)
        }

        fn contains_object(&self, id: &gix_hash::ObjectId) -> bool {
            self.objects.lock().unwrap().contains_key(id)
        }

        fn hash_kind(&self) -> gix_hash::Kind {
            gix_hash::Kind::Sha1
        }
    }

    #[test]
    fn parse_single_blob() {
        let blob_data = b"hello world";
        let pack = make_single_blob_pack(blob_data);
        let backend = MemBackend::new();

        let result = parse_pack(&pack, &backend).unwrap();
        assert_eq!(result.objects_stored, 1);

        // Verify the blob was stored
        let expected_oid = {
            let mut h = gix_hash::hasher(gix_hash::Kind::Sha1);
            h.update(format!("blob {}\0", blob_data.len()).as_bytes());
            h.update(blob_data);
            h.try_finalize().unwrap()
        };
        assert!(backend.contains_object(&expected_oid));
        let obj = backend.read_object(&expected_oid).unwrap();
        assert_eq!(obj.kind, GitObjectKind::Blob);
        assert_eq!(obj.data, blob_data);
    }

    #[test]
    fn parse_empty_blob() {
        let blob_data = b"";
        let pack = make_single_blob_pack(blob_data);
        let backend = MemBackend::new();

        let result = parse_pack(&pack, &backend).unwrap();
        assert_eq!(result.objects_stored, 1);
    }

    #[test]
    fn parse_large_blob() {
        // Blob larger than 15 bytes to exercise multi-byte size varint.
        let blob_data = vec![0xABu8; 300];
        let pack = make_single_blob_pack(&blob_data);
        let backend = MemBackend::new();

        let result = parse_pack(&pack, &backend).unwrap();
        assert_eq!(result.objects_stored, 1);
    }

    #[test]
    fn bad_magic_rejected() {
        let mut pack = make_single_blob_pack(b"x");
        pack[0] = b'X'; // corrupt magic
        // Also need to fix checksum...but it will fail on magic first
        let backend = MemBackend::new();
        assert!(parse_pack(&pack, &backend).is_err());
    }

    #[test]
    fn bad_checksum_rejected() {
        let mut pack = make_single_blob_pack(b"x");
        let len = pack.len();
        pack[len - 1] ^= 0xff; // corrupt checksum
        let backend = MemBackend::new();
        assert!(parse_pack(&pack, &backend).is_err());
    }

    #[test]
    fn apply_delta_insert_only() {
        let base = b"hello";
        // Delta: src_size=5, tgt_size=11, insert 11 bytes "hello world"
        let mut delta = Vec::new();
        delta.push(5); // src size
        delta.push(11); // tgt size
        delta.push(11); // insert 11 bytes
        delta.extend_from_slice(b"hello world");

        let result = apply_delta(base, &delta).unwrap();
        assert_eq!(result, b"hello world");
    }

    #[test]
    fn apply_delta_copy_only() {
        let base = b"hello world";
        // Delta: src_size=11, tgt_size=5, copy offset=0 size=5
        let delta = vec![
            11, // src size
            5,  // tgt size
            // Copy instruction: 1_0001_0001 -> offset byte + size byte
            0x80 | 0x01 | 0x10, // copy, offset byte 0, size byte 0
            0x00,               // offset = 0
            0x05,               // size = 5
        ];

        let result = apply_delta(base, &delta).unwrap();
        assert_eq!(result, b"hello");
    }

    #[test]
    fn apply_delta_copy_and_insert() {
        let base = b"hello";
        // Target: "hello world" — copy "hello" from base, insert " world"
        let mut delta = vec![
            5,  // src size
            11, // tgt size
            // Copy: offset=0, size=5
            0x80 | 0x01 | 0x10,
            0x00, // offset = 0
            0x05, // size = 5
            // Insert 6 bytes: " world"
            6,
        ];
        delta.extend_from_slice(b" world");

        let result = apply_delta(base, &delta).unwrap();
        assert_eq!(result, b"hello world");
    }

    /// Build a pack with one base blob and one ofs_delta referencing it.
    #[test]
    fn parse_ofs_delta() {
        let base_data = b"the base content here";
        let target_data = b"the base content here, extended!";

        // Build delta instructions: copy all of base, insert ", extended!"
        let mut delta_instr = vec![
            base_data.len() as u8,   // src size
            target_data.len() as u8, // tgt size
            // Copy offset=0, size=base_data.len()
            0x80 | 0x01 | 0x10,
            0x00,
            base_data.len() as u8,
        ];
        // Insert the rest
        let suffix = b", extended!";
        delta_instr.push(suffix.len() as u8);
        delta_instr.extend_from_slice(suffix);

        let mut pack = Vec::new();
        pack.extend_from_slice(b"PACK");
        pack.extend_from_slice(&2u32.to_be_bytes());
        pack.extend_from_slice(&2u32.to_be_bytes()); // 2 objects

        // Object 1: base blob
        let base_entry_offset = pack.len();
        {
            let size = base_data.len();
            if size < 16 {
                pack.push((3 << 4) | (size as u8));
            } else {
                pack.push(0x80 | (3 << 4) | (size as u8 & 0x0f));
                let mut remaining = size >> 4;
                loop {
                    if remaining < 128 {
                        pack.push(remaining as u8);
                        break;
                    } else {
                        pack.push(0x80 | (remaining as u8 & 0x7f));
                        remaining >>= 7;
                    }
                }
            }
            let mut enc = ZlibEncoder::new(Vec::new(), Compression::default());
            enc.write_all(base_data).unwrap();
            pack.extend_from_slice(&enc.finish().unwrap());
        }

        // Object 2: ofs_delta referencing object 1
        let delta_entry_offset = pack.len();
        {
            let size = delta_instr.len();
            if size < 16 {
                pack.push((6 << 4) | (size as u8));
            } else {
                pack.push(0x80 | (6 << 4) | (size as u8 & 0x0f));
                let mut remaining = size >> 4;
                loop {
                    if remaining < 128 {
                        pack.push(remaining as u8);
                        break;
                    } else {
                        pack.push(0x80 | (remaining as u8 & 0x7f));
                        remaining >>= 7;
                    }
                }
            }
            // ofs_delta offset (negative offset to base)
            let neg_offset = delta_entry_offset - base_entry_offset;
            encode_ofs_offset(&mut pack, neg_offset);

            let mut enc = ZlibEncoder::new(Vec::new(), Compression::default());
            enc.write_all(&delta_instr).unwrap();
            pack.extend_from_slice(&enc.finish().unwrap());
        }

        // Checksum
        let mut hasher = gix_hash::hasher(gix_hash::Kind::Sha1);
        hasher.update(&pack);
        let checksum = hasher.try_finalize().unwrap();
        pack.extend_from_slice(checksum.as_bytes());

        let backend = MemBackend::new();
        let result = parse_pack(&pack, &backend).unwrap();
        assert_eq!(result.objects_stored, 2);

        // Verify the delta-resolved object exists with correct content
        let expected_oid = {
            let mut h = gix_hash::hasher(gix_hash::Kind::Sha1);
            h.update(format!("blob {}\0", target_data.len()).as_bytes());
            h.update(target_data.as_slice());
            h.try_finalize().unwrap()
        };
        assert!(backend.contains_object(&expected_oid));
        let obj = backend.read_object(&expected_oid).unwrap();
        assert_eq!(obj.data, target_data);
    }

    /// Encode a negative offset for ofs_delta (same encoding git uses).
    fn encode_ofs_offset(buf: &mut Vec<u8>, mut offset: usize) {
        let mut bytes = Vec::new();
        bytes.push((offset & 0x7f) as u8);
        offset >>= 7;
        while offset > 0 {
            offset -= 1;
            bytes.push(0x80 | (offset & 0x7f) as u8);
            offset >>= 7;
        }
        bytes.reverse();
        buf.extend_from_slice(&bytes);
    }
}
