use covalence_hash::O256;

use crate::varint;

// ---------------------------------------------------------------------------
// Types
// ---------------------------------------------------------------------------

/// Field type codes — builtins low, indices high.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum FieldType {
    /// Inline bytes / string.
    Blob = 0x00,
    /// Index into the deps segment.
    Dep = 0xFD,
    /// Index into the refs segment.
    Ref = 0xFF,
}

impl FieldType {
    fn from_byte(b: u8) -> Result<Self, TableError> {
        match b {
            0x00 => Ok(Self::Blob),
            0xFD => Ok(Self::Dep),
            0xFF => Ok(Self::Ref),
            _ => Err(TableError::UnknownFieldType(b)),
        }
    }
}

/// A single field descriptor: `(repr, type)`.
///
/// - `repr = 0xFF` → variable-length (dynamic).
/// - `repr = 1..=254` → fixed-width, that many bytes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FieldSpec {
    pub repr: u8,
    pub field_type: FieldType,
}

impl FieldSpec {
    pub const fn new(repr: u8, field_type: FieldType) -> Self {
        Self { repr, field_type }
    }

    /// Dynamic blob field (variable-length).
    pub const fn blob() -> Self {
        Self::new(0xFF, FieldType::Blob)
    }

    /// Fixed-width ref index field.
    pub const fn ref_index(width: u8) -> Self {
        Self::new(width, FieldType::Ref)
    }

    /// Fixed-width dep index field.
    pub const fn dep_index(width: u8) -> Self {
        Self::new(width, FieldType::Dep)
    }

    fn is_dynamic(self) -> bool {
        self.repr == 0xFF
    }

    fn fixed_width(self) -> usize {
        if self.is_dynamic() {
            0
        } else {
            self.repr as usize
        }
    }
}

/// Errors from parsing a table blob.
#[derive(Debug, thiserror::Error)]
pub enum TableError {
    #[error("blob too short: need {need} bytes, got {got}")]
    TooShort { need: usize, got: usize },
    #[error("meta header size {0} is not a multiple of 32")]
    BadAlignment(u8),
    #[error("expected segment width {expected}, got {got}")]
    BadSegmentWidth { expected: u8, got: u8 },
    #[error("truncated varint in meta header")]
    TruncatedVarint,
    #[error("unknown field type 0x{0:02X}")]
    UnknownFieldType(u8),
    #[error("odd schema length {0} (must be even)")]
    OddSchemaLen(u64),
    #[error("segment size {size} not divisible by entry width {width}")]
    BadSegmentSize { size: usize, width: usize },
    #[error("row index {index} out of range (num_entries = {num_entries})")]
    RowOutOfRange { index: usize, num_entries: usize },
    #[error("entry {index} data is too short for fixed fields")]
    EntryTooShort { index: usize },
    #[error("offset table entry width {0} is not 1, 2, 4, or 8")]
    BadOffsetWidth(u8),
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Minimum bytes to represent values 0..n-1. Returns 1 for n <= 1.
///
/// Use this to compute canonical `repr` values for [`FieldSpec`] index fields.
pub fn min_bytes(n: usize) -> u8 {
    if n <= 1 {
        return 1;
    }
    let bits = usize::BITS - (n - 1).leading_zeros();
    ((bits + 7) / 8) as u8
}

/// Minimum power-of-2 bytes to represent a value (for offset table widths).
fn min_pow2_bytes(max_val: u64) -> u8 {
    match max_val {
        0..=0xFF => 1,
        0..=0xFFFF => 2,
        0..=0xFFFF_FFFF => 4,
        _ => 8,
    }
}

/// Read a little-endian unsigned integer of `width` bytes.
fn read_le(data: &[u8], width: usize) -> u64 {
    let mut val = 0u64;
    for i in 0..width {
        val |= (data[i] as u64) << (i * 8);
    }
    val
}

/// Write a little-endian unsigned integer of `width` bytes.
fn write_le(val: u64, width: usize, buf: &mut Vec<u8>) {
    for i in 0..width {
        buf.push((val >> (i * 8)) as u8);
    }
}

// ---------------------------------------------------------------------------
// TableBuilder
// ---------------------------------------------------------------------------

/// Builds a table blob from refs, deps, a row schema, and row data.
///
/// # Example
///
/// ```
/// use covalence_hash::O256;
/// use covalence_object::{TableBuilder, FieldSpec, FieldType};
///
/// let mut builder = TableBuilder::new(
///     vec![O256::blob("blob_mode")],               // refs
///     vec![O256::blob("child_hash")],               // deps
///     vec![FieldSpec::blob(), FieldSpec::ref_index(1), FieldSpec::dep_index(1)],
/// );
/// builder.push_row(&[b"hello.txt", &[0x00], &[0x00]]);
/// let blob = builder.build();
/// assert!(!blob.is_empty());
/// ```
pub struct TableBuilder {
    refs: Vec<O256>,
    deps: Vec<O256>,
    schema: Vec<FieldSpec>,
    /// Each row is a Vec of field values (raw bytes), in schema order.
    rows: Vec<Vec<Vec<u8>>>,
}

impl TableBuilder {
    /// Create a new builder with the given refs, deps, and row schema.
    ///
    /// Refs and deps will be sorted by hash value on `build()` for canonical
    /// representation. The returned index maps let you translate original
    /// insertion indices to sorted indices.
    pub fn new(refs: Vec<O256>, deps: Vec<O256>, schema: Vec<FieldSpec>) -> Self {
        Self {
            refs,
            deps,
            schema,
            rows: Vec::new(),
        }
    }

    /// Add a row. `fields` must have one entry per schema field, each as raw
    /// bytes (the caller is responsible for encoding indices as the correct
    /// width).
    pub fn push_row(&mut self, fields: &[&[u8]]) {
        assert_eq!(
            fields.len(),
            self.schema.len(),
            "field count must match schema"
        );
        self.rows.push(fields.iter().map(|f| f.to_vec()).collect());
    }

    /// Serialize the table into a blob.
    pub fn build(&self) -> Vec<u8> {
        // Sort refs and deps for canonical order.
        let mut sorted_refs = self.refs.clone();
        sorted_refs.sort();
        let mut sorted_deps = self.deps.clone();
        sorted_deps.sort();

        // Compute segment sizes.
        let ref_end = sorted_refs.len() * 32;
        let dep_end = ref_end + sorted_deps.len() * 32;

        // Serialize row data and collect offsets.
        let (row_data, offsets) = self.serialize_rows();
        let data_size = row_data.len() as u64;

        let ot_w = min_pow2_bytes(data_size) as usize;
        let ot_end = dep_end + offsets.len() * ot_w;
        let data_end = ot_end + row_data.len();

        // Build meta header content.
        let mut mh = Vec::new();
        mh.push(0); // placeholder for mh_size

        // Descriptor 1: refs (width=32)
        mh.push(0x20);
        varint::encode(ref_end as u64, &mut mh);

        // Descriptor 2: deps (width=32)
        mh.push(0x20);
        varint::encode(dep_end as u64, &mut mh);

        // Descriptor 3: offset table
        mh.push(ot_w as u8);
        varint::encode(ot_end as u64, &mut mh);

        // Descriptor 4: dynamic data
        mh.push(0xFF);
        varint::encode(data_end as u64, &mut mh);

        // Descriptor 5: schema
        let schema_bytes = self.schema.len() * 2;
        mh.push(0x00);
        varint::encode(schema_bytes as u64, &mut mh);
        for field in &self.schema {
            mh.push(field.repr);
            mh.push(field.field_type as u8);
        }

        // Pad to multiple of 32.
        let mh_size = (mh.len() + 31) & !31;
        mh[0] = mh_size as u8;
        mh.resize(mh_size, 0);

        // Assemble the full blob.
        let mut blob = mh;

        // Refs segment.
        for r in &sorted_refs {
            blob.extend_from_slice(r.as_bytes());
        }

        // Deps segment.
        for d in &sorted_deps {
            blob.extend_from_slice(d.as_bytes());
        }

        // Offset table.
        for &off in &offsets {
            write_le(off as u64, ot_w, &mut blob);
        }

        // Data.
        blob.extend_from_slice(&row_data);

        blob
    }

    /// Serialize all rows into (data_bytes, offsets).
    fn serialize_rows(&self) -> (Vec<u8>, Vec<usize>) {
        let mut data = Vec::new();
        let mut offsets = Vec::new();
        let ot_w = {
            // Pre-compute data size to know offset width for length prefixes.
            let est: usize = self
                .rows
                .iter()
                .map(|row| {
                    row.iter()
                        .zip(&self.schema)
                        .map(|(f, s)| {
                            if s.is_dynamic() {
                                f.len() + 8 // worst-case length prefix
                            } else {
                                s.fixed_width()
                            }
                        })
                        .sum::<usize>()
                })
                .sum();
            min_pow2_bytes(est as u64) as usize
        };

        // Find index of last dynamic field.
        let last_dynamic = self.schema.iter().rposition(|s| s.is_dynamic());

        for row in &self.rows {
            offsets.push(data.len());
            for (i, (field_data, spec)) in row.iter().zip(&self.schema).enumerate() {
                if spec.is_dynamic() {
                    if Some(i) == last_dynamic {
                        // Last dynamic field: just write raw bytes.
                        data.extend_from_slice(field_data);
                    } else {
                        // Non-last dynamic: length-prefixed with ot_w bytes.
                        write_le(field_data.len() as u64, ot_w, &mut data);
                        data.extend_from_slice(field_data);
                    }
                } else {
                    assert_eq!(
                        field_data.len(),
                        spec.fixed_width(),
                        "field {i} width mismatch: expected {}, got {}",
                        spec.fixed_width(),
                        field_data.len()
                    );
                    data.extend_from_slice(field_data);
                }
            }
        }

        (data, offsets)
    }
}

// ---------------------------------------------------------------------------
// TableParser
// ---------------------------------------------------------------------------

/// Parsed meta header — all the info needed to interpret segments.
struct ParsedHeader {
    mh_size: usize,
    ref_end: usize,
    dep_end: usize,
    ot_end: usize,
    ot_w: usize,
    data_end: usize,
    schema: Vec<FieldSpec>,
}

/// Zero-copy parser for a table blob.
///
/// ```
/// use covalence_hash::O256;
/// use covalence_object::{TableBuilder, TableParser, FieldSpec, FieldType};
///
/// // Build a simple table.
/// let schema = vec![FieldSpec::blob(), FieldSpec::ref_index(1), FieldSpec::dep_index(1)];
/// let mut builder = TableBuilder::new(
///     vec![O256::blob("mode_blob")],
///     vec![O256::blob("child")],
///     schema,
/// );
/// builder.push_row(&[b"file.txt", &[0x00], &[0x00]]);
/// let blob = builder.build();
///
/// // Parse it back.
/// let parser = TableParser::new(&blob).unwrap();
/// assert_eq!(parser.num_refs(), 1);
/// assert_eq!(parser.num_deps(), 1);
/// assert_eq!(parser.num_entries(), 1);
///
/// let row = parser.row(0).unwrap();
/// assert_eq!(row[0], b"file.txt");
/// assert_eq!(row[1], &[0x00]);
/// assert_eq!(row[2], &[0x00]);
/// ```
pub struct TableParser<'a> {
    data: &'a [u8],
    header: ParsedHeader,
}

impl<'a> TableParser<'a> {
    /// Parse a table blob.
    pub fn new(data: &'a [u8]) -> Result<Self, TableError> {
        let header = Self::parse_header(data)?;
        Ok(Self { data, header })
    }

    fn parse_header(data: &[u8]) -> Result<ParsedHeader, TableError> {
        if data.is_empty() {
            return Err(TableError::TooShort { need: 1, got: 0 });
        }

        let mh_size = data[0] as usize;
        if mh_size % 32 != 0 {
            return Err(TableError::BadAlignment(data[0]));
        }
        if data.len() < mh_size {
            return Err(TableError::TooShort {
                need: mh_size,
                got: data.len(),
            });
        }

        let mh = &data[..mh_size];
        let mut pos = 1;

        // Helper: read descriptor (width byte + varint end offset).
        let read_descriptor =
            |mh: &[u8], pos: &mut usize, expected_width: u8| -> Result<(u8, usize), TableError> {
                if *pos >= mh.len() {
                    return Err(TableError::TooShort {
                        need: *pos + 1,
                        got: mh.len(),
                    });
                }
                let width = mh[*pos];
                if width != expected_width {
                    return Err(TableError::BadSegmentWidth {
                        expected: expected_width,
                        got: width,
                    });
                }
                *pos += 1;
                let (end, consumed) =
                    varint::decode(&mh[*pos..]).ok_or(TableError::TruncatedVarint)?;
                *pos += consumed;
                Ok((width, end as usize))
            };

        // Descriptor 1: refs (width=32).
        let (_, ref_end) = read_descriptor(mh, &mut pos, 0x20)?;

        // Descriptor 2: deps (width=32).
        let (_, dep_end) = read_descriptor(mh, &mut pos, 0x20)?;

        // Descriptor 3: offset table (width=1/2/4/8).
        if pos >= mh.len() {
            return Err(TableError::TooShort {
                need: pos + 1,
                got: mh.len(),
            });
        }
        let ot_w = mh[pos] as usize;
        if !matches!(ot_w, 1 | 2 | 4 | 8) {
            return Err(TableError::BadOffsetWidth(mh[pos]));
        }
        pos += 1;
        let (ot_end_val, consumed) =
            varint::decode(&mh[pos..]).ok_or(TableError::TruncatedVarint)?;
        pos += consumed;
        let ot_end = ot_end_val as usize;

        // Descriptor 4: dynamic data (width=0xFF).
        if pos >= mh.len() || mh[pos] != 0xFF {
            return Err(TableError::BadSegmentWidth {
                expected: 0xFF,
                got: if pos < mh.len() { mh[pos] } else { 0 },
            });
        }
        pos += 1;
        let (data_end_val, consumed) =
            varint::decode(&mh[pos..]).ok_or(TableError::TruncatedVarint)?;
        pos += consumed;
        let data_end = data_end_val as usize;

        // Descriptor 5: schema (width=0x00).
        if pos >= mh.len() || mh[pos] != 0x00 {
            return Err(TableError::BadSegmentWidth {
                expected: 0x00,
                got: if pos < mh.len() { mh[pos] } else { 0 },
            });
        }
        pos += 1;
        let (schema_len, consumed) =
            varint::decode(&mh[pos..]).ok_or(TableError::TruncatedVarint)?;
        pos += consumed;

        if schema_len % 2 != 0 {
            return Err(TableError::OddSchemaLen(schema_len));
        }

        let schema_len = schema_len as usize;
        if pos + schema_len > mh.len() {
            return Err(TableError::TooShort {
                need: pos + schema_len,
                got: mh.len(),
            });
        }

        let mut schema = Vec::with_capacity(schema_len / 2);
        for i in 0..(schema_len / 2) {
            let repr = mh[pos + i * 2];
            let ft = FieldType::from_byte(mh[pos + i * 2 + 1])?;
            schema.push(FieldSpec::new(repr, ft));
        }

        // Validate segment sizes.
        let ref_size = ref_end;
        if ref_size % 32 != 0 {
            return Err(TableError::BadSegmentSize {
                size: ref_size,
                width: 32,
            });
        }
        let dep_size = dep_end.checked_sub(ref_end).ok_or(TableError::TooShort {
            need: ref_end,
            got: dep_end,
        })?;
        if dep_size % 32 != 0 {
            return Err(TableError::BadSegmentSize {
                size: dep_size,
                width: 32,
            });
        }
        let ot_size = ot_end.checked_sub(dep_end).ok_or(TableError::TooShort {
            need: dep_end,
            got: ot_end,
        })?;
        if ot_size % ot_w != 0 {
            return Err(TableError::BadSegmentSize {
                size: ot_size,
                width: ot_w,
            });
        }

        // Verify total blob length.
        let total = mh_size + data_end;
        if data.len() < total {
            return Err(TableError::TooShort {
                need: total,
                got: data.len(),
            });
        }

        Ok(ParsedHeader {
            mh_size,
            ref_end,
            dep_end,
            ot_end,
            ot_w,
            data_end,
            schema,
        })
    }

    /// Number of refs.
    pub fn num_refs(&self) -> usize {
        self.header.ref_end / 32
    }

    /// Number of deps.
    pub fn num_deps(&self) -> usize {
        (self.header.dep_end - self.header.ref_end) / 32
    }

    /// Number of entries (rows).
    pub fn num_entries(&self) -> usize {
        (self.header.ot_end - self.header.dep_end) / self.header.ot_w
    }

    /// The row schema.
    pub fn schema(&self) -> &[FieldSpec] {
        &self.header.schema
    }

    /// Get ref `i` as an O256.
    pub fn ref_hash(&self, i: usize) -> O256 {
        let start = self.header.mh_size + i * 32;
        let mut bytes = [0u8; 32];
        bytes.copy_from_slice(&self.data[start..start + 32]);
        O256::from_bytes(bytes)
    }

    /// Get dep `i` as an O256.
    pub fn dep_hash(&self, i: usize) -> O256 {
        let start = self.header.mh_size + self.header.ref_end + i * 32;
        let mut bytes = [0u8; 32];
        bytes.copy_from_slice(&self.data[start..start + 32]);
        O256::from_bytes(bytes)
    }

    /// All refs as a Vec.
    pub fn refs(&self) -> Vec<O256> {
        (0..self.num_refs()).map(|i| self.ref_hash(i)).collect()
    }

    /// All deps as a Vec.
    pub fn deps(&self) -> Vec<O256> {
        (0..self.num_deps()).map(|i| self.dep_hash(i)).collect()
    }

    /// Parse row `i`, returning one byte slice per schema field.
    pub fn row(&self, index: usize) -> Result<Vec<&'a [u8]>, TableError> {
        let n = self.num_entries();
        if index >= n {
            return Err(TableError::RowOutOfRange {
                index,
                num_entries: n,
            });
        }

        let h = &self.header;
        let base = h.mh_size;
        let ot_start = base + h.dep_end;
        let data_start = base + h.ot_end;
        let data_size = h.data_end - h.ot_end;

        // Read entry start offset.
        let off_pos = ot_start + index * h.ot_w;
        let entry_start = read_le(&self.data[off_pos..], h.ot_w) as usize;

        // Entry end: next offset or data_size.
        let entry_end = if index + 1 < n {
            let next_pos = ot_start + (index + 1) * h.ot_w;
            read_le(&self.data[next_pos..], h.ot_w) as usize
        } else {
            data_size
        };

        let entry = &self.data[data_start + entry_start..data_start + entry_end];
        self.parse_entry(index, entry)
    }

    /// Parse a single entry's bytes into field slices according to the schema.
    fn parse_entry(&self, index: usize, entry: &'a [u8]) -> Result<Vec<&'a [u8]>, TableError> {
        let schema = &self.header.schema;
        let ot_w = self.header.ot_w;

        // Find the last dynamic field index.
        let last_dynamic = schema.iter().rposition(|s| s.is_dynamic());

        // Compute trailing fixed bytes after each position (for the last dynamic field).
        let mut fields = Vec::with_capacity(schema.len());
        let mut cursor = 0;

        for (i, spec) in schema.iter().enumerate() {
            if !spec.is_dynamic() {
                // Fixed field.
                let w = spec.fixed_width();
                if cursor + w > entry.len() {
                    return Err(TableError::EntryTooShort { index });
                }
                fields.push(&entry[cursor..cursor + w]);
                cursor += w;
            } else if Some(i) == last_dynamic {
                // Last dynamic field: absorbs remainder minus trailing fixed.
                let trailing: usize = schema[i + 1..].iter().map(|s| s.fixed_width()).sum();
                let end = entry.len() - trailing;
                if cursor > end {
                    return Err(TableError::EntryTooShort { index });
                }
                fields.push(&entry[cursor..end]);
                cursor = end;
            } else {
                // Non-last dynamic: length-prefixed with ot_w bytes.
                if cursor + ot_w > entry.len() {
                    return Err(TableError::EntryTooShort { index });
                }
                let len = read_le(&entry[cursor..], ot_w) as usize;
                cursor += ot_w;
                if cursor + len > entry.len() {
                    return Err(TableError::EntryTooShort { index });
                }
                fields.push(&entry[cursor..cursor + len]);
                cursor += len;
            }
        }

        Ok(fields)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn min_bytes_cases() {
        assert_eq!(min_bytes(0), 1);
        assert_eq!(min_bytes(1), 1);
        assert_eq!(min_bytes(2), 1);
        assert_eq!(min_bytes(255), 1);
        assert_eq!(min_bytes(256), 1);
        assert_eq!(min_bytes(257), 2);
        assert_eq!(min_bytes(65536), 2);
        assert_eq!(min_bytes(65537), 3);
    }

    #[test]
    fn min_pow2_bytes_cases() {
        assert_eq!(min_pow2_bytes(0), 1);
        assert_eq!(min_pow2_bytes(255), 1);
        assert_eq!(min_pow2_bytes(256), 2);
        assert_eq!(min_pow2_bytes(65535), 2);
        assert_eq!(min_pow2_bytes(65536), 4);
    }

    #[test]
    fn empty_table() {
        let builder = TableBuilder::new(vec![], vec![], vec![]);
        let blob = builder.build();
        let parser = TableParser::new(&blob).unwrap();
        assert_eq!(parser.num_refs(), 0);
        assert_eq!(parser.num_deps(), 0);
        assert_eq!(parser.num_entries(), 0);
        assert!(parser.schema().is_empty());
    }

    #[test]
    fn directory_roundtrip() {
        let ref_blob = O256::blob("blob");
        let ref_dir = O256::blob("dir");
        let ref_exec = O256::blob("executable");
        let dep_hello = O256::blob("hello_content");
        let dep_run = O256::blob("run_content");
        let dep_src = O256::blob("src_content");

        // Sort refs/deps the same way the builder will, so we know the indices.
        let mut refs = vec![ref_blob, ref_dir, ref_exec];
        refs.sort();
        let mut deps = vec![dep_hello, dep_run, dep_src];
        deps.sort();

        let ref_w = min_bytes(refs.len());
        let dep_w = min_bytes(deps.len());

        let schema = vec![
            FieldSpec::blob(),
            FieldSpec::ref_index(ref_w),
            FieldSpec::dep_index(dep_w),
        ];

        // Find the sorted index of each ref/dep.
        let blob_idx = refs.iter().position(|r| *r == ref_blob).unwrap() as u8;
        let dir_idx = refs.iter().position(|r| *r == ref_dir).unwrap() as u8;
        let exec_idx = refs.iter().position(|r| *r == ref_exec).unwrap() as u8;
        let hello_idx = deps.iter().position(|d| *d == dep_hello).unwrap() as u8;
        let run_idx = deps.iter().position(|d| *d == dep_run).unwrap() as u8;
        let src_idx = deps.iter().position(|d| *d == dep_src).unwrap() as u8;

        let mut builder = TableBuilder::new(refs.clone(), deps.clone(), schema.clone());
        builder.push_row(&[b"hello.txt", &[blob_idx], &[hello_idx]]);
        builder.push_row(&[b"run.sh", &[exec_idx], &[run_idx]]);
        builder.push_row(&[b"src", &[dir_idx], &[src_idx]]);

        let blob = builder.build();

        // Parse it back.
        let parser = TableParser::new(&blob).unwrap();
        assert_eq!(parser.num_refs(), 3);
        assert_eq!(parser.num_deps(), 3);
        assert_eq!(parser.num_entries(), 3);
        assert_eq!(parser.schema(), &schema);

        // Verify hashes.
        assert_eq!(parser.refs(), refs);
        assert_eq!(parser.deps(), deps);

        // Verify rows.
        let row0 = parser.row(0).unwrap();
        assert_eq!(row0[0], b"hello.txt");
        assert_eq!(row0[1], &[blob_idx]);
        assert_eq!(row0[2], &[hello_idx]);

        let row1 = parser.row(1).unwrap();
        assert_eq!(row1[0], b"run.sh");
        assert_eq!(row1[1], &[exec_idx]);
        assert_eq!(row1[2], &[run_idx]);

        let row2 = parser.row(2).unwrap();
        assert_eq!(row2[0], b"src");
        assert_eq!(row2[1], &[dir_idx]);
        assert_eq!(row2[2], &[src_idx]);
    }

    #[test]
    fn meta_header_is_32_aligned() {
        let builder = TableBuilder::new(
            vec![O256::blob("r")],
            vec![O256::blob("d")],
            vec![FieldSpec::blob()],
        );
        let blob = builder.build();
        assert_eq!(blob[0] % 32, 0);
    }

    #[test]
    fn refs_and_deps_sorted() {
        let r1 = O256::blob("zzz");
        let r2 = O256::blob("aaa");
        let d1 = O256::blob("999");
        let d2 = O256::blob("111");

        let builder = TableBuilder::new(vec![r1, r2], vec![d1, d2], vec![FieldSpec::dep_index(1)]);
        let blob = builder.build();
        let parser = TableParser::new(&blob).unwrap();

        let refs = parser.refs();
        assert!(refs[0] <= refs[1]);
        let deps = parser.deps();
        assert!(deps[0] <= deps[1]);
    }

    #[test]
    fn single_entry_no_refs() {
        let dep = O256::blob("content");
        let mut builder = TableBuilder::new(
            vec![],
            vec![dep],
            vec![FieldSpec::blob(), FieldSpec::dep_index(1)],
        );
        builder.push_row(&[b"file.txt", &[0x00]]);
        let blob = builder.build();

        let parser = TableParser::new(&blob).unwrap();
        assert_eq!(parser.num_refs(), 0);
        assert_eq!(parser.num_deps(), 1);
        assert_eq!(parser.num_entries(), 1);

        let row = parser.row(0).unwrap();
        assert_eq!(row[0], b"file.txt");
        assert_eq!(row[1], &[0x00]);
    }

    #[test]
    fn multi_blob_fields() {
        // Schema: BB (key + value, like a Prolly leaf).
        let mut builder = TableBuilder::new(
            vec![O256::blob("prolly.leaf")],
            vec![],
            vec![FieldSpec::blob(), FieldSpec::blob()],
        );
        builder.push_row(&[b"key1", b"value1"]);
        builder.push_row(&[b"k2", b"a longer value here"]);
        let blob = builder.build();

        let parser = TableParser::new(&blob).unwrap();
        assert_eq!(parser.num_entries(), 2);

        let row0 = parser.row(0).unwrap();
        assert_eq!(row0[0], b"key1");
        assert_eq!(row0[1], b"value1");

        let row1 = parser.row(1).unwrap();
        assert_eq!(row1[0], b"k2");
        assert_eq!(row1[1], b"a longer value here");
    }

    #[test]
    fn row_out_of_range() {
        let builder = TableBuilder::new(vec![], vec![], vec![]);
        let blob = builder.build();
        let parser = TableParser::new(&blob).unwrap();
        assert!(parser.row(0).is_err());
    }

    #[test]
    fn schema_fingerprint_is_stable() {
        // The schema bytes in the meta header should be deterministic.
        let schema = vec![
            FieldSpec::blob(),
            FieldSpec::ref_index(1),
            FieldSpec::dep_index(1),
        ];
        let b1 = TableBuilder::new(vec![O256::blob("r")], vec![O256::blob("d")], schema.clone());
        let b2 = TableBuilder::new(vec![O256::blob("r")], vec![O256::blob("d")], schema);

        let blob1 = b1.build();
        let blob2 = b2.build();
        // Meta headers should be identical.
        let mh_size = blob1[0] as usize;
        assert_eq!(&blob1[..mh_size], &blob2[..mh_size]);
    }
}
