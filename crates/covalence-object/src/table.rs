use covalence_hash::O256;

use covalence_parse::leb128;

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

    /// Fixed-width raw blob field (e.g. 2 bytes for a u16 mode).
    pub const fn fixed(width: u8) -> Self {
        Self::new(width, FieldType::Blob)
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
    #[error("invalid git tree: {0}")]
    InvalidGitTree(String),
    #[error("invalid git commit: {0}")]
    InvalidGitCommit(String),
    #[error("schema mismatch: expected {expected} fields, got {got}")]
    SchemaMismatch { expected: usize, got: usize },
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
pub(crate) fn read_le(data: &[u8], width: usize) -> u64 {
    let mut val = 0u64;
    for i in 0..width {
        val |= (data[i] as u64) << (i * 8);
    }
    val
}

/// Write a little-endian unsigned integer of `width` bytes.
pub(crate) fn write_le(val: u64, width: usize, buf: &mut Vec<u8>) {
    for i in 0..width {
        buf.push((val >> (i * 8)) as u8);
    }
}

// ---------------------------------------------------------------------------
// RowCodec trait
// ---------------------------------------------------------------------------

/// Defines how rows are encoded into / decoded from the table format.
pub trait RowCodec {
    /// Owned row type for building.
    type Row;
    /// Borrowed row type returned by the parser.
    type RowRef<'a>;

    /// Collect refs and deps contributed by this row.
    /// Called by `TableBuilder::push_row` to auto-register hashes.
    fn collect(&self, row: &Self::Row, refs: &mut Vec<O256>, deps: &mut Vec<O256>);

    /// Compute the row schema given the final ref/dep counts.
    fn row_schema(&self, num_refs: usize, num_deps: usize) -> RowSchema;

    /// Encode a typed row into raw field byte vectors.
    fn encode(
        &self,
        row: &Self::Row,
        sorted_refs: &[O256],
        sorted_deps: &[O256],
        ref_w: u8,
        dep_w: u8,
    ) -> Vec<Vec<u8>>;

    /// Decode raw field slices into a typed row.
    fn decode<'a>(
        &self,
        fields: Vec<&'a [u8]>,
        refs: &[O256],
        deps: &[O256],
    ) -> Result<Self::RowRef<'a>, TableError>;

    /// Called before serialization to prepare rows (e.g., sort, validate).
    fn prepare(&self, _rows: &mut [Self::Row]) {}
}

// ---------------------------------------------------------------------------
// RowSchema
// ---------------------------------------------------------------------------

/// A row schema — wraps a `Vec<FieldSpec>` describing column layout.
///
/// Also implements [`RowCodec`] for dynamic (untyped) row access where the
/// caller manages raw byte fields manually.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RowSchema(Vec<FieldSpec>);

impl RowSchema {
    pub fn new(field_specs: Vec<FieldSpec>) -> Self {
        Self(field_specs)
    }

    pub fn fields(&self) -> &[FieldSpec] {
        &self.0
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
}

impl RowCodec for RowSchema {
    type Row = Vec<Vec<u8>>;
    type RowRef<'a> = Vec<&'a [u8]>;

    fn collect(&self, _row: &Self::Row, _refs: &mut Vec<O256>, _deps: &mut Vec<O256>) {
        // No-op: caller manages refs/deps manually.
    }

    fn row_schema(&self, _num_refs: usize, _num_deps: usize) -> RowSchema {
        self.clone()
    }

    fn encode(
        &self,
        row: &Self::Row,
        _sorted_refs: &[O256],
        _sorted_deps: &[O256],
        _ref_w: u8,
        _dep_w: u8,
    ) -> Vec<Vec<u8>> {
        row.clone()
    }

    fn decode<'a>(
        &self,
        fields: Vec<&'a [u8]>,
        _refs: &[O256],
        _deps: &[O256],
    ) -> Result<Self::RowRef<'a>, TableError> {
        Ok(fields)
    }
}

// ---------------------------------------------------------------------------
// TableBuilder
// ---------------------------------------------------------------------------

/// Builds a table blob from refs, deps, a row codec, and row data.
///
/// # Example
///
/// ```
/// use covalence_hash::O256;
/// use covalence_object::{TableBuilder, RowSchema, FieldSpec};
///
/// let mut builder = TableBuilder::new(RowSchema::new(
///     vec![FieldSpec::blob(), FieldSpec::ref_index(1), FieldSpec::dep_index(1)],
/// ));
/// builder.push_ref(O256::blob("blob_mode"));
/// builder.push_dep(O256::blob("child_hash"));
/// builder.push_raw(&[b"hello.txt" as &[u8], &[0x00], &[0x00]]);
/// let table = builder.build();
/// assert!(!table.as_bytes().is_empty());
/// ```
pub struct TableBuilder<S: RowCodec> {
    schema: S,
    refs: Vec<O256>,
    deps: Vec<O256>,
    rows: Vec<S::Row>,
}

impl<S: RowCodec> TableBuilder<S> {
    /// Create a new builder with the given schema.
    pub fn new(schema: S) -> Self {
        Self {
            schema,
            refs: Vec::new(),
            deps: Vec::new(),
            rows: Vec::new(),
        }
    }

    /// Manually add a ref hash.
    pub fn push_ref(&mut self, r: O256) {
        self.refs.push(r);
    }

    /// Manually add a dep hash.
    pub fn push_dep(&mut self, d: O256) {
        self.deps.push(d);
    }

    /// Add a row. The schema's `collect` method is called to auto-register
    /// any refs/deps the row contributes.
    pub fn push_row(&mut self, row: S::Row) {
        self.schema.collect(&row, &mut self.refs, &mut self.deps);
        self.rows.push(row);
    }

    /// Serialize the table into a [`Table`].
    ///
    /// Calls the schema's [`RowCodec::prepare`] hook before encoding, then
    /// wraps the serialized blob, sorted refs/deps, and parsed header.
    pub fn build(mut self) -> Table<S> {
        self.schema.prepare(&mut self.rows);

        let Self {
            schema,
            refs,
            deps,
            rows,
        } = self;

        // Dedup and sort refs/deps for canonical order.
        let mut sorted_refs = refs;
        sorted_refs.sort();
        sorted_refs.dedup();
        let mut sorted_deps = deps;
        sorted_deps.sort();
        sorted_deps.dedup();

        let ref_w = min_bytes(sorted_refs.len());
        let dep_w = min_bytes(sorted_deps.len());
        let row_schema = schema.row_schema(sorted_refs.len(), sorted_deps.len());
        let field_specs = row_schema.fields();

        // Encode all rows via the schema.
        let encoded: Vec<Vec<Vec<u8>>> = rows
            .iter()
            .map(|row| schema.encode(row, &sorted_refs, &sorted_deps, ref_w, dep_w))
            .collect();

        // Serialize encoded rows into (data_bytes, offsets).
        let (row_data, offsets) = serialize_rows_raw(&encoded, field_specs);
        let data_size = row_data.len() as u64;

        // Compute segment layout.
        let ref_end = sorted_refs.len() * 32;
        let dep_end = ref_end + sorted_deps.len() * 32;
        let ot_w = min_pow2_bytes(data_size) as usize;
        let ot_end = dep_end + offsets.len() * ot_w;
        let data_end = ot_end + row_data.len();

        // Build meta header.
        let mut mh = Vec::new();
        mh.push(0); // placeholder for mh_size

        mh.push(0x20);
        leb128::encode_u64(ref_end as u64, &mut mh);

        mh.push(0x20);
        leb128::encode_u64(dep_end as u64, &mut mh);

        mh.push(ot_w as u8);
        leb128::encode_u64(ot_end as u64, &mut mh);

        mh.push(0xFF);
        leb128::encode_u64(data_end as u64, &mut mh);

        let schema_bytes = field_specs.len() * 2;
        mh.push(0x00);
        leb128::encode_u64(schema_bytes as u64, &mut mh);
        for field in field_specs {
            mh.push(field.repr);
            mh.push(field.field_type as u8);
        }

        let mh_size = (mh.len() + 31) & !31;
        mh[0] = mh_size as u8;
        mh.resize(mh_size, 0);

        // Assemble full blob.
        let mut blob = mh;
        for r in &sorted_refs {
            blob.extend_from_slice(r.as_bytes());
        }
        for d in &sorted_deps {
            blob.extend_from_slice(d.as_bytes());
        }
        for &off in &offsets {
            write_le(off as u64, ot_w, &mut blob);
        }
        blob.extend_from_slice(&row_data);

        let header = parse_header(&blob).expect("freshly built blob must be valid");
        Table {
            blob,
            codec: schema,
            header,
            refs: sorted_refs,
            deps: sorted_deps,
        }
    }
}

/// Convenience methods for `RowSchema` builders.
impl TableBuilder<RowSchema> {
    /// Create a dynamic builder with pre-populated refs, deps, and field specs.
    pub fn dynamic(refs: Vec<O256>, deps: Vec<O256>, field_specs: Vec<FieldSpec>) -> Self {
        Self {
            schema: RowSchema::new(field_specs),
            refs,
            deps,
            rows: Vec::new(),
        }
    }

    /// Push a row from raw byte slices (convenience for dynamic schemas).
    pub fn push_raw(&mut self, fields: &[&[u8]]) {
        let row: Vec<Vec<u8>> = fields.iter().map(|f| f.to_vec()).collect();
        self.push_row(row);
    }
}

/// Serialize pre-encoded rows into (data_bytes, offsets).
fn serialize_rows_raw(rows: &[Vec<Vec<u8>>], field_specs: &[FieldSpec]) -> (Vec<u8>, Vec<usize>) {
    let mut data = Vec::new();
    let mut offsets = Vec::new();

    // Estimate data size for offset width.
    let est: usize = rows
        .iter()
        .map(|row| {
            row.iter()
                .zip(field_specs)
                .map(|(f, s)| {
                    if s.is_dynamic() {
                        f.len() + 8
                    } else {
                        s.fixed_width()
                    }
                })
                .sum::<usize>()
        })
        .sum();
    let ot_w = min_pow2_bytes(est as u64) as usize;

    let last_dynamic = field_specs.iter().rposition(|s| s.is_dynamic());

    for row in rows {
        offsets.push(data.len());
        for (i, (field_data, spec)) in row.iter().zip(field_specs).enumerate() {
            if spec.is_dynamic() {
                if Some(i) == last_dynamic {
                    data.extend_from_slice(field_data);
                } else {
                    write_le(field_data.len() as u64, ot_w, &mut data);
                    data.extend_from_slice(field_data);
                }
            } else {
                debug_assert_eq!(field_data.len(), spec.fixed_width());
                data.extend_from_slice(field_data);
            }
        }
    }

    (data, offsets)
}

// ---------------------------------------------------------------------------
// TableParser
// ---------------------------------------------------------------------------

/// Parsed meta header.
pub(crate) struct ParsedHeader {
    pub mh_size: usize,
    pub ref_end: usize,
    pub dep_end: usize,
    pub ot_end: usize,
    pub ot_w: usize,
    pub data_end: usize,
    pub schema: Vec<FieldSpec>,
}

/// Zero-copy parser for a table blob, parameterized by a [`RowCodec`].
///
/// ```
/// use covalence_hash::O256;
/// use covalence_object::{TableBuilder, TableParser, RowSchema, FieldSpec};
///
/// let schema = vec![FieldSpec::blob(), FieldSpec::ref_index(1), FieldSpec::dep_index(1)];
/// let mut builder = TableBuilder::dynamic(
///     vec![O256::blob("mode")],
///     vec![O256::blob("child")],
///     schema,
/// );
/// builder.push_raw(&[b"file.txt", &[0x00], &[0x00]]);
/// let table = builder.build();
///
/// let parser = TableParser::dynamic(table.as_bytes()).unwrap();
/// assert_eq!(parser.num_entries(), 1);
/// let row = parser.row(0).unwrap();
/// assert_eq!(row[0], b"file.txt");
/// ```
pub struct TableParser<'a, S: RowCodec> {
    data: &'a [u8],
    header: ParsedHeader,
    schema: S,
    refs: Vec<O256>,
    deps: Vec<O256>,
}

impl<'a, S: RowCodec> TableParser<'a, S> {
    /// Parse a table blob with the given schema.
    pub fn new(data: &'a [u8], schema: S) -> Result<Self, TableError> {
        let header = parse_header(data)?;
        let refs = read_hashes(data, header.mh_size, header.ref_end / 32);
        let deps = read_hashes(
            data,
            header.mh_size + header.ref_end,
            (header.dep_end - header.ref_end) / 32,
        );
        Ok(Self {
            data,
            header,
            schema,
            refs,
            deps,
        })
    }

    /// Number of refs.
    pub fn num_refs(&self) -> usize {
        self.refs.len()
    }

    /// Number of deps.
    pub fn num_deps(&self) -> usize {
        self.deps.len()
    }

    /// Number of entries (rows).
    pub fn num_entries(&self) -> usize {
        (self.header.ot_end - self.header.dep_end) / self.header.ot_w
    }

    /// The parsed field specs from the blob header.
    pub fn field_specs(&self) -> &[FieldSpec] {
        &self.header.schema
    }

    /// Get ref `i` as an O256.
    pub fn ref_hash(&self, i: usize) -> O256 {
        self.refs[i]
    }

    /// Get dep `i` as an O256.
    pub fn dep_hash(&self, i: usize) -> O256 {
        self.deps[i]
    }

    /// All refs.
    pub fn refs(&self) -> &[O256] {
        &self.refs
    }

    /// All deps.
    pub fn deps(&self) -> &[O256] {
        &self.deps
    }

    /// Parse row `i` into a typed row via the schema.
    pub fn row(&self, index: usize) -> Result<S::RowRef<'a>, TableError> {
        let fields = self.raw_row(index)?;
        self.schema.decode(fields, &self.refs, &self.deps)
    }

    /// Parse row `i` into raw field slices (schema-independent).
    pub fn raw_row(&self, index: usize) -> Result<Vec<&'a [u8]>, TableError> {
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

        let off_pos = ot_start + index * h.ot_w;
        let entry_start = read_le(&self.data[off_pos..], h.ot_w) as usize;
        let entry_end = if index + 1 < n {
            let next_pos = ot_start + (index + 1) * h.ot_w;
            read_le(&self.data[next_pos..], h.ot_w) as usize
        } else {
            data_size
        };

        let entry = &self.data[data_start + entry_start..data_start + entry_end];
        parse_entry(index, entry, &h.schema, h.ot_w)
    }
}

/// Convenience constructor for dynamic (untyped) parsing.
impl<'a> TableParser<'a, RowSchema> {
    /// Parse a blob with a dynamic schema (field specs read from the blob).
    pub fn dynamic(data: &'a [u8]) -> Result<Self, TableError> {
        let header = parse_header(data)?;
        let schema = RowSchema::new(header.schema.clone());
        let refs = read_hashes(data, header.mh_size, header.ref_end / 32);
        let deps = read_hashes(
            data,
            header.mh_size + header.ref_end,
            (header.dep_end - header.ref_end) / 32,
        );
        Ok(Self {
            data,
            header,
            schema,
            refs,
            deps,
        })
    }
}

// ---------------------------------------------------------------------------
// Table<R> — owned, parsed table
// ---------------------------------------------------------------------------

/// An owned, parsed table: the blob bytes plus pre-parsed header, refs, deps,
/// and the [`RowCodec`] used for typed row access.
pub struct Table<R> {
    blob: Vec<u8>,
    codec: R,
    header: ParsedHeader,
    refs: Vec<O256>,
    deps: Vec<O256>,
}

impl<R: RowCodec> Table<R> {
    /// Construct a `Table` from raw bytes and a codec.
    pub fn parse(blob: Vec<u8>, codec: R) -> Result<Self, TableError> {
        let header = parse_header(&blob)?;
        let refs = read_hashes(&blob, header.mh_size, header.ref_end / 32);
        let deps = read_hashes(
            &blob,
            header.mh_size + header.ref_end,
            (header.dep_end - header.ref_end) / 32,
        );
        Ok(Self {
            blob,
            codec,
            header,
            refs,
            deps,
        })
    }

    /// The raw table bytes.
    pub fn as_bytes(&self) -> &[u8] {
        &self.blob
    }

    /// Consume and return the raw table bytes.
    pub fn into_bytes(self) -> Vec<u8> {
        self.blob
    }

    /// Number of refs.
    pub fn num_refs(&self) -> usize {
        self.refs.len()
    }

    /// Number of deps.
    pub fn num_deps(&self) -> usize {
        self.deps.len()
    }

    /// Number of entries (rows).
    pub fn num_entries(&self) -> usize {
        (self.header.ot_end - self.header.dep_end) / self.header.ot_w
    }

    /// All refs.
    pub fn refs(&self) -> &[O256] {
        &self.refs
    }

    /// All deps.
    pub fn deps(&self) -> &[O256] {
        &self.deps
    }

    /// The parsed field specs from the blob header.
    pub fn field_specs(&self) -> &[FieldSpec] {
        &self.header.schema
    }

    /// Parse row `i` into a typed row via the codec.
    pub fn row(&self, index: usize) -> Result<R::RowRef<'_>, TableError> {
        let fields = self.raw_row(index)?;
        self.codec.decode(fields, &self.refs, &self.deps)
    }

    /// Parse row `i` into raw field slices.
    pub fn raw_row(&self, index: usize) -> Result<Vec<&[u8]>, TableError> {
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

        let off_pos = ot_start + index * h.ot_w;
        let entry_start = read_le(&self.blob[off_pos..], h.ot_w) as usize;
        let entry_end = if index + 1 < n {
            let next_pos = ot_start + (index + 1) * h.ot_w;
            read_le(&self.blob[next_pos..], h.ot_w) as usize
        } else {
            data_size
        };

        let entry = &self.blob[data_start + entry_start..data_start + entry_end];
        parse_entry(index, entry, &h.schema, h.ot_w)
    }

    /// Content-hash of the table blob.
    ///
    /// Uses BLAKE3 key derivation under `COV_ROOT` → `"covalence table (development)"`,
    /// then keyed-hashes the full blob.
    pub fn content_hash(&self) -> O256 {
        use covalence_hash::{COV_ROOT, HashCtx};
        let key = COV_ROOT.tag("covalence table (development)");
        key.tag(&self.blob)
    }
}

/// Convenience constructor for dynamic (untyped) tables.
impl Table<RowSchema> {
    /// Parse a blob with a dynamic schema (field specs read from the blob header).
    pub fn parse_dynamic(blob: Vec<u8>) -> Result<Self, TableError> {
        let header = parse_header(&blob)?;
        let schema = RowSchema::new(header.schema.clone());
        let refs = read_hashes(&blob, header.mh_size, header.ref_end / 32);
        let deps = read_hashes(
            &blob,
            header.mh_size + header.ref_end,
            (header.dep_end - header.ref_end) / 32,
        );
        Ok(Self {
            blob,
            codec: schema,
            header,
            refs,
            deps,
        })
    }
}

// ---------------------------------------------------------------------------
// Free functions for parsing
// ---------------------------------------------------------------------------

fn read_hashes(data: &[u8], offset: usize, count: usize) -> Vec<O256> {
    (0..count)
        .map(|i| {
            let start = offset + i * 32;
            let mut bytes = [0u8; 32];
            bytes.copy_from_slice(&data[start..start + 32]);
            O256::from_bytes(bytes)
        })
        .collect()
}

pub(crate) fn parse_header(data: &[u8]) -> Result<ParsedHeader, TableError> {
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
                leb128::decode_u64(&mh[*pos..]).map_err(|_| TableError::TruncatedVarint)?;
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
        leb128::decode_u64(&mh[pos..]).map_err(|_| TableError::TruncatedVarint)?;
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
        leb128::decode_u64(&mh[pos..]).map_err(|_| TableError::TruncatedVarint)?;
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
        leb128::decode_u64(&mh[pos..]).map_err(|_| TableError::TruncatedVarint)?;
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
    if ref_end % 32 != 0 {
        return Err(TableError::BadSegmentSize {
            size: ref_end,
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

/// Parse a single entry's bytes into field slices.
fn parse_entry<'a>(
    index: usize,
    entry: &'a [u8],
    schema: &[FieldSpec],
    ot_w: usize,
) -> Result<Vec<&'a [u8]>, TableError> {
    let last_dynamic = schema.iter().rposition(|s| s.is_dynamic());

    let mut fields = Vec::with_capacity(schema.len());
    let mut cursor = 0;

    for (i, spec) in schema.iter().enumerate() {
        if !spec.is_dynamic() {
            let w = spec.fixed_width();
            if cursor + w > entry.len() {
                return Err(TableError::EntryTooShort { index });
            }
            fields.push(&entry[cursor..cursor + w]);
            cursor += w;
        } else if Some(i) == last_dynamic {
            let trailing: usize = schema[i + 1..].iter().map(|s| s.fixed_width()).sum();
            let end = entry.len() - trailing;
            if cursor > end {
                return Err(TableError::EntryTooShort { index });
            }
            fields.push(&entry[cursor..end]);
            cursor = end;
        } else {
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
        let table = TableBuilder::dynamic(vec![], vec![], vec![]).build();
        assert_eq!(table.num_refs(), 0);
        assert_eq!(table.num_deps(), 0);
        assert_eq!(table.num_entries(), 0);
        assert!(table.field_specs().is_empty());
    }

    #[test]
    fn directory_roundtrip_dynamic() {
        let ref_blob = O256::blob("blob");
        let ref_dir = O256::blob("dir");
        let ref_exec = O256::blob("executable");
        let dep_hello = O256::blob("hello_content");
        let dep_run = O256::blob("run_content");
        let dep_src = O256::blob("src_content");

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

        let blob_idx = refs.iter().position(|r| *r == ref_blob).unwrap() as u8;
        let dir_idx = refs.iter().position(|r| *r == ref_dir).unwrap() as u8;
        let exec_idx = refs.iter().position(|r| *r == ref_exec).unwrap() as u8;
        let hello_idx = deps.iter().position(|d| *d == dep_hello).unwrap() as u8;
        let run_idx = deps.iter().position(|d| *d == dep_run).unwrap() as u8;
        let src_idx = deps.iter().position(|d| *d == dep_src).unwrap() as u8;

        let mut builder = TableBuilder::dynamic(refs.clone(), deps.clone(), schema.clone());
        builder.push_raw(&[b"hello.txt", &[blob_idx], &[hello_idx]]);
        builder.push_raw(&[b"run.sh", &[exec_idx], &[run_idx]]);
        builder.push_raw(&[b"src", &[dir_idx], &[src_idx]]);

        let table = builder.build();

        assert_eq!(table.num_refs(), 3);
        assert_eq!(table.num_deps(), 3);
        assert_eq!(table.num_entries(), 3);
        assert_eq!(table.field_specs(), &schema);
        assert_eq!(table.refs(), &refs);
        assert_eq!(table.deps(), &deps);

        let row0 = table.row(0).unwrap();
        assert_eq!(row0[0], b"hello.txt");
        assert_eq!(row0[1], &[blob_idx]);
        assert_eq!(row0[2], &[hello_idx]);

        let row1 = table.row(1).unwrap();
        assert_eq!(row1[0], b"run.sh");

        let row2 = table.row(2).unwrap();
        assert_eq!(row2[0], b"src");
    }

    #[test]
    fn meta_header_is_32_aligned() {
        let mut builder = TableBuilder::new(RowSchema::new(vec![FieldSpec::blob()]));
        builder.push_ref(O256::blob("r"));
        builder.push_dep(O256::blob("d"));
        let table = builder.build();
        assert_eq!(table.as_bytes()[0] % 32, 0);
    }

    #[test]
    fn refs_and_deps_sorted_and_deduped() {
        let r1 = O256::blob("zzz");
        let r2 = O256::blob("aaa");

        let mut builder = TableBuilder::dynamic(
            vec![r1, r2, r1], // r1 duplicated
            vec![O256::blob("d")],
            vec![FieldSpec::dep_index(1)],
        );
        builder.push_raw(&[&[0x00]]);
        let table = builder.build();

        assert_eq!(table.num_refs(), 2); // deduped
        let refs = table.refs();
        assert!(refs[0] <= refs[1]);
    }

    #[test]
    fn push_ref_and_dep() {
        let mut builder = TableBuilder::new(RowSchema::new(vec![FieldSpec::blob()]));
        builder.push_ref(O256::blob("r1"));
        builder.push_ref(O256::blob("r2"));
        builder.push_dep(O256::blob("d1"));
        builder.push_row(vec![b"hello".to_vec()]);
        let table = builder.build();

        assert_eq!(table.num_refs(), 2);
        assert_eq!(table.num_deps(), 1);
        assert_eq!(table.num_entries(), 1);
    }

    #[test]
    fn multi_blob_fields() {
        let mut builder = TableBuilder::dynamic(
            vec![O256::blob("prolly.leaf")],
            vec![],
            vec![FieldSpec::blob(), FieldSpec::blob()],
        );
        builder.push_raw(&[b"key1", b"value1"]);
        builder.push_raw(&[b"k2", b"a longer value here"]);
        let table = builder.build();

        assert_eq!(table.num_entries(), 2);

        let row0 = table.row(0).unwrap();
        assert_eq!(row0[0], b"key1");
        assert_eq!(row0[1], b"value1");

        let row1 = table.row(1).unwrap();
        assert_eq!(row1[0], b"k2");
        assert_eq!(row1[1], b"a longer value here");
    }

    #[test]
    fn row_out_of_range() {
        let table = TableBuilder::dynamic(vec![], vec![], vec![]).build();
        assert!(table.row(0).is_err());
    }

    #[test]
    fn table_parser_still_works() {
        let mut builder = TableBuilder::dynamic(
            vec![O256::blob("r")],
            vec![O256::blob("d")],
            vec![FieldSpec::blob()],
        );
        builder.push_raw(&[b"hello"]);
        let table = builder.build();

        let parser = TableParser::dynamic(table.as_bytes()).unwrap();
        assert_eq!(parser.num_entries(), 1);
        assert_eq!(parser.row(0).unwrap()[0], b"hello");
    }

    #[test]
    fn parse_dynamic_roundtrip() {
        let mut builder =
            TableBuilder::dynamic(vec![O256::blob("r")], vec![], vec![FieldSpec::blob()]);
        builder.push_raw(&[b"data"]);
        let original = builder.build();

        let reparsed = Table::parse_dynamic(original.as_bytes().to_vec()).unwrap();
        assert_eq!(reparsed.num_entries(), 1);
        assert_eq!(reparsed.row(0).unwrap()[0], b"data");
    }

    #[test]
    fn content_hash_deterministic() {
        let mut b1 = TableBuilder::dynamic(vec![], vec![], vec![FieldSpec::blob()]);
        b1.push_raw(&[b"hello"]);
        let t1 = b1.build();

        let mut b2 = TableBuilder::dynamic(vec![], vec![], vec![FieldSpec::blob()]);
        b2.push_raw(&[b"hello"]);
        let t2 = b2.build();

        assert_eq!(t1.content_hash(), t2.content_hash());
    }

    #[test]
    fn content_hash_differs() {
        let mut b1 = TableBuilder::dynamic(vec![], vec![], vec![FieldSpec::blob()]);
        b1.push_raw(&[b"hello"]);
        let t1 = b1.build();

        let mut b2 = TableBuilder::dynamic(vec![], vec![], vec![FieldSpec::blob()]);
        b2.push_raw(&[b"world"]);
        let t2 = b2.build();

        assert_ne!(t1.content_hash(), t2.content_hash());
    }
}
