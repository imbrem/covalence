//! Wrapper around the Apache Arrow Rust implementation.
//!
//! Re-exports [`arrow`] for callers; adds [`parse_ipc`] which accepts either
//! the IPC *file* format (with the `ARROW1` magic) or the IPC *stream* format
//! and returns an [`ArrowInfo`] summary suitable for printing in the REPL.

use std::fmt;
use std::io::Cursor;
use std::sync::Arc;

pub use arrow;
use arrow::datatypes::Schema;
use arrow::error::ArrowError as RawArrowError;
use arrow::ipc::reader::{FileReader, StreamReader};

/// Errors from Arrow IPC parsing.
#[derive(Debug, thiserror::Error)]
pub enum ArrowError {
    #[error("arrow error: {0}")]
    Arrow(#[from] RawArrowError),
    #[error("not an Arrow IPC payload: {0}")]
    Format(String),
}

/// Which Arrow IPC encoding was detected.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum IpcFormat {
    /// IPC file format (random-access, has `ARROW1` magic).
    File,
    /// IPC stream format (sequential).
    Stream,
}

impl fmt::Display for IpcFormat {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            IpcFormat::File => f.write_str("file"),
            IpcFormat::Stream => f.write_str("stream"),
        }
    }
}

/// Summary statistics for an Arrow IPC payload.
#[derive(Debug, Clone)]
pub struct ArrowInfo {
    pub format: IpcFormat,
    pub schema: Arc<Schema>,
    pub num_rows: usize,
    pub num_batches: usize,
}

impl fmt::Display for ArrowInfo {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(
            f,
            "arrow ({}): {} batches, {} rows, {} columns",
            self.format,
            self.num_batches,
            self.num_rows,
            self.schema.fields().len()
        )?;
        for field in self.schema.fields() {
            writeln!(f, "  {}: {}", field.name(), field.data_type())?;
        }
        Ok(())
    }
}

const ARROW_FILE_MAGIC: &[u8; 6] = b"ARROW1";

/// Parse an Arrow IPC payload, auto-detecting file vs. stream format.
pub fn parse_ipc(bytes: &[u8]) -> Result<ArrowInfo, ArrowError> {
    if bytes.starts_with(ARROW_FILE_MAGIC) {
        parse_file(bytes)
    } else {
        parse_stream(bytes)
    }
}

/// Parse an Arrow IPC *file* payload (random-access, `ARROW1` magic).
pub fn parse_file(bytes: &[u8]) -> Result<ArrowInfo, ArrowError> {
    let mut reader = FileReader::try_new(Cursor::new(bytes), None)?;
    let schema = reader.schema();
    let mut num_rows = 0;
    let mut num_batches = 0;
    for batch in &mut reader {
        let batch = batch?;
        num_rows += batch.num_rows();
        num_batches += 1;
    }
    Ok(ArrowInfo {
        format: IpcFormat::File,
        schema,
        num_rows,
        num_batches,
    })
}

/// Parse an Arrow IPC *stream* payload (sequential, no magic).
pub fn parse_stream(bytes: &[u8]) -> Result<ArrowInfo, ArrowError> {
    let mut reader = StreamReader::try_new(Cursor::new(bytes), None)
        .map_err(|e| ArrowError::Format(e.to_string()))?;
    let schema = reader.schema();
    let mut num_rows = 0;
    let mut num_batches = 0;
    for batch in &mut reader {
        let batch = batch?;
        num_rows += batch.num_rows();
        num_batches += 1;
    }
    Ok(ArrowInfo {
        format: IpcFormat::Stream,
        schema,
        num_rows,
        num_batches,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use arrow::array::{Int32Array, StringArray};
    use arrow::datatypes::{DataType, Field};
    use arrow::ipc::writer::{FileWriter, StreamWriter};
    use arrow::record_batch::RecordBatch;

    fn sample_batch() -> RecordBatch {
        let schema = Arc::new(Schema::new(vec![
            Field::new("id", DataType::Int32, false),
            Field::new("name", DataType::Utf8, true),
        ]));
        let id = Int32Array::from(vec![1, 2, 3]);
        let name = StringArray::from(vec![Some("a"), Some("b"), None]);
        RecordBatch::try_new(schema, vec![Arc::new(id), Arc::new(name)]).unwrap()
    }

    #[test]
    fn parses_file_format() {
        let batch = sample_batch();
        let mut buf = Vec::new();
        {
            let mut w = FileWriter::try_new(&mut buf, &batch.schema()).unwrap();
            w.write(&batch).unwrap();
            w.finish().unwrap();
        }

        let info = parse_ipc(&buf).unwrap();
        assert_eq!(info.format, IpcFormat::File);
        assert_eq!(info.num_batches, 1);
        assert_eq!(info.num_rows, 3);
        assert_eq!(info.schema.fields().len(), 2);
    }

    #[test]
    fn parses_stream_format() {
        let batch = sample_batch();
        let mut buf = Vec::new();
        {
            let mut w = StreamWriter::try_new(&mut buf, &batch.schema()).unwrap();
            w.write(&batch).unwrap();
            w.finish().unwrap();
        }

        let info = parse_ipc(&buf).unwrap();
        assert_eq!(info.format, IpcFormat::Stream);
        assert_eq!(info.num_batches, 1);
        assert_eq!(info.num_rows, 3);
    }

    #[test]
    fn rejects_garbage() {
        let err = parse_ipc(b"not an arrow payload at all").unwrap_err();
        // stream reader returns an error because the bytes aren't a valid IPC message.
        assert!(matches!(err, ArrowError::Format(_) | ArrowError::Arrow(_)));
    }
}
