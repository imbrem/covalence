use std::io::Read;

use pyo3::prelude::*;

/// Detected compression format.
pub enum Compression {
    Gzip,
    Bzip2,
    Zstd,
    None,
}

/// Detect compression from file extension.
pub fn detect_compression(path: &str) -> Compression {
    if path.ends_with(".gz") {
        Compression::Gzip
    } else if path.ends_with(".bz2") {
        Compression::Bzip2
    } else if path.ends_with(".zst") || path.ends_with(".zstd") {
        Compression::Zstd
    } else {
        Compression::None
    }
}

/// Decompress data according to the given compression format.
pub fn decompress(data: &[u8], compression: &Compression) -> std::io::Result<Vec<u8>> {
    fn read_all<R: Read>(mut reader: R) -> std::io::Result<Vec<u8>> {
        let mut out = Vec::new();
        reader.read_to_end(&mut out)?;
        Ok(out)
    }

    match compression {
        Compression::Gzip => read_all(flate2::read::GzDecoder::new(data)),
        Compression::Bzip2 => read_all(bzip2::read::BzDecoder::new(data)),
        Compression::Zstd => read_all(zstd::Decoder::new(data)?),
        Compression::None => Ok(data.to_vec()),
    }
}

/// Read a file, auto-decompressing based on extension.
pub fn read_file(path: &str) -> std::io::Result<Vec<u8>> {
    let data = std::fs::read(path)?;
    let compression = detect_compression(path);
    decompress(&data, &compression)
}

/// Read a file and auto-decompress based on extension.
#[pyfunction]
pub fn read_compressed(path: &str) -> PyResult<Vec<u8>> {
    read_file(path).map_err(|e| pyo3::exceptions::PyIOError::new_err(e.to_string()))
}
