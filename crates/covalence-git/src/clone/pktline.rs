//! Git pkt-line format codec.
//!
//! The pkt-line format prefixes each data line with a 4-byte hex length
//! (including the 4 length bytes themselves). Special length values:
//! - `0000` — flush packet
//! - `0001` — delimiter packet
//! - `0002` — response-end packet

use std::io::{self, BufRead, Write};

/// A single pkt-line packet.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PktLine {
    /// Data payload (without the 4-byte length prefix).
    Data(Vec<u8>),
    /// Flush packet (`0000`).
    Flush,
    /// Delimiter packet (`0001`).
    Delim,
    /// Response-end packet (`0002`).
    ResponseEnd,
}

/// Read a single pkt-line from a buffered reader.
///
/// Returns `Ok(None)` on EOF (no bytes available).
pub fn read_pkt_line(r: &mut impl BufRead) -> io::Result<Option<PktLine>> {
    let mut hex = [0u8; 4];
    match r.read_exact(&mut hex) {
        Ok(()) => {}
        Err(e) if e.kind() == io::ErrorKind::UnexpectedEof => return Ok(None),
        Err(e) => return Err(e),
    }

    let len = u16::from_str_radix(std::str::from_utf8(&hex).map_err(invalid)?, 16)
        .map_err(|e| invalid(e))?;

    match len {
        0 => Ok(Some(PktLine::Flush)),
        1 => Ok(Some(PktLine::Delim)),
        2 => Ok(Some(PktLine::ResponseEnd)),
        n if n < 4 => Err(invalid("pkt-line length < 4 but not a special value")),
        n => {
            let data_len = (n - 4) as usize;
            let mut buf = vec![0u8; data_len];
            r.read_exact(&mut buf)?;
            Ok(Some(PktLine::Data(buf)))
        }
    }
}

/// Read all pkt-lines until a flush packet (or EOF).
///
/// The flush packet itself is consumed but not included in the result.
pub fn read_until_flush(r: &mut impl BufRead) -> io::Result<Vec<PktLine>> {
    let mut lines = Vec::new();
    loop {
        match read_pkt_line(r)? {
            None | Some(PktLine::Flush) => return Ok(lines),
            Some(pkt) => lines.push(pkt),
        }
    }
}

/// Write a data pkt-line.
pub fn write_pkt_line(w: &mut impl Write, data: &[u8]) -> io::Result<()> {
    let len = data.len() + 4;
    assert!(len <= 65535, "pkt-line data too large");
    write!(w, "{len:04x}")?;
    w.write_all(data)?;
    Ok(())
}

/// Write a flush packet (`0000`).
pub fn write_flush(w: &mut impl Write) -> io::Result<()> {
    w.write_all(b"0000")
}

/// Write a delimiter packet (`0001`).
pub fn write_delim(w: &mut impl Write) -> io::Result<()> {
    w.write_all(b"0001")
}

fn invalid(e: impl std::fmt::Display) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, e.to_string())
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::BufReader;

    #[test]
    fn round_trip_data() {
        let mut buf = Vec::new();
        write_pkt_line(&mut buf, b"hello\n").unwrap();
        assert_eq!(&buf, b"000ahello\n");

        let mut reader = BufReader::new(&buf[..]);
        let pkt = read_pkt_line(&mut reader).unwrap().unwrap();
        assert_eq!(pkt, PktLine::Data(b"hello\n".to_vec()));
    }

    #[test]
    fn round_trip_flush() {
        let mut buf = Vec::new();
        write_flush(&mut buf).unwrap();
        assert_eq!(&buf, b"0000");

        let mut reader = BufReader::new(&buf[..]);
        let pkt = read_pkt_line(&mut reader).unwrap().unwrap();
        assert_eq!(pkt, PktLine::Flush);
    }

    #[test]
    fn round_trip_delim() {
        let mut buf = Vec::new();
        write_delim(&mut buf).unwrap();
        assert_eq!(&buf, b"0001");

        let mut reader = BufReader::new(&buf[..]);
        let pkt = read_pkt_line(&mut reader).unwrap().unwrap();
        assert_eq!(pkt, PktLine::Delim);
    }

    #[test]
    fn read_multiple_lines() {
        let mut buf = Vec::new();
        write_pkt_line(&mut buf, b"line one\n").unwrap();
        write_pkt_line(&mut buf, b"line two\n").unwrap();
        write_flush(&mut buf).unwrap();
        write_pkt_line(&mut buf, b"after flush\n").unwrap();

        let mut reader = BufReader::new(&buf[..]);
        let lines = read_until_flush(&mut reader).unwrap();
        assert_eq!(lines.len(), 2);
        assert_eq!(lines[0], PktLine::Data(b"line one\n".to_vec()));
        assert_eq!(lines[1], PktLine::Data(b"line two\n".to_vec()));

        // Next read picks up the line after flush.
        let pkt = read_pkt_line(&mut reader).unwrap().unwrap();
        assert_eq!(pkt, PktLine::Data(b"after flush\n".to_vec()));
    }

    #[test]
    fn eof_returns_none() {
        let buf: &[u8] = &[];
        let mut reader = BufReader::new(buf);
        assert!(read_pkt_line(&mut reader).unwrap().is_none());
    }

    #[test]
    fn minimal_data_packet() {
        // Length 0004 = 4 bytes total, 0 data bytes.
        let buf = b"0004";
        let mut reader = BufReader::new(&buf[..]);
        let pkt = read_pkt_line(&mut reader).unwrap().unwrap();
        assert_eq!(pkt, PktLine::Data(vec![]));
    }
}
