use std::io::{self, Write};

use crate::{Clause, DratProof, DratStep, Lit};

use super::ParseError;

/// Parse a text-format DRAT proof.
///
/// Each line is a clause: space-separated literal integers terminated by `0`.
/// Lines prefixed with `d` are deletion steps; lines prefixed with `a` or
/// unprefixed are addition steps. Lines starting with `c` are comments.
pub fn parse_drat_text(input: &str) -> Result<DratProof, ParseError> {
    let mut steps = Vec::new();

    for (line_idx, line) in input.lines().enumerate() {
        let line_num = line_idx + 1;
        let trimmed = line.trim();

        if trimmed.is_empty() || trimmed.starts_with('c') {
            continue;
        }

        let (is_delete, rest) = if let Some(after) = trimmed.strip_prefix('d') {
            (true, after.trim_start())
        } else if let Some(after) = trimmed.strip_prefix('a') {
            (false, after.trim_start())
        } else {
            (false, trimmed)
        };

        let mut lits = Vec::new();
        for token in rest.split_whitespace() {
            let val: i32 = token.parse().map_err(|_| ParseError::ExpectedInteger {
                line: line_num,
                token: token.to_string(),
            })?;

            if val == 0 {
                break;
            }

            let lit = Lit::from_dimacs(val).ok_or_else(|| ParseError::InvalidLiteral {
                line: line_num,
                message: "literal value is zero".to_string(),
            })?;
            lits.push(lit);
        }

        let clause = Clause::new(lits);
        if is_delete {
            steps.push(DratStep::Delete(clause));
        } else {
            steps.push(DratStep::Add(clause));
        }
    }

    Ok(DratProof::new(steps))
}

/// Encode a literal as a binary DRAT varint.
///
/// Standard binary DRAT format: `(var << 1) | sign` where sign=1 means negative.
/// Each byte: 7 data bits in the low bits, MSB is continuation flag.
fn encode_lit_varint(lit: Lit, out: &mut Vec<u8>) {
    let var = lit.var().index() as u32;
    let sign = if lit.is_neg() { 1u32 } else { 0u32 };
    let mut val = (var << 1) | sign;

    loop {
        let mut byte = (val & 0x7F) as u8;
        val >>= 7;
        if val != 0 {
            byte |= 0x80; // continuation bit
        }
        out.push(byte);
        if val == 0 {
            break;
        }
    }
}

/// Decode a varint from binary DRAT data, returning the decoded value and bytes consumed.
fn decode_varint(data: &[u8], offset: usize) -> Result<(u32, usize), ParseError> {
    let mut result: u32 = 0;
    let mut shift = 0u32;
    let mut pos = offset;

    loop {
        if pos >= data.len() {
            return Err(ParseError::UnexpectedEof);
        }
        let byte = data[pos];
        pos += 1;

        result |= ((byte & 0x7F) as u32) << shift;
        if byte & 0x80 == 0 {
            return Ok((result, pos));
        }
        shift += 7;
        if shift >= 32 {
            return Err(ParseError::InvalidBinaryEncoding { offset });
        }
    }
}

/// Parse a standard binary DRAT proof.
///
/// Binary format (drat-trim/CaDiCaL convention):
/// - `a` byte (0x61) for addition, `d` byte (0x64) for deletion
/// - Literals as varint: `(var << 1) | sign` where sign=1 means negative
/// - Each byte: 7 data bits + MSB continuation flag
/// - Clause terminated by `0x00`
pub fn parse_drat_binary(input: &[u8]) -> Result<DratProof, ParseError> {
    let mut steps = Vec::new();
    let mut pos = 0;

    while pos < input.len() {
        let is_delete = match input[pos] {
            b'a' => {
                pos += 1;
                false
            }
            b'd' => {
                pos += 1;
                true
            }
            _ => return Err(ParseError::InvalidBinaryEncoding { offset: pos }),
        };
        if pos >= input.len() {
            return Err(ParseError::UnexpectedEof);
        }

        let mut lits = Vec::new();

        loop {
            if pos >= input.len() {
                return Err(ParseError::UnexpectedEof);
            }

            // Check for clause terminator.
            if input[pos] == 0x00 {
                pos += 1;
                break;
            }

            let (val, new_pos) = decode_varint(input, pos)?;
            pos = new_pos;

            if val == 0 {
                break;
            }

            let var = (val >> 1) as i32;
            let sign = val & 1;
            if var == 0 {
                return Err(ParseError::InvalidBinaryEncoding { offset: pos });
            }
            let dimacs = if sign == 1 { -var } else { var };
            let lit = Lit::from_dimacs(dimacs)
                .ok_or(ParseError::InvalidBinaryEncoding { offset: pos })?;
            lits.push(lit);
        }

        let clause = Clause::new(lits);
        if is_delete {
            steps.push(DratStep::Delete(clause));
        } else {
            steps.push(DratStep::Add(clause));
        }
    }

    Ok(DratProof::new(steps))
}

/// Write a DRAT proof in text format.
pub fn write_drat_text(proof: &DratProof, writer: &mut dyn Write) -> io::Result<()> {
    for step in proof.steps() {
        match step {
            DratStep::Add(clause) => {
                for (i, lit) in clause.lits().iter().enumerate() {
                    if i > 0 {
                        write!(writer, " ")?;
                    }
                    write!(writer, "{}", lit.dimacs())?;
                }
                writeln!(writer, " 0")?;
            }
            DratStep::Delete(clause) => {
                write!(writer, "d ")?;
                for (i, lit) in clause.lits().iter().enumerate() {
                    if i > 0 {
                        write!(writer, " ")?;
                    }
                    write!(writer, "{}", lit.dimacs())?;
                }
                writeln!(writer, " 0")?;
            }
        }
    }
    Ok(())
}

/// Write a DRAT proof in text format, returning a [`String`].
pub fn write_drat_text_to_string(proof: &DratProof) -> String {
    let mut buf = Vec::new();
    write_drat_text(proof, &mut buf).expect("write to Vec never fails");
    String::from_utf8(buf).expect("DRAT text output is always ASCII")
}

/// Write a DRAT proof in standard binary format.
pub fn write_drat_binary(proof: &DratProof, writer: &mut dyn Write) -> io::Result<()> {
    let mut buf = Vec::new();
    for step in proof.steps() {
        match step {
            DratStep::Add(clause) => {
                buf.push(b'a');
                for lit in clause.lits() {
                    encode_lit_varint(*lit, &mut buf);
                }
                buf.push(0x00);
            }
            DratStep::Delete(clause) => {
                buf.push(b'd');
                for lit in clause.lits() {
                    encode_lit_varint(*lit, &mut buf);
                }
                buf.push(0x00);
            }
        }
    }
    writer.write_all(&buf)
}

/// Write a DRAT proof in standard binary format, returning a [`Vec<u8>`].
pub fn write_drat_binary_to_vec(proof: &DratProof) -> Vec<u8> {
    let mut buf = Vec::new();
    write_drat_binary(proof, &mut buf).expect("write to Vec never fails");
    buf
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn text_add_steps() {
        let input = "1 -2 0\n3 0\n";
        let proof = parse_drat_text(input).unwrap();
        assert_eq!(proof.len(), 2);
        assert!(matches!(&proof.steps()[0], DratStep::Add(c) if c.len() == 2));
        assert!(matches!(&proof.steps()[1], DratStep::Add(c) if c.len() == 1));
    }

    #[test]
    fn text_delete_steps() {
        let input = "d 1 -2 0\nd 3 0\n";
        let proof = parse_drat_text(input).unwrap();
        assert_eq!(proof.len(), 2);
        assert!(matches!(&proof.steps()[0], DratStep::Delete(_)));
        assert!(matches!(&proof.steps()[1], DratStep::Delete(_)));
    }

    #[test]
    fn text_mixed() {
        let input = "1 0\nd 1 0\n-2 0\n";
        let proof = parse_drat_text(input).unwrap();
        assert_eq!(proof.len(), 3);
        assert!(matches!(&proof.steps()[0], DratStep::Add(_)));
        assert!(matches!(&proof.steps()[1], DratStep::Delete(_)));
        assert!(matches!(&proof.steps()[2], DratStep::Add(_)));
    }

    #[test]
    fn text_a_prefix() {
        let input = "a 1 -2 0\n";
        let proof = parse_drat_text(input).unwrap();
        assert_eq!(proof.len(), 1);
        assert!(matches!(&proof.steps()[0], DratStep::Add(c) if c.len() == 2));
    }

    #[test]
    fn text_comments() {
        let input = "c this is a comment\n1 0\nc another\nd 1 0\n";
        let proof = parse_drat_text(input).unwrap();
        assert_eq!(proof.len(), 2);
    }

    #[test]
    fn text_empty_clause_add() {
        let input = "0\n";
        let proof = parse_drat_text(input).unwrap();
        assert_eq!(proof.len(), 1);
        assert!(matches!(&proof.steps()[0], DratStep::Add(c) if c.is_empty()));
    }

    #[test]
    fn text_roundtrip() {
        let input = "1 -2 0\nd 3 0\n0\n";
        let proof = parse_drat_text(input).unwrap();
        let output = write_drat_text_to_string(&proof);
        let proof2 = parse_drat_text(&output).unwrap();
        assert_eq!(proof, proof2);
    }

    #[test]
    fn binary_basic() {
        // Add clause {1, -2}: a, lit 1 = (1<<1)|0 = 2, lit -2 = (2<<1)|1 = 5
        let data: Vec<u8> = vec![b'a', 0x02, 0x05, 0x00];
        let proof = parse_drat_binary(&data).unwrap();
        assert_eq!(proof.len(), 1);
        let step = &proof.steps()[0];
        assert!(matches!(step, DratStep::Add(c) if c.len() == 2));
        if let DratStep::Add(c) = step {
            assert_eq!(c.lits()[0].dimacs(), 1);
            assert_eq!(c.lits()[1].dimacs(), -2);
        }
    }

    #[test]
    fn binary_delete() {
        // Delete clause {1}: d, (1<<1)|0 = 2, 0x00
        let data: Vec<u8> = vec![b'd', 0x02, 0x00];
        let proof = parse_drat_binary(&data).unwrap();
        assert_eq!(proof.len(), 1);
        assert!(matches!(&proof.steps()[0], DratStep::Delete(c) if c.len() == 1));
    }

    #[test]
    fn binary_multi_byte_varint() {
        // Variable 100, positive: (100 << 1) | 0 = 200
        // 200 = 0b11001000
        // varint: first byte = 200 & 0x7F = 0x48, set continuation: 0xC8
        // second byte = 200 >> 7 = 1, no continuation: 0x01
        let data: Vec<u8> = vec![b'a', 0xC8, 0x01, 0x00];
        let proof = parse_drat_binary(&data).unwrap();
        assert_eq!(proof.len(), 1);
        if let DratStep::Add(c) = &proof.steps()[0] {
            assert_eq!(c.lits()[0].dimacs(), 100);
        }
    }

    #[test]
    fn binary_empty_clause() {
        let data: Vec<u8> = vec![b'a', 0x00];
        let proof = parse_drat_binary(&data).unwrap();
        assert_eq!(proof.len(), 1);
        assert!(matches!(&proof.steps()[0], DratStep::Add(c) if c.is_empty()));
    }

    #[test]
    fn varint_encode_decode_edge_cases() {
        // Test single-byte values.
        for var in [1, 2, 63] {
            let lit = Lit::from_dimacs(var).unwrap();
            let mut buf = Vec::new();
            encode_lit_varint(lit, &mut buf);
            let (decoded, _) = decode_varint(&buf, 0).unwrap();
            let dec_var = (decoded >> 1) as i32;
            assert_eq!(dec_var, var);
        }

        // Test multi-byte values.
        for var in [64, 127, 128, 1000, 10000] {
            let lit = Lit::from_dimacs(var).unwrap();
            let mut buf = Vec::new();
            encode_lit_varint(lit, &mut buf);
            let (decoded, _) = decode_varint(&buf, 0).unwrap();
            let dec_var = (decoded >> 1) as i32;
            let dec_sign = decoded & 1;
            assert_eq!(dec_var, var);
            assert_eq!(dec_sign, 0);
        }

        // Test negative literal.
        let lit = Lit::from_dimacs(-42).unwrap();
        let mut buf = Vec::new();
        encode_lit_varint(lit, &mut buf);
        let (decoded, _) = decode_varint(&buf, 0).unwrap();
        let dec_var = (decoded >> 1) as i32;
        let dec_sign = decoded & 1;
        assert_eq!(dec_var, 42);
        assert_eq!(dec_sign, 1);
    }

    #[test]
    fn binary_roundtrip() {
        let text_input = "1 -2 0\nd 3 0\n0\n";
        let proof = parse_drat_text(text_input).unwrap();

        let binary = write_drat_binary_to_vec(&proof);
        let proof2 = parse_drat_binary(&binary).unwrap();
        assert_eq!(proof, proof2);
    }

    #[test]
    fn cross_format_roundtrip() {
        // text → binary → text
        let input = "1 -2 3 0\nd -1 2 0\n0\n";
        let proof1 = parse_drat_text(input).unwrap();

        let binary = write_drat_binary_to_vec(&proof1);
        let proof2 = parse_drat_binary(&binary).unwrap();
        assert_eq!(proof1, proof2);

        let text_out = write_drat_text_to_string(&proof2);
        let proof3 = parse_drat_text(&text_out).unwrap();
        assert_eq!(proof1, proof3);
    }
}
