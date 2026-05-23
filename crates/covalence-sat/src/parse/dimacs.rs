use std::io::{self, Write};

use crate::{Clause, Cnf, Lit};

use super::ParseError;

/// Parse a DIMACS CNF text file into a [`Cnf`].
///
/// Accepts the standard format: `c` comment lines, a `p cnf <vars> <clauses>`
/// header, and clause lines with space-separated literals terminated by `0`.
/// A trailing clause without a final `0` is accepted.
pub fn parse_dimacs(input: &str) -> Result<Cnf, ParseError> {
    let mut num_vars: Option<u32> = None;
    let mut declared_clauses: Option<usize> = None;
    let mut clauses: Vec<Clause> = Vec::new();
    let mut current_lits: Vec<Lit> = Vec::new();

    for (line_idx, line) in input.lines().enumerate() {
        let line_num = line_idx + 1;
        let trimmed = line.trim();

        // Skip blank lines and comments.
        if trimmed.is_empty() || trimmed.starts_with('c') {
            continue;
        }

        // Parse header.
        if trimmed.starts_with('p') {
            let parts: Vec<&str> = trimmed.split_whitespace().collect();
            if parts.len() != 4 || parts[1] != "cnf" {
                return Err(ParseError::InvalidHeader {
                    line: line_num,
                    message: format!("expected `p cnf <vars> <clauses>`, got `{trimmed}`"),
                });
            }
            num_vars = Some(
                parts[2]
                    .parse::<u32>()
                    .map_err(|_| ParseError::InvalidHeader {
                        line: line_num,
                        message: format!("invalid variable count `{}`", parts[2]),
                    })?,
            );
            declared_clauses =
                Some(
                    parts[3]
                        .parse::<usize>()
                        .map_err(|_| ParseError::InvalidHeader {
                            line: line_num,
                            message: format!("invalid clause count `{}`", parts[3]),
                        })?,
                );
            continue;
        }

        // Must have seen header by now.
        if num_vars.is_none() {
            return Err(ParseError::MissingHeader);
        }

        // Parse clause tokens.
        for token in trimmed.split_whitespace() {
            let val: i32 = token.parse().map_err(|_| ParseError::ExpectedInteger {
                line: line_num,
                token: token.to_string(),
            })?;

            if val == 0 {
                clauses.push(Clause::new(current_lits.drain(..)));
            } else {
                let lit = Lit::from_dimacs(val).ok_or_else(|| ParseError::InvalidLiteral {
                    line: line_num,
                    message: "literal value is zero".to_string(),
                })?;
                current_lits.push(lit);
            }
        }
    }

    // Accept trailing clause without final 0.
    if !current_lits.is_empty() {
        clauses.push(Clause::new(current_lits));
    }

    let nv = num_vars.ok_or(ParseError::MissingHeader)?;

    if let Some(declared) = declared_clauses {
        if declared != clauses.len() {
            return Err(ParseError::ClauseCountMismatch {
                declared,
                actual: clauses.len(),
            });
        }
    }

    Ok(Cnf::from_parts(nv, clauses))
}

/// Write a [`Cnf`] in DIMACS CNF format.
pub fn write_dimacs(cnf: &Cnf, writer: &mut dyn Write) -> io::Result<()> {
    writeln!(writer, "p cnf {} {}", cnf.num_vars(), cnf.num_clauses())?;
    for clause in cnf.clauses() {
        for (i, lit) in clause.lits().iter().enumerate() {
            if i > 0 {
                write!(writer, " ")?;
            }
            write!(writer, "{}", lit.dimacs())?;
        }
        writeln!(writer, " 0")?;
    }
    Ok(())
}

/// Write a [`Cnf`] in DIMACS CNF format, returning a [`String`].
pub fn write_dimacs_to_string(cnf: &Cnf) -> String {
    let mut buf = Vec::new();
    write_dimacs(cnf, &mut buf).expect("write to Vec never fails");
    String::from_utf8(buf).expect("DIMACS output is always ASCII")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn basic_parse() {
        let input = "p cnf 2 2\n1 -2 0\n-1 2 0\n";
        let cnf = parse_dimacs(input).unwrap();
        assert_eq!(cnf.num_vars(), 2);
        assert_eq!(cnf.num_clauses(), 2);
        assert_eq!(cnf.clauses().next().unwrap().len(), 2);
    }

    #[test]
    fn comments_and_blanks() {
        let input = "\
c This is a comment
c Another comment

p cnf 1 1

c Inline comment
1 0
";
        let cnf = parse_dimacs(input).unwrap();
        assert_eq!(cnf.num_vars(), 1);
        assert_eq!(cnf.num_clauses(), 1);
    }

    #[test]
    fn multiple_clauses_per_line() {
        let input = "p cnf 2 2\n1 -2 0 -1 2 0\n";
        let cnf = parse_dimacs(input).unwrap();
        assert_eq!(cnf.num_clauses(), 2);
    }

    #[test]
    fn empty_clause() {
        let input = "p cnf 0 1\n0\n";
        let cnf = parse_dimacs(input).unwrap();
        assert_eq!(cnf.num_clauses(), 1);
        assert!(cnf.clauses().next().unwrap().is_empty());
    }

    #[test]
    fn large_vars() {
        let input = "p cnf 1000 1\n999 -1000 0\n";
        let cnf = parse_dimacs(input).unwrap();
        assert_eq!(cnf.num_vars(), 1000);
        let clause = cnf.clauses().next().unwrap();
        assert_eq!(clause.lits()[0].dimacs(), 999);
        assert_eq!(clause.lits()[1].dimacs(), -1000);
    }

    #[test]
    fn missing_header_error() {
        let input = "1 -2 0\n";
        let err = parse_dimacs(input).unwrap_err();
        assert!(matches!(err, ParseError::MissingHeader));
    }

    #[test]
    fn bad_header() {
        let input = "p sat 2 2\n1 0\n-1 0\n";
        let err = parse_dimacs(input).unwrap_err();
        assert!(matches!(err, ParseError::InvalidHeader { .. }));
    }

    #[test]
    fn clause_count_mismatch() {
        let input = "p cnf 2 3\n1 -2 0\n-1 2 0\n";
        let err = parse_dimacs(input).unwrap_err();
        assert!(matches!(
            err,
            ParseError::ClauseCountMismatch {
                declared: 3,
                actual: 2
            }
        ));
    }

    #[test]
    fn non_integer_token() {
        let input = "p cnf 2 1\n1 abc 0\n";
        let err = parse_dimacs(input).unwrap_err();
        assert!(matches!(err, ParseError::ExpectedInteger { .. }));
    }

    #[test]
    fn trailing_clause_accepted() {
        let input = "p cnf 2 1\n1 -2\n";
        let cnf = parse_dimacs(input).unwrap();
        assert_eq!(cnf.num_clauses(), 1);
        assert_eq!(cnf.clauses().next().unwrap().len(), 2);
    }

    #[test]
    fn roundtrip() {
        let input = "p cnf 3 2\n1 -2 3 0\n-1 2 0\n";
        let cnf = parse_dimacs(input).unwrap();
        let output = write_dimacs_to_string(&cnf);
        let cnf2 = parse_dimacs(&output).unwrap();
        assert_eq!(cnf, cnf2);
    }

    #[test]
    fn writer_format() {
        let mut cnf = Cnf::new();
        let x = cnf.fresh();
        let y = cnf.fresh();
        cnf.clause([x, !y]);
        cnf.clause([!x]);

        let output = write_dimacs_to_string(&cnf);
        assert_eq!(output, "p cnf 2 2\n1 -2 0\n-1 0\n");
    }
}
