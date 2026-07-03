use crate::lrat::{LratProof, LratStep};
use crate::{Clause, Lit};

use super::ParseError;

/// Parse a text-format LRAT proof.
///
/// Each line has the form:
/// - Addition: `<id> <lit>... 0 <antecedent_id>... 0`
/// - Deletion: `<id> d <clause_id>... 0`
/// - Comments (lines starting with `c`) and blank lines are skipped.
pub fn parse_lrat_text(input: &str) -> Result<LratProof, ParseError> {
    let mut steps = Vec::new();

    for (line_idx, line) in input.lines().enumerate() {
        let line_num = line_idx + 1;
        let trimmed = line.trim();

        if trimmed.is_empty() || trimmed.starts_with('c') {
            continue;
        }

        let mut tokens = trimmed.split_whitespace();

        // First token: step ID.
        let id_token = tokens.next().ok_or(ParseError::UnexpectedEof)?;
        let id: u64 = id_token.parse().map_err(|_| ParseError::ExpectedInteger {
            line: line_num,
            token: id_token.to_string(),
        })?;

        // Second token: either 'd' (deletion) or first literal/0.
        let second = tokens.next().ok_or(ParseError::UnexpectedEof)?;

        if second == "d" {
            // Deletion step: parse clause IDs until 0.
            let mut clause_ids = Vec::new();
            for token in tokens {
                let val: u64 = token.parse().map_err(|_| ParseError::ExpectedInteger {
                    line: line_num,
                    token: token.to_string(),
                })?;
                if val == 0 {
                    break;
                }
                clause_ids.push(val);
            }
            steps.push(LratStep::Delete { id, clause_ids });
        } else {
            // Addition step: parse literals until 0, then antecedents until 0.
            let mut lits = Vec::new();

            // The second token is the first literal (or 0).
            let first_val: i32 = second.parse().map_err(|_| ParseError::ExpectedInteger {
                line: line_num,
                token: second.to_string(),
            })?;

            if first_val != 0 {
                let lit =
                    Lit::from_dimacs(first_val).ok_or_else(|| ParseError::InvalidLiteral {
                        line: line_num,
                        message: "literal value is zero".to_string(),
                    })?;
                lits.push(lit);

                // Continue parsing literals until 0.
                for token in tokens.by_ref() {
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
            }

            // Parse antecedent clause IDs until 0.
            let mut antecedents = Vec::new();
            for token in tokens {
                let val: u64 = token.parse().map_err(|_| ParseError::ExpectedInteger {
                    line: line_num,
                    token: token.to_string(),
                })?;
                if val == 0 {
                    break;
                }
                antecedents.push(val);
            }

            let clause = Clause::new(lits);
            steps.push(LratStep::Add {
                id,
                clause,
                antecedents,
            });
        }
    }

    Ok(LratProof::new(steps))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_addition_step() {
        let input = "3 0 1 2 0\n";
        let proof = parse_lrat_text(input).unwrap();
        assert_eq!(proof.len(), 1);
        match &proof.steps()[0] {
            LratStep::Add {
                id,
                clause,
                antecedents,
            } => {
                assert_eq!(*id, 3);
                assert!(clause.is_empty());
                assert_eq!(antecedents, &[1, 2]);
            }
            _ => panic!("expected Add step"),
        }
    }

    #[test]
    fn parse_deletion_step() {
        let input = "8 d 1 2 0\n";
        let proof = parse_lrat_text(input).unwrap();
        assert_eq!(proof.len(), 1);
        match &proof.steps()[0] {
            LratStep::Delete { id, clause_ids } => {
                assert_eq!(*id, 8);
                assert_eq!(clause_ids, &[1, 2]);
            }
            _ => panic!("expected Delete step"),
        }
    }

    #[test]
    fn parse_mixed() {
        let input = "5 -2 0 3 4 0\n6 1 0 5 1 0\n6 d 3 4 0\n7 0 6 5 2 0\n";
        let proof = parse_lrat_text(input).unwrap();
        assert_eq!(proof.len(), 4);
        assert!(matches!(&proof.steps()[0], LratStep::Add { id: 5, .. }));
        assert!(matches!(&proof.steps()[1], LratStep::Add { id: 6, .. }));
        assert!(matches!(&proof.steps()[2], LratStep::Delete { id: 6, .. }));
        assert!(matches!(&proof.steps()[3], LratStep::Add { id: 7, .. }));
    }

    #[test]
    fn parse_comments_and_blanks() {
        let input = "c comment\n\n3 0 1 2 0\nc another\n";
        let proof = parse_lrat_text(input).unwrap();
        assert_eq!(proof.len(), 1);
    }

    #[test]
    fn parse_empty_deletion() {
        let input = "4 d 0\n";
        let proof = parse_lrat_text(input).unwrap();
        assert_eq!(proof.len(), 1);
        match &proof.steps()[0] {
            LratStep::Delete { id, clause_ids } => {
                assert_eq!(*id, 4);
                assert!(clause_ids.is_empty());
            }
            _ => panic!("expected Delete step"),
        }
    }

    #[test]
    fn parse_clause_with_literals() {
        let input = "5 -2 3 0 1 4 0\n";
        let proof = parse_lrat_text(input).unwrap();
        match &proof.steps()[0] {
            LratStep::Add {
                id,
                clause,
                antecedents,
            } => {
                assert_eq!(*id, 5);
                assert_eq!(clause.len(), 2);
                assert_eq!(clause.lits()[0].dimacs(), -2);
                assert_eq!(clause.lits()[1].dimacs(), 3);
                assert_eq!(antecedents, &[1, 4]);
            }
            _ => panic!("expected Add step"),
        }
    }
}
