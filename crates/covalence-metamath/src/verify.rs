use std::collections::HashMap;

use covalence_types::Decision;

use crate::database::{Database, Frame, Proof, Statement, StatementId, SymbolId};
use crate::error::MmError;

/// Summary of verification results.
#[derive(Debug, Clone)]
pub struct VerifyResult {
    /// Number of successfully verified `$p` statements.
    pub verified: usize,
    /// Total number of `$p` statements.
    pub total: usize,
}

impl VerifyResult {
    /// `Sat` if all proofs verified, `Unsat` otherwise.
    pub fn decision(&self) -> Decision {
        Decision::from(self.verified == self.total)
    }
}

/// Verify all `$p` statements in the database.
pub fn verify_all(db: &Database) -> Result<VerifyResult, MmError> {
    let mut verified = 0;
    let mut total = 0;
    for (i, stmt) in db.statements.iter().enumerate() {
        if matches!(stmt, Statement::Provable { .. }) {
            total += 1;
            verify_proof(db, StatementId(i as u32))?;
            verified += 1;
        }
    }
    Ok(VerifyResult { verified, total })
}

/// A decoded proof step from a compressed proof.
enum ProofStep {
    /// Reference a statement by its id (mandatory hyp, label-block entry, or prior theorem).
    Stmt(StatementId),
    /// Save top of stack to heap.
    Save,
    /// Push a previously saved heap entry.
    Heap(usize),
}

/// Decompress a compressed proof into a sequence of proof steps.
fn decompress_proof(
    labels: &[String],
    letters: &[u8],
    frame: &Frame,
    db: &Database,
    theorem: &str,
) -> Result<Vec<ProofStep>, MmError> {
    let mand_count = frame.floats.len() + frame.essentials.len();
    let label_count = labels.len();

    // Resolve label block entries to statement ids.
    let label_ids: Vec<StatementId> = labels
        .iter()
        .map(|l| {
            db.lookup_label(l).ok_or_else(|| MmError::UnknownLabel {
                theorem: theorem.to_owned(),
                label: l.clone(),
            })
        })
        .collect::<Result<_, _>>()?;

    let mut steps = Vec::new();
    let mut heap_count: usize = 0;
    let mut i = 0;

    while i < letters.len() {
        let b = letters[i];

        if b == b'?' {
            return Err(MmError::CompressedProofError {
                theorem: theorem.to_owned(),
                message: "incomplete proof (contains `?`)".into(),
            });
        }

        if b == b'Z' {
            steps.push(ProofStep::Save);
            heap_count += 1;
            i += 1;
            continue;
        }

        // Decode proof integer.
        // A-T (1-20) are terminal digits, U-Y (1-5) are continuation digits.
        let mut n: usize = 0;
        loop {
            let c = letters[i];
            i += 1;
            if c >= b'A' && c <= b'T' {
                // Terminal digit: value 1-20
                let t = (c - b'A') as usize + 1;
                n = n * 20 + t;
                break;
            } else if c >= b'U' && c <= b'Y' {
                // Continuation digit: value 1-5
                let d = (c - b'U') as usize + 1;
                n = n * 5 + d;
            } else if c == b'Z' || c == b'?' {
                // Shouldn't reach here since we handle Z above, but just in case.
                return Err(MmError::CompressedProofError {
                    theorem: theorem.to_owned(),
                    message: format!("unexpected `{}` mid-integer", c as char),
                });
            } else {
                return Err(MmError::CompressedProofError {
                    theorem: theorem.to_owned(),
                    message: format!("invalid character `{}` in letter block", c as char),
                });
            }

            if i >= letters.len() {
                return Err(MmError::CompressedProofError {
                    theorem: theorem.to_owned(),
                    message: "letter block ends mid-integer".into(),
                });
            }
        }

        // Resolve proof integer n (1-based).
        if n == 0 {
            return Err(MmError::CompressedProofError {
                theorem: theorem.to_owned(),
                message: "proof integer 0 is invalid".into(),
            });
        }

        if n <= mand_count {
            // Mandatory hypothesis: floats first, then essentials.
            let idx = n - 1;
            let id = if idx < frame.floats.len() {
                frame.floats[idx]
            } else {
                frame.essentials[idx - frame.floats.len()]
            };
            steps.push(ProofStep::Stmt(id));
        } else if n <= mand_count + label_count {
            // Label block entry.
            let lid = n - mand_count - 1;
            steps.push(ProofStep::Stmt(label_ids[lid]));
        } else {
            // Heap backreference.
            let hidx = n - mand_count - label_count - 1;
            if hidx >= heap_count {
                return Err(MmError::CompressedProofError {
                    theorem: theorem.to_owned(),
                    message: format!(
                        "heap backreference {} out of range (heap has {} entries)",
                        hidx, heap_count
                    ),
                });
            }
            steps.push(ProofStep::Heap(hidx));
        }
    }

    Ok(steps)
}

/// Verify a single `$p` statement's proof.
pub fn verify_proof(db: &Database, stmt_id: StatementId) -> Result<(), MmError> {
    let stmt = db.statement(stmt_id);
    let Statement::Provable {
        label: theorem,
        symbols: assertion,
        frame,
        proof,
    } = stmt
    else {
        return Ok(());
    };

    let mut stack: Vec<Vec<SymbolId>> = Vec::new();

    match proof {
        Proof::Normal(labels) => {
            for proof_label in labels {
                let target_id =
                    db.lookup_label(proof_label)
                        .ok_or_else(|| MmError::UnknownLabel {
                            theorem: theorem.clone(),
                            label: proof_label.clone(),
                        })?;
                execute_step(db, target_id, &mut stack, theorem)?;
            }
        }
        Proof::Compressed { labels, letters } => {
            let steps = decompress_proof(labels, letters, frame, db, theorem)?;
            let mut heap: Vec<Vec<SymbolId>> = Vec::new();

            for step in &steps {
                match step {
                    ProofStep::Stmt(target_id) => {
                        execute_step(db, *target_id, &mut stack, theorem)?;
                    }
                    ProofStep::Save => {
                        let top = stack.last().ok_or_else(|| MmError::StackUnderflow {
                            theorem: theorem.clone(),
                        })?;
                        heap.push(top.clone());
                    }
                    ProofStep::Heap(idx) => {
                        stack.push(heap[*idx].clone());
                    }
                }
            }
        }
    }

    // Stack should contain exactly one entry matching the assertion.
    if stack.len() != 1 {
        return Err(MmError::StackResidue {
            theorem: theorem.clone(),
            count: stack.len(),
        });
    }

    if stack[0] != *assertion {
        return Err(MmError::ResultMismatch {
            theorem: theorem.clone(),
        });
    }

    // $d checking not enforced in v1.
    let _ = &frame.disjoints;

    Ok(())
}

/// Execute a single proof step: push hypothesis or pop+unify for axiom/theorem.
fn execute_step(
    db: &Database,
    target_id: StatementId,
    stack: &mut Vec<Vec<SymbolId>>,
    theorem: &str,
) -> Result<(), MmError> {
    let target = db.statement(target_id);

    match target {
        Statement::Float { typecode, var, .. } => {
            stack.push(vec![*typecode, *var]);
        }
        Statement::Essential { symbols, .. } => {
            stack.push(symbols.clone());
        }
        Statement::Axiom {
            symbols: target_syms,
            frame: target_frame,
            ..
        }
        | Statement::Provable {
            symbols: target_syms,
            frame: target_frame,
            ..
        } => {
            // Pop hypotheses and compute substitution.
            let n_hyps = target_frame.floats.len() + target_frame.essentials.len();
            if stack.len() < n_hyps {
                return Err(MmError::StackUnderflow {
                    theorem: theorem.to_owned(),
                });
            }
            let hyp_entries: Vec<Vec<SymbolId>> = stack.drain(stack.len() - n_hyps..).collect();

            // Build substitution from $f hypotheses.
            let mut subst: HashMap<SymbolId, Vec<SymbolId>> = HashMap::new();
            let mut hyp_idx = 0;
            for &fid in &target_frame.floats {
                let Statement::Float { typecode, var, .. } = db.statement(fid) else {
                    unreachable!();
                };
                let entry = &hyp_entries[hyp_idx];
                hyp_idx += 1;

                // First symbol of the stack entry must match the typecode.
                if entry.is_empty() || entry[0] != *typecode {
                    return Err(MmError::UnificationFailed {
                        theorem: theorem.to_owned(),
                        message: format!(
                            "typecode mismatch for variable `{}`",
                            db.symbol_name(*var)
                        ),
                    });
                }
                subst.insert(*var, entry[1..].to_vec());
            }

            // Verify $e hypotheses match after substitution.
            for &eid in &target_frame.essentials {
                let Statement::Essential { symbols: esyms, .. } = db.statement(eid) else {
                    unreachable!();
                };
                let substituted = apply_subst(esyms, &subst);
                let entry = &hyp_entries[hyp_idx];
                hyp_idx += 1;

                if *entry != substituted {
                    return Err(MmError::UnificationFailed {
                        theorem: theorem.to_owned(),
                        message: format!(
                            "$e hypothesis mismatch: expected {:?}, got {:?}",
                            substituted
                                .iter()
                                .map(|s| db.symbol_name(*s))
                                .collect::<Vec<_>>(),
                            entry.iter().map(|s| db.symbol_name(*s)).collect::<Vec<_>>(),
                        ),
                    });
                }
            }

            // Push the substituted result.
            let result = apply_subst(target_syms, &subst);
            stack.push(result);
        }
        _ => {
            return Err(MmError::CompressedProofError {
                theorem: theorem.to_owned(),
                message: format!("unexpected statement type for label in proof"),
            });
        }
    }

    Ok(())
}

/// Apply a substitution map to a symbol string.
fn apply_subst(symbols: &[SymbolId], subst: &HashMap<SymbolId, Vec<SymbolId>>) -> Vec<SymbolId> {
    let mut result = Vec::new();
    for &sym in symbols {
        if let Some(replacement) = subst.get(&sym) {
            result.extend_from_slice(replacement);
        } else {
            result.push(sym);
        }
    }
    result
}

/// Decode a single compressed proof integer for testing.
/// Returns the integer value for a sequence of uppercase letters.
#[cfg(test)]
fn decode_compressed_integer(letters: &[u8]) -> Option<usize> {
    let mut n: usize = 0;
    let mut i = 0;
    while i < letters.len() {
        let c = letters[i];
        i += 1;
        if c >= b'A' && c <= b'T' {
            let t = (c - b'A') as usize + 1;
            n = n * 20 + t;
            return Some(n);
        } else if c >= b'U' && c <= b'Y' {
            let d = (c - b'U') as usize + 1;
            n = n * 5 + d;
        } else {
            return None;
        }
    }
    None // incomplete
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parse::parse;

    /// The "demo0" database from the Metamath book.
    const DEMO0: &str = "\
        $c 0 + = -> ( ) term wff |- $.\n\
        $v t r s P Q $.\n\
        tt $f term t $.\n\
        tr $f term r $.\n\
        ts $f term s $.\n\
        wp $f wff P $.\n\
        wq $f wff Q $.\n\
        tze $a term 0 $.\n\
        tpl $a term ( t + r ) $.\n\
        weq $a wff t = r $.\n\
        wim $a wff ( P -> Q ) $.\n\
        a1 $a |- ( t = r -> ( t = s -> r = s ) ) $.\n\
        a2 $a |- ( t + 0 ) = t $.\n\
        ${  min $e |- P $.  maj $e |- ( P -> Q ) $.\n\
            mp $a |- Q $.\n\
        $}\n\
        th1 $p |- t = t $= tt tze tpl tt weq tt tt weq tt a2 tt tze tpl \
            tt weq tt tze tpl tt weq tt tt weq wim tt a2 tt tze tpl \
            tt tt a1 mp mp $.\n\
    ";

    #[test]
    fn parse_demo0() {
        let db = parse(DEMO0).unwrap();
        assert!(db.lookup_label("th1").is_some());
        assert!(db.lookup_label("a1").is_some());
        assert!(db.lookup_label("mp").is_some());
    }

    #[test]
    fn verify_demo0() {
        let db = parse(DEMO0).unwrap();
        let result = verify_all(&db).unwrap();
        assert_eq!(result.verified, 1);
        assert_eq!(result.total, 1);
        assert_eq!(result.decision(), Decision::Sat);
    }

    #[test]
    fn verify_bad_proof() {
        // Tamper with th1's proof by removing the last step.
        let input = "\
            $c 0 + = -> ( ) term wff |- $.\n\
            $v t r s P Q $.\n\
            tt $f term t $.\n\
            tr $f term r $.\n\
            ts $f term s $.\n\
            wp $f wff P $.\n\
            wq $f wff Q $.\n\
            tze $a term 0 $.\n\
            tpl $a term ( t + r ) $.\n\
            weq $a wff t = r $.\n\
            wim $a wff ( P -> Q ) $.\n\
            a1 $a |- ( t = r -> ( t = s -> r = s ) ) $.\n\
            a2 $a |- ( t + 0 ) = t $.\n\
            ${  min $e |- P $.  maj $e |- ( P -> Q ) $.\n\
                mp $a |- Q $.\n\
            $}\n\
            th1 $p |- t = t $= tt tze tpl tt weq $.\n\
        ";
        let db = parse(input).unwrap();
        assert!(verify_all(&db).is_err());
    }

    #[test]
    fn verify_unknown_label() {
        let input = "\
            $c term $.\n\
            $v t $.\n\
            tt $f term t $.\n\
            th $p term t $= tt bogus $.\n\
        ";
        let db = parse(input).unwrap();
        let err = verify_all(&db).unwrap_err();
        assert!(matches!(err, MmError::UnknownLabel { .. }));
    }

    /// A slightly richer example with two theorems.
    #[test]
    fn verify_two_theorems() {
        let input = "\
            $c 0 + = -> ( ) term wff |- $.\n\
            $v t r s P Q $.\n\
            tt $f term t $.\n\
            tr $f term r $.\n\
            ts $f term s $.\n\
            wp $f wff P $.\n\
            wq $f wff Q $.\n\
            tze $a term 0 $.\n\
            tpl $a term ( t + r ) $.\n\
            weq $a wff t = r $.\n\
            wim $a wff ( P -> Q ) $.\n\
            a1 $a |- ( t = r -> ( t = s -> r = s ) ) $.\n\
            a2 $a |- ( t + 0 ) = t $.\n\
            ${  min $e |- P $.  maj $e |- ( P -> Q ) $.\n\
                mp $a |- Q $.\n\
            $}\n\
            th1 $p |- t = t $= tt tze tpl tt weq tt tt weq tt a2 tt tze tpl \
                tt weq tt tze tpl tt weq tt tt weq wim tt a2 tt tze tpl \
                tt tt a1 mp mp $.\n\
            $( th2 proves 0 = 0, reusing th1 $)\n\
            th2 $p |- 0 = 0 $= tze th1 $.\n\
        ";
        let db = parse(input).unwrap();
        let result = verify_all(&db).unwrap();
        assert_eq!(result.verified, 2);
        assert_eq!(result.total, 2);
        assert_eq!(result.decision(), Decision::Sat);
    }

    // --- Compressed proof tests ---

    #[test]
    fn decode_integers() {
        // A=1, B=2, ..., T=20
        assert_eq!(decode_compressed_integer(b"A"), Some(1));
        assert_eq!(decode_compressed_integer(b"B"), Some(2));
        assert_eq!(decode_compressed_integer(b"T"), Some(20));
        // UA=21, UB=22, ..., UT=40
        assert_eq!(decode_compressed_integer(b"UA"), Some(21));
        assert_eq!(decode_compressed_integer(b"UB"), Some(22));
        assert_eq!(decode_compressed_integer(b"UT"), Some(40));
        // VA=41, ..., YT=120
        assert_eq!(decode_compressed_integer(b"VA"), Some(41));
        assert_eq!(decode_compressed_integer(b"YT"), Some(120));
        // UUA=121
        assert_eq!(decode_compressed_integer(b"UUA"), Some(121));
    }

    #[test]
    fn verify_demo0_compressed() {
        // Same demo0 but th1 uses a compressed proof without Z saves.
        // M=1 (mandatory: tt), L=7 (tze tpl weq wim a2 a1 mp).
        // A=tt, B=tze, C=tpl, D=weq, E=wim, F=a2, G=a1, H=mp.
        let input = "\
            $c 0 + = -> ( ) term wff |- $.\n\
            $v t r s P Q $.\n\
            tt $f term t $.\n\
            tr $f term r $.\n\
            ts $f term s $.\n\
            wp $f wff P $.\n\
            wq $f wff Q $.\n\
            tze $a term 0 $.\n\
            tpl $a term ( t + r ) $.\n\
            weq $a wff t = r $.\n\
            wim $a wff ( P -> Q ) $.\n\
            a1 $a |- ( t = r -> ( t = s -> r = s ) ) $.\n\
            a2 $a |- ( t + 0 ) = t $.\n\
            ${  min $e |- P $.  maj $e |- ( P -> Q ) $.\n\
                mp $a |- Q $.\n\
            $}\n\
            th1 $p |- t = t $= ( tze tpl weq wim a2 a1 mp ) ABCADAADAFABCADABCADAADEAFABCAAGHH $.\n\
        ";
        let db = parse(input).unwrap();
        let result = verify_all(&db).unwrap();
        assert_eq!(result.verified, 1);
        assert_eq!(result.total, 1);
        assert_eq!(result.decision(), Decision::Sat);
    }

    #[test]
    fn verify_compressed_with_save() {
        // Same demo0 but th1 uses Z saves to reduce repetition.
        // heap[0]=wff(t+0)=t (I=9), heap[1]=wff t=t (J=10), heap[2]=|-(t+0)=t (K=11).
        let input = "\
            $c 0 + = -> ( ) term wff |- $.\n\
            $v t r s P Q $.\n\
            tt $f term t $.\n\
            tr $f term r $.\n\
            ts $f term s $.\n\
            wp $f wff P $.\n\
            wq $f wff Q $.\n\
            tze $a term 0 $.\n\
            tpl $a term ( t + r ) $.\n\
            weq $a wff t = r $.\n\
            wim $a wff ( P -> Q ) $.\n\
            a1 $a |- ( t = r -> ( t = s -> r = s ) ) $.\n\
            a2 $a |- ( t + 0 ) = t $.\n\
            ${  min $e |- P $.  maj $e |- ( P -> Q ) $.\n\
                mp $a |- Q $.\n\
            $}\n\
            th1 $p |- t = t $= ( tze tpl weq wim a2 a1 mp ) ABCADZAADZAFZIIJEKABCAAGHH $.\n\
        ";
        let db = parse(input).unwrap();
        let result = verify_all(&db).unwrap();
        assert_eq!(result.verified, 1);
        assert_eq!(result.total, 1);
        assert_eq!(result.decision(), Decision::Sat);
    }

    #[test]
    fn parse_compressed_proof_structure() {
        let input = "\
            $c 0 term $.\n\
            $v t $.\n\
            tt $f term t $.\n\
            tze $a term 0 $.\n\
            th $p term t $= ( tze ) AB $.\n\
        ";
        let db = parse(input).unwrap();
        let stmt_id = db.lookup_label("th").unwrap();
        let stmt = db.statement(stmt_id);
        match stmt {
            Statement::Provable { proof, .. } => match proof {
                Proof::Compressed { labels, letters } => {
                    assert_eq!(labels, &["tze"]);
                    assert_eq!(letters, b"AB");
                }
                _ => panic!("expected compressed proof"),
            },
            _ => panic!("expected provable statement"),
        }
    }
}
