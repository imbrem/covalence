//! Schematic rule application and the RPN proof checker.
//!
//! A normal (uncompressed) Metamath proof is a sequence of labels evaluated
//! against a stack of expressions:
//!
//! * a `$f`/`$e` hypothesis label pushes its expression;
//! * an assertion label (`$a`/`$p`) pops its mandatory hypotheses, unifies the
//!   floats to build a substitution, checks the essentials and the
//!   distinct-variable conditions, and pushes the substituted conclusion.
//!
//! A proof is valid iff it terminates with exactly one expression on the stack,
//! equal to the claimed conclusion. The checker never trusts the proof: every
//! substitution, typecode, and `$d` constraint is re-derived and re-checked.

use std::collections::BTreeSet;

use crate::metamath::database::{Assertion, Database, Statement};
use crate::metamath::error::MmError;
use crate::metamath::expr::{Expr, body_of, render, typecode_of};
use crate::metamath::subst::{Subst, apply_subst, vars_in_body};

/// Verify every `$p` theorem in the database. Returns the number verified.
pub fn verify_all(db: &Database) -> Result<usize, MmError> {
    let mut count = 0;
    for assertion in db.assertions() {
        if assertion.proof.is_some() {
            verify_assertion(db, assertion)?;
            count += 1;
        }
    }
    Ok(count)
}

/// Verify a single `$p` assertion's proof against the database. `$a` axioms
/// (no proof) verify trivially.
pub fn verify_assertion(db: &Database, assertion: &Assertion) -> Result<(), MmError> {
    let Some(proof) = &assertion.proof else {
        return Ok(());
    };
    let theorem = &assertion.label;

    let mut stack: Vec<Expr> = Vec::new();

    for label in proof {
        let stmt = db
            .statement_by_label(label)
            .ok_or_else(|| MmError::UnknownLabel {
                theorem: theorem.clone(),
                label: label.clone(),
            })?;

        match stmt {
            Statement::Float(f) => {
                // Push the expression `typecode var`.
                stack.push(crate::metamath::expr::make_expr(&f.typecode, [f.var.as_str()]));
            }
            Statement::Essential(h) => {
                stack.push(h.expr.clone());
            }
            Statement::Assert(target) => {
                apply_assertion(db, assertion, target, label, &mut stack)?;
            }
            _ => {
                return Err(MmError::UnknownLabel {
                    theorem: theorem.clone(),
                    label: label.clone(),
                });
            }
        }
    }

    if stack.len() != 1 {
        return Err(MmError::StackResidue {
            theorem: theorem.clone(),
            count: stack.len(),
        });
    }
    let result = stack.pop().unwrap();
    if result != assertion.conclusion {
        return Err(MmError::ResultMismatch {
            theorem: theorem.clone(),
            expected: render(&assertion.conclusion),
            found: render(&result),
        });
    }
    Ok(())
}

/// Apply `target` (the asserted rule) within the proof of `current`, popping
/// the mandatory hypotheses off `stack`, checking everything, and pushing the
/// substituted conclusion.
fn apply_assertion(
    db: &Database,
    current: &Assertion,
    target: &Assertion,
    step: &str,
    stack: &mut Vec<Expr>,
) -> Result<(), MmError> {
    let theorem = &current.label;
    let frame = &target.frame;
    let n = frame.mandatory_count();
    if stack.len() < n {
        return Err(MmError::StackUnderflow {
            theorem: theorem.clone(),
            step: step.to_string(),
        });
    }
    // Pop n args; they correspond to floats (first) then essentials (order).
    let args: Vec<Expr> = stack.split_off(stack.len() - n);

    // --- build substitution from floats ---
    let mut subst = Subst::new();
    for (i, f) in frame.floats.iter().enumerate() {
        let arg = &args[i];
        let arg_tc = typecode_of(arg).ok_or_else(|| MmError::TypecodeMismatch {
            theorem: theorem.clone(),
            step: step.to_string(),
            var: f.var.clone(),
            expected: f.typecode.clone(),
            found: render(arg),
        })?;
        if arg_tc != f.typecode {
            return Err(MmError::TypecodeMismatch {
                theorem: theorem.clone(),
                step: step.to_string(),
                var: f.var.clone(),
                expected: f.typecode.clone(),
                found: arg_tc.to_string(),
            });
        }
        let body = body_of(arg).unwrap_or(&[]).to_vec();
        subst.insert(f.var.clone(), body);
    }

    // --- check essentials ---
    for (j, h) in frame.essentials.iter().enumerate() {
        let arg = &args[frame.floats.len() + j];
        let expected = apply_subst(&h.expr, &subst);
        if &expected != arg {
            return Err(MmError::HypothesisMismatch {
                theorem: theorem.clone(),
                step: step.to_string(),
                expected: render(&expected),
                found: render(arg),
            });
        }
    }

    // --- check distinct-variable ($d) conditions ---
    check_disjoints(db, current, target, step, &subst)?;

    // --- push the substituted conclusion ---
    stack.push(apply_subst(&target.conclusion, &subst));
    Ok(())
}

/// Check the target assertion's `$d` conditions under the substitution.
///
/// Metamath's rule: if the applied assertion requires `$d a b`, then for every
/// variable `x` occurring in `subst(a)` and every variable `y` occurring in
/// `subst(b)`:
///   1. `x` and `y` must be syntactically distinct, **and**
///   2. the *current* theorem's frame must itself contain `$d x y`.
///
/// (1) alone would be unsound; (2) is what propagates distinctness obligations
/// outward to the theorem's own signature.
fn check_disjoints(
    db: &Database,
    current: &Assertion,
    target: &Assertion,
    step: &str,
    subst: &Subst,
) -> Result<(), MmError> {
    if target.frame.disjoints.is_empty() {
        return Ok(());
    }
    let is_var = |s: &str| db.is_variable(s);

    // The current theorem's $d pairs, as an unordered-pair set for fast lookup.
    let current_dv: BTreeSet<(String, String)> = current
        .frame
        .disjoints
        .iter()
        .map(|(a, b)| ordered_pair(a, b))
        .collect();

    for (a, b) in &target.frame.disjoints {
        let img_a = subst.get(a).map(|v| v.as_slice()).unwrap_or(&[]);
        let img_b = subst.get(b).map(|v| v.as_slice()).unwrap_or(&[]);
        let vars_a = vars_in_body(img_a, &is_var);
        let vars_b = vars_in_body(img_b, &is_var);

        for &x in &vars_a {
            for &y in &vars_b {
                // (1) substitutions may not share a variable.
                if x == y {
                    return Err(MmError::DisjointViolation {
                        theorem: current.label.clone(),
                        step: step.to_string(),
                        a: a.clone(),
                        b: b.clone(),
                        shared: x.to_string(),
                    });
                }
                // (2) the obligation must be discharged by the current frame.
                if !current_dv.contains(&ordered_pair(x, y)) {
                    return Err(MmError::DisjointViolation {
                        theorem: current.label.clone(),
                        step: step.to_string(),
                        a: a.clone(),
                        b: b.clone(),
                        shared: format!("{x},{y} not declared $d in `{}`", current.label),
                    });
                }
            }
        }
    }
    Ok(())
}

/// Order a variable pair so `(a, b)` and `(b, a)` compare equal.
fn ordered_pair(a: &str, b: &str) -> (String, String) {
    if a <= b {
        (a.to_string(), b.to_string())
    } else {
        (b.to_string(), a.to_string())
    }
}

