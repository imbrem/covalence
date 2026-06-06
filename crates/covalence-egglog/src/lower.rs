//! Lower a parsed egglog [`Command`] sequence into bridge declarations
//! plus a Fiat-only [`ProofStore`].
//!
//! This is the "source → kernel" glue: it applies sort/constructor
//! declarations to a [`EgglogBridge`] as it walks the program, builds a
//! [`TermDag`] from the union'd and proven expressions, allocates one
//! [`Justification::Fiat`] per `(union …)` command, and finally locates
//! the [`Command::Prove`] root.
//!
//! Out of scope here: rewrites, datatypes-with-arity-in-result-position,
//! schedules, the egglog saturation loop. This lowering only supports
//! the subset of egglog programs whose `(prove …)` target is *itself*
//! one of the asserted `(union …)`s (i.e. ground equalities). Programs
//! that require derivation (Trans / Sym / Congr) to reach the proven
//! equality wait until we ingest real proof DAGs from upstream egglog.

use std::collections::HashMap;

use crate::ast::{Command, Expr};
use crate::bridge::EgglogBridge;
use crate::error::BridgeError;
use crate::proof::{
    Justification, Proof, ProofId, ProofStore, Proposition, Term, TermDag, TermId,
};

/// Result of lowering a program: a [`TermDag`] holding every materialised
/// term, a [`ProofStore`] of `Fiat`-justified ground equalities, and the
/// [`ProofId`] of the [`Command::Prove`]'d proposition.
#[derive(Debug)]
pub struct LoweredProgram {
    pub dag: TermDag,
    pub store: ProofStore,
    pub root: ProofId,
}

/// Apply every declaration in `commands` to `bridge`, build a Fiat-only
/// proof store from the `(union …)`s, and return the [`ProofId`] of the
/// (unique) `(prove (= lhs rhs))` whose sides were previously `union`'d.
///
/// Errors loudly if there is no `(prove …)`, more than one, or if the
/// proved equality has no matching `(union …)` in scope — the latter is
/// the "ground-only" restriction this lowering enforces.
pub fn lower_program<B: EgglogBridge>(
    bridge: &mut B,
    commands: &[Command],
) -> Result<LoweredProgram, BridgeError> {
    let mut dag = TermDag::new();
    let mut store = ProofStore::new();
    let mut union_index: HashMap<(Expr, Expr), ProofId> = HashMap::new();
    let mut prove_root: Option<ProofId> = None;

    for cmd in commands {
        match cmd {
            Command::Sort(name) => {
                bridge.declare_sort(name)?;
            }
            Command::Constructor {
                name,
                params,
                result,
            } => {
                let param_refs: Vec<&str> = params.iter().map(String::as_str).collect();
                bridge.declare_constructor(name, &param_refs, result)?;
            }
            Command::Datatype { name, ctors } => {
                bridge.declare_sort(name)?;
                for (ctor_name, ctor_params) in ctors {
                    let param_refs: Vec<&str> =
                        ctor_params.iter().map(String::as_str).collect();
                    bridge.declare_constructor(ctor_name, &param_refs, name)?;
                }
            }
            Command::Union(lhs, rhs) => {
                let lhs_id = build_term(&mut dag, lhs);
                let rhs_id = build_term(&mut dag, rhs);
                let pid = store.alloc(Proof {
                    proposition: Proposition::new(lhs_id, rhs_id),
                    justification: Justification::Fiat,
                });
                // Match both orderings: `(prove (= b a))` after `(union a b)`
                // should still resolve. We could synthesise a Sym justification
                // here instead; for the Fiat-only subset, both orderings point
                // at the same ProofId and `fiat` discharges them identically.
                union_index.insert((lhs.clone(), rhs.clone()), pid);
                union_index.insert((rhs.clone(), lhs.clone()), pid);
            }
            Command::Prove(lhs, rhs) => {
                let _ = build_term(&mut dag, lhs);
                let _ = build_term(&mut dag, rhs);
                let pid = union_index.get(&(lhs.clone(), rhs.clone())).copied().ok_or_else(
                    || {
                        BridgeError::Malformed(format!(
                            "(prove …) target {lhs:?} = {rhs:?} has no matching \
                             (union …) — derivation from source is out of scope \
                             for the lowering, only ground Fiats are supported"
                        ))
                    },
                )?;
                if prove_root.replace(pid).is_some() {
                    return Err(BridgeError::Malformed(
                        "multiple (prove …) commands — only one root supported".into(),
                    ));
                }
            }
        }
    }

    let root = prove_root.ok_or_else(|| {
        BridgeError::Malformed("program has no (prove …) command".into())
    })?;
    Ok(LoweredProgram { dag, store, root })
}

fn build_term(dag: &mut TermDag, expr: &Expr) -> TermId {
    match expr {
        Expr::Sym(s) => dag.alloc(Term::Const(s.clone())),
        Expr::App(head, args) => {
            let arg_ids: Vec<TermId> =
                args.iter().map(|a| build_term(dag, a)).collect();
            dag.alloc(Term::App(head.clone(), arg_ids))
        }
    }
}
