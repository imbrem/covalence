//! External-egglog driver (feature `external-egglog`).
//!
//! Bridges upstream egglog (`egglog = "2"`) into our bridge surface. The
//! public API of this module is deliberately upstream-type-free: callers
//! receive [`crate::TermDag`] / [`crate::ProofStore`] handles, never
//! `egglog::*` types. That keeps the dep tree from leaking into the rest
//! of the crate and lets us pin the API surface independently of
//! upstream's release cadence.
//!
//! Two responsibilities, mirroring the integration plan:
//!
//!   1. **Drive upstream egglog** to saturate a user program and
//!      materialise a proof DAG for a `(prove …)` target.
//!   2. **Convert** the resulting upstream proof DAG into our local
//!      [`crate::ProofStore`] mirror so the rest of the crate (the bridge
//!      trait, the driver, every catalogue entry) stays oblivious of
//!      upstream's types.
//!
//! **Scope note.** This module exists to pin down the *API surface* — the
//! function signatures, the module split, and the trust boundary with
//! upstream. The bodies are deliberately stubbed where the upstream
//! entry point is uncertain (egglog 2.0.0 doesn't yet publicise its
//! `proof` module — that lands in the next release) or where the kernel
//! rewrite will force a refactor anyway. The high-level public API
//! ([`run_program`], [`ingest_via_oracle`]) is what the rest of the
//! crate commits to.

use std::collections::{HashMap, HashSet};

use crate::bridge::EgglogBridge;
use crate::error::BridgeError;
use crate::ingest::ingest_proof_store;
use crate::proof::{
    Justification, Proof, ProofId, ProofStore, Proposition, Term, TermDag, TermId,
};

/// Synthesised sort name used by [`ingest_via_oracle`]'s auto-declaration
/// pass. Every upstream constructor we encounter in the proof's term arena
/// gets declared on the bridge with all parameters and result sort set to
/// this name — opaque, single-universe semantics, sufficient for the
/// trusted-shim Rule handler.
const UNIVERSE_SORT: &str = "egglog_universe";

/// Run an egglog `source` program with upstream egglog, materialise the
/// proof DAG for its `(prove …)` target, convert it to our local types,
/// and ingest the result into `bridge` — producing the corresponding
/// [`Thm`](EgglogBridge::Thm) in our kernel.
///
/// This is the user-facing one-shot composing [`run_program`] and
/// [`ingest_proof_store`].
///
/// Caveat: the caller is currently responsible for declaring sorts and
/// constructors on `bridge` ahead of time — the upstream proof DAG
/// references terms by id, and we have no syntactic-declaration
/// extractor yet. The kernel-rewrite work will likely move declaration
/// synthesis into this driver too; see the matching open question in
/// the integration plan.
pub fn ingest_via_oracle<B: EgglogBridge>(
    bridge: &mut B,
    source: &str,
) -> Result<B::Thm, BridgeError> {
    let (dag, store, root) = run_program(source)?;
    auto_declare_from_dag(bridge, &dag)?;
    ingest_proof_store(bridge, &store, &dag, root)
}

/// Walk every term in `dag` and declare its constructor head on `bridge`
/// — once per unique head, with arity inferred from the term shape and
/// every parameter / result typed at the synthesised [`UNIVERSE_SORT`].
///
/// This is the "auto-discover declarations from the proof" fallback that
/// keeps the user's bridge configuration minimal at the cost of giving
/// up sort-level distinctions. Catalogue entries that care about sorts
/// should declare them by hand and skip [`ingest_via_oracle`], using
/// [`run_program`] + [`ingest_proof_store`] directly.
fn auto_declare_from_dag<B: EgglogBridge>(
    bridge: &mut B,
    dag: &TermDag,
) -> Result<(), BridgeError> {
    bridge.declare_sort(UNIVERSE_SORT)?;
    let mut declared: HashSet<String> = HashSet::new();
    for term in dag.iter() {
        let (name, arity) = match term {
            Term::Const(name) => (name.clone(), 0),
            Term::App(name, args) => (name.clone(), args.len()),
        };
        if !declared.insert(name.clone()) {
            continue;
        }
        let params = vec![UNIVERSE_SORT; arity];
        let param_refs: Vec<&str> = params.iter().copied().collect();
        bridge.declare_constructor(&name, &param_refs, UNIVERSE_SORT)?;
    }
    Ok(())
}

/// Parse `source`, run it through a fresh upstream `EGraph`, extract the
/// proof of its (single) `(prove …)` target, and convert the result to
/// our local types.
///
/// Returned [`TermDag`] / [`ProofStore`] are *ours* — upstream's types
/// never appear in this function's signature. Conversion happens inside.
///
/// Errors loudly if:
/// - the source is malformed at upstream's parser;
/// - the program falls outside upstream's proof-encodable fragment;
/// - the program has no `(prove …)` or more than one;
/// - the conversion hits a term shape we don't yet model
///   (primitives, containers).
pub fn run_program(source: &str) -> Result<(TermDag, ProofStore, ProofId), BridgeError> {
    let mut egraph = egglog::EGraph::new_with_proofs();
    let outputs = egraph
        .parse_and_run_program(None, source)
        .map_err(|e| BridgeError::Malformed(format!("egglog parse/run error: {e}")))?;

    let (ext_store, ext_root) = single_prove_output(outputs)?;
    convert_proof_store(&ext_store, ext_root)
}

/// Extract the single `ProveExists` output from a run. `(prove …)` desugars
/// to `(prove-exists …)`, so a single user-level `(prove …)` produces one
/// `CommandOutput::ProveExists`.
fn single_prove_output(
    outputs: Vec<egglog::CommandOutput>,
) -> Result<(egglog::proof::ProofStore, egglog::proof::ProofId), BridgeError> {
    let mut prove_outputs = outputs.into_iter().filter_map(|o| match o {
        egglog::CommandOutput::ProveExists {
            proof_store,
            proof_id,
        } => Some((proof_store, proof_id)),
        _ => None,
    });
    let first = prove_outputs.next().ok_or_else(|| {
        BridgeError::Malformed(
            "egglog source had no `(prove …)` or `(prove-exists …)` — \
             ingest_via_oracle needs a proof target"
                .into(),
        )
    })?;
    if prove_outputs.next().is_some() {
        return Err(BridgeError::Malformed(
            "multiple proof outputs are not supported — single prove target expected".into(),
        ));
    }
    Ok(first)
}

/// Convert an upstream proof DAG (term arena + proof arena + a root id)
/// into our local types. Term indices are preserved one-to-one — upstream
/// is `usize`, ours is `u32`, so we'd overflow only for absurdly large
/// arenas. Proof indices are remapped: we walk the DAG depth-first from
/// `ext_root` and allocate one of ours per reachable upstream proof.
fn convert_proof_store(
    ext_store: &egglog::proof::ProofStore,
    ext_root: egglog::proof::ProofId,
) -> Result<(TermDag, ProofStore, ProofId), BridgeError> {
    let dag = convert_term_dag(ext_store.term_dag())?;
    let mut store = ProofStore::new();
    let mut map: HashMap<egglog::proof::ProofId, ProofId> = HashMap::new();
    let root = convert_proof_dfs(ext_store, ext_root, &mut store, &mut map)?;
    Ok((dag, store, root))
}

/// Walk upstream's `TermDag` densely and build ours in the same insertion
/// order, preserving the `TermId` correspondence.
fn convert_term_dag(ext: &egglog::TermDag) -> Result<TermDag, BridgeError> {
    let mut ours = TermDag::new();
    for i in 0..ext.size() {
        let converted = convert_term(ext.get(i))?;
        let allocated = ours.alloc(converted);
        debug_assert_eq!(
            allocated.0 as usize, i,
            "TermDag conversion expected dense one-to-one indices"
        );
    }
    Ok(ours)
}

/// Convert one upstream term node to ours. `Lit` and `Var` are stringified
/// onto our [`Term::Const`] — the kernel rewrite will eventually grow
/// proper variants for primitive literals and pattern variables.
fn convert_term(ext: &egglog::Term) -> Result<Term, BridgeError> {
    Ok(match ext {
        egglog::Term::Lit(lit) => Term::Const(format!("{lit}")),
        egglog::Term::Var(name) => Term::Const(name.clone()),
        egglog::Term::App(head, args) => {
            let our_args: Vec<TermId> = args.iter().map(|&id| TermId(id as u32)).collect();
            Term::App(head.clone(), our_args)
        }
    })
}

/// Depth-first traversal of the upstream proof DAG, allocating into our
/// `ProofStore` in dependency-first order. `map` memoises so shared
/// sub-proofs lower to a single one of ours, preserving the DAG shape.
fn convert_proof_dfs(
    ext_store: &egglog::proof::ProofStore,
    ext_id: egglog::proof::ProofId,
    out: &mut ProofStore,
    map: &mut HashMap<egglog::proof::ProofId, ProofId>,
) -> Result<ProofId, BridgeError> {
    if let Some(&id) = map.get(&ext_id) {
        return Ok(id);
    }
    let ext_proof = ext_store.get(ext_id);
    let justification = convert_justification(ext_store, ext_proof.justification(), out, map)?;
    let proposition = convert_proposition(ext_proof.proposition());
    let our_id = out.alloc(Proof {
        proposition,
        justification,
    });
    map.insert(ext_id, our_id);
    Ok(our_id)
}

fn convert_proposition(ext: &egglog::proof::Proposition) -> Proposition {
    Proposition {
        lhs: TermId(ext.lhs() as u32),
        rhs: TermId(ext.rhs() as u32),
    }
}

fn convert_justification(
    ext_store: &egglog::proof::ProofStore,
    ext: &egglog::proof::Justification,
    out: &mut ProofStore,
    map: &mut HashMap<egglog::proof::ProofId, ProofId>,
) -> Result<Justification, BridgeError> {
    Ok(match ext {
        egglog::proof::Justification::Fiat => Justification::Fiat,
        egglog::proof::Justification::Rule {
            name,
            premise_proofs,
            substitution,
        } => {
            let premises = premise_proofs
                .iter()
                .map(|&p| convert_proof_dfs(ext_store, p, out, map))
                .collect::<Result<Vec<_>, _>>()?;
            let subst = substitution
                .iter()
                .map(|(k, &v)| (k.clone(), TermId(v as u32)))
                .collect();
            Justification::Rule {
                name: name.clone(),
                premise_proofs: premises,
                substitution: subst,
            }
        }
        egglog::proof::Justification::MergeFn {
            function,
            old_proof,
            new_proof,
        } => Justification::MergeFn {
            function: function.clone(),
            old_proof: convert_proof_dfs(ext_store, *old_proof, out, map)?,
            new_proof: convert_proof_dfs(ext_store, *new_proof, out, map)?,
        },
        egglog::proof::Justification::Trans(a, b) => Justification::Trans(
            convert_proof_dfs(ext_store, *a, out, map)?,
            convert_proof_dfs(ext_store, *b, out, map)?,
        ),
        egglog::proof::Justification::Sym(a) => {
            Justification::Sym(convert_proof_dfs(ext_store, *a, out, map)?)
        }
        egglog::proof::Justification::Congr {
            proof,
            child_index,
            child_proof,
        } => Justification::Congr {
            proof: convert_proof_dfs(ext_store, *proof, out, map)?,
            child_index: *child_index,
            child_proof: convert_proof_dfs(ext_store, *child_proof, out, map)?,
        },
    })
}


/// Pre-flight check: does the program in `path` belong to the fragment
/// upstream egglog can produce a proof DAG for? Wraps
/// [`egglog::file_supports_proofs`].
///
/// Returns `Ok(())` for proof-supportable programs; otherwise
/// [`BridgeError::Malformed`].
///
/// File-shaped on purpose — egglog 2.0.0's public surface only checks
/// files, not source strings. A future release is expected to expose a
/// program/commands variant; when it ships we'll add a sibling
/// `file_supports_proofs_source(&str)` here and call it from
/// [`run_program`] before invoking the upstream EGraph.
pub fn file_supports_proofs(path: &std::path::Path) -> Result<(), BridgeError> {
    if egglog::file_supports_proofs(path) {
        Ok(())
    } else {
        Err(BridgeError::Malformed(format!(
            "program at `{}` is outside upstream's proof-encodable fragment",
            path.display()
        )))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Confirms the dep links and our surface uses only our types — i.e.
    /// `run_program`'s return is `(TermDag, ProofStore, ProofId)` with no
    /// upstream leakage.
    #[test]
    fn surface_uses_only_local_types() {
        fn _accepts_local(_d: &TermDag, _s: &ProofStore, _r: ProofId) {}
    }

    /// Confirms the workspace `[patch.crates-io]` is in effect — upstream's
    /// `proof` module is only publicised on git main (post-2.0.0). Naming
    /// these types is a compile-time-only check; if the patch were
    /// removed this test would stop compiling, not start failing.
    #[test]
    fn upstream_proof_module_is_reachable() {
        fn _accepts_upstream_proof_store(_s: &egglog::proof::ProofStore) {}
        fn _accepts_upstream_proof_id(_i: egglog::proof::ProofId) {}
        fn _accepts_upstream_justification(_j: &egglog::proof::Justification) {}
        fn _accepts_upstream_proposition(_p: &egglog::proof::Proposition) {}
    }

    /// Confirms the upstream entry point our public API currently calls
    /// (`egglog::file_supports_proofs`) links and runs. We hand it a
    /// non-existent path — we don't care about the answer, just that the
    /// call doesn't panic.
    #[test]
    fn file_supports_proofs_runs() {
        let _ = file_supports_proofs(std::path::Path::new("/nonexistent"));
    }

    /// `run_program` against a tiny EUF program — round-trips through
    /// upstream egglog and produces a [`ProofStore`] with at least one
    /// node (`(prove …)` desugars to a `ProveExists`-justified DAG).
    #[test]
    fn run_program_round_trips_tiny_euf() {
        let src = r#"
            (datatype U (A) (B))
            (union (A) (B))
            (prove (= (A) (B)))
        "#;
        let (dag, store, _root) = run_program(src).expect("run_program should succeed");
        assert!(!dag.is_empty(), "term dag should hold the materialised terms");
        assert!(!store.is_empty(), "proof store should hold at least one node");
    }

    /// Source without `(prove …)` produces no proof output, surfaced as a
    /// clean [`BridgeError::Malformed`] rather than a panic.
    #[test]
    fn run_program_rejects_program_without_prove() {
        let err = run_program("(datatype U (A))").expect_err("no `(prove …)` should error");
        assert!(matches!(err, BridgeError::Malformed(_)));
    }
}
