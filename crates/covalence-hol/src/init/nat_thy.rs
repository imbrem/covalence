//! `nat.cov ⊨ nat.thy` — the **satisfaction proof** that kernel-nat (the
//! structure carrying a `natrec`) realizes the canonical `nat` interface.
//!
//! Two artifacts pin the interface↔implementation correspondence:
//!
//! - [`init/nat.sig`](../nat.sig) / [`init/nat.thy`](../nat.thy) — the
//!   **specification**: the `nat` signature (sort + ops) and the full list of
//!   proof obligations `(#spec NAME C)`, one per *exported* theorem of
//!   `nat.cov`.
//! - [`init/nat.cov`](../nat.cov) — the **proof**: ~45 lemmas over the kernel
//!   `natrec` env, each `#export`ed.
//!
//! The witnessing model is the **self model**: sort `nat` := kernel `nat`, and
//! each op interpreted by its kernel term (`add := nat.add`, `rec := natrec-op`,
//! literal `0` := zero, …). Re-elaborating a spec's conclusion in the kernel env
//! therefore reproduces *exactly* the `nat.cov` conclusion, so satisfaction is
//! checked by, for each `(#spec NAME C)`:
//!
//! 1. parsing `C` against the **self-model env** (`core` + the `natrec` env +
//!    `logic`, i.e. exactly what `nat.cov` is proved over), and
//! 2. confirming `nat.cov` exports a theorem named `NAME` whose conclusion is
//!    **α-equal** to that parsed goal (`Term` equality is α-equality under the
//!    locally-nameless representation).
//!
//! This is a *genuine* satisfaction check: every obligation is discharged by a
//! kernel-rechecked theorem, matched by α-equal conclusion — not by name alone.
//!
//! The deeper, **carrier-generic** model (specs over a `tfree` sort,
//! re-elaborated at any structure carrying a `natrec`, with `nat/self` only one
//! instance) is deferred — see `SKELETONS.md`.

use crate::script::{Env, ScriptError, Scope, syntax};

/// The **self-model env** the `nat` specs are interpreted over: `core` (the
/// kernel ops/rules), the `natrec` env (the freeness + recursion givens), and
/// `logic` — exactly the import set `nat.cov` is proved against. Re-elaborating
/// a spec's conclusion here reproduces the kernel-nat statement.
fn self_model_env() -> Env {
    let mut e = Env::core();
    e.merge(&crate::init::nat::natrec_env());
    e.merge(&crate::init::logic::cov::env());
    e
}

/// One discharged obligation: the spec name and the kernel goal it elaborated to.
struct SpecGoal {
    name: String,
    goal: covalence_core::Term,
}

/// Parse `init/nat.thy`, returning each `(#spec NAME C)` elaborated at the
/// self model. Errors on a malformed `.thy` or a spec that does not typecheck
/// in the kernel env.
fn parse_nat_thy_specs() -> Result<Vec<SpecGoal>, ScriptError> {
    let src = include_str!("nat.thy");
    let forms = covalence_sexp::parse(src)
        .map_err(|e| ScriptError::Syntax(format!("nat.thy: parse error: {e}")))?;
    // The single top-level form is the `(#thy nat (over nat) (#spec …) …)`.
    let thy = forms
        .iter()
        .find_map(|f| {
            let items = f.as_list()?;
            (items.first().and_then(|s| s.as_symbol()) == Some("#thy")).then_some(items)
        })
        .ok_or_else(|| ScriptError::Syntax("nat.thy: no top-level (#thy …) form".into()))?;

    let env = self_model_env();
    let mut specs = Vec::new();
    for clause in &thy[1..] {
        let Some(items) = clause.as_list() else {
            continue;
        };
        if items.first().and_then(|s| s.as_symbol()) != Some("#spec") {
            continue; // skip the `(over nat)` clause and the name atom
        }
        if items.len() != 3 {
            return Err(ScriptError::Syntax(format!(
                "nat.thy: (#spec …) expects NAME and a conclusion, got {} elements",
                items.len()
            )));
        }
        let name = items[1]
            .as_symbol()
            .ok_or_else(|| ScriptError::Syntax("nat.thy: #spec name is not a symbol".into()))?
            .to_string();
        let mut scope = Scope::new();
        let goal = syntax::parse_term(&items[2], &mut scope, &env)
            .map_err(|e| ScriptError::Syntax(format!("nat.thy: spec `{name}`: {e}")))?;
        specs.push(SpecGoal { name, goal });
    }
    Ok(specs)
}

/// Check `nat.cov ⊨ nat.thy`: every `(#spec NAME C)` of `nat.thy` is discharged
/// by an exported `nat.cov` theorem named `NAME` whose conclusion is α-equal to
/// `C` (interpreted at the self model). Returns the matched spec names on
/// success, or a description of the first mismatch.
pub fn check_nat_cov_satisfies_nat_thy() -> Result<Vec<String>, String> {
    let specs = parse_nat_thy_specs().map_err(|e| format!("{e}"))?;
    if specs.is_empty() {
        return Err("nat.thy declared no specs".into());
    }
    let cov = crate::init::nat::cov::env();
    let mut matched = Vec::new();
    for spec in &specs {
        let thm = cov.lemma_ready(&spec.name).ok_or_else(|| {
            format!(
                "spec `{}` is not discharged: nat.cov exports no theorem of that name",
                spec.name
            )
        })?;
        // `Term` equality is α-equality (locally-nameless de Bruijn indices).
        if thm.concl() != &spec.goal {
            return Err(format!(
                "spec `{}` mismatch:\n  thy goal: {}\n  cov concl: {}",
                spec.name,
                spec.goal,
                thm.concl()
            ));
        }
        matched.push(spec.name.clone());
    }
    Ok(matched)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The canonical `nat.sig` is a well-formed `(#sig nat …)`: it parses, names
    /// its sort `nat`, and declares every op the specs mention.
    #[test]
    fn nat_sig_is_well_formed() {
        let src = include_str!("nat.sig");
        let forms = covalence_sexp::parse(src).expect("nat.sig parses");
        let sig_form = forms
            .iter()
            .find_map(|f| {
                let items = f.as_list()?;
                (items.first().and_then(|s| s.as_symbol()) == Some("#sig")).then_some(items)
            })
            .expect("nat.sig has a (#sig …) form");
        let sig = crate::script::theory::parse_sig(sig_form, &Env::core())
            .expect("nat.sig is a well-formed signature");
        assert_eq!(sig.name, "nat");
        assert_eq!(sig.sort, "nat");
        // Every op the spec conclusions mention is declared.
        for op in ["rec", "zero", "succ", "add", "mul", "sub", "pow", "shl", "le", "lt"] {
            assert!(
                sig.ops.iter().any(|o| o.name == op),
                "nat.sig must declare op `{op}`"
            );
        }
    }

    /// THE SATISFACTION CHECK: `nat.cov ⊨ nat.thy` — every spec in `nat.thy` is
    /// discharged by an α-equal exported `nat.cov` theorem of the same name. The
    /// witnessing model is kernel nat (the self model).
    #[test]
    fn nat_cov_satisfies_nat_thy() {
        let matched = check_nat_cov_satisfies_nat_thy().expect("nat.cov ⊨ nat.thy");
        // All 47 exported `nat.cov` theorems are specified and discharged.
        assert_eq!(
            matched.len(),
            47,
            "expected 47 discharged specs, got {}: {matched:?}",
            matched.len()
        );
    }
}
