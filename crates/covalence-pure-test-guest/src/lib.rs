//! Guest fixture for `cov:pure@0.1.0`.
//!
//! Compiled to `wasm32-unknown-unknown` as a cdylib, then wrapped into
//! a WASM component by `covalence-wasm`'s integration tests. The host
//! provides `cov:pure/api` (refl, trans, beta-conv, …); this crate
//! exposes a single `run-prover` export that dispatches a small
//! registry of canned proofs by name.
//!
//! The dispatch pattern keeps the WIT surface tiny while letting one
//! guest expose many proofs. The same scaffold can be cloned to drive
//! `cov:kernel/api` or `cov:hol-light/api` once those land — only the
//! WIT path and the prover bodies change.
//!
//! On non-`wasm32` targets the crate compiles to an empty cdylib —
//! `wit_bindgen::generate!` emits `extern "C"` intrinsics that only
//! link in the wasm32 ABI, so the macro is gated.

#![cfg(target_arch = "wasm32")]

wit_bindgen::generate!({
    path: "../covalence-wasm/wit/pure.wit",
    world: "pure-guest",
});

// For wit-bindgen 0.51, a top-level world export emits `Guest` at the
// world's root (here, the crate root). Imports from an interface land
// at `<namespace>::<package>::<interface>`.
use crate::Guest as ProverGuest;
use cov::pure::api::{PureType, Term, Thm};

struct Component;

impl ProverGuest for Component {
    fn run_prover(name: String) -> Result<String, String> {
        match name.as_str() {
            "refl-blob" => prove_refl_blob(),
            "trans-refl-refl" => prove_trans_refl_refl(),
            "imp-intro-p-implies-p" => prove_imp_intro_p_implies_p(),
            "beta-identity" => prove_beta_identity(),
            "all-intro-elim" => prove_all_intro_elim(),
            "inst-tfree" => prove_inst_tfree(),
            other => Err(format!("unknown prover: {other}")),
        }
    }
}

export!(Component);

// ============================================================================
// Provers
// ============================================================================

/// `⊢ "hello" ≡ "hello"`.
fn prove_refl_blob() -> Result<String, String> {
    let hi = Term::blob(&b"hello".to_vec());
    let thm = Thm::refl(&hi).map_err(|e| format!("refl: {e}"))?;
    Ok(thm.render())
}

/// `⊢ a ≡ a` derived by `trans(refl a, refl a)`.
fn prove_trans_refl_refl() -> Result<String, String> {
    let a = Term::blob(&b"a".to_vec());
    let r1 = Thm::refl(&a).map_err(|e| format!("refl1: {e}"))?;
    let r2 = Thm::refl(&a).map_err(|e| format!("refl2: {e}"))?;
    let chained = r1.trans(&r2).map_err(|e| format!("trans: {e}"))?;
    Ok(chained.render())
}

/// `⊢ p ⟹ p` via assume + imp-intro.
fn prove_imp_intro_p_implies_p() -> Result<String, String> {
    let prop = PureType::prop();
    let p = Term::free("p", &prop);
    let assumed = Thm::assume(&p).map_err(|e| format!("assume: {e}"))?;
    let derived = assumed.imp_intro(&p).map_err(|e| format!("imp-intro: {e}"))?;
    Ok(derived.render())
}

/// `⊢ (λx:bytes. x) "hi" ≡ "hi"` via beta-conv.
fn prove_beta_identity() -> Result<String, String> {
    let bytes_ty = PureType::bytes();
    let body = Term::bound(0);
    let id = Term::abs("x", &bytes_ty, &body);
    let hi = Term::blob(&b"hi".to_vec());
    let app = Term::app(&id, &hi);
    let thm = Thm::beta_conv(&app).map_err(|e| format!("beta-conv: {e}"))?;
    Ok(thm.render())
}

/// Quantify over `x` then specialise to `"hi"`: `⊢ "hi" ≡ "hi"`.
fn prove_all_intro_elim() -> Result<String, String> {
    let bytes_ty = PureType::bytes();
    let x = Term::free("x", &bytes_ty);
    let refl_x = Thm::refl(&x).map_err(|e| format!("refl: {e}"))?;
    let universal = refl_x
        .all_intro("x", &bytes_ty)
        .map_err(|e| format!("all-intro: {e}"))?;
    let hi = Term::blob(&b"hi".to_vec());
    let specialized = universal
        .all_elim(&hi)
        .map_err(|e| format!("all-elim: {e}"))?;
    Ok(specialized.render())
}

/// `⊢ ⋀x:'a. x ≡ x`, then `inst-tfree('a ↦ bytes)`.
fn prove_inst_tfree() -> Result<String, String> {
    let a = PureType::tfree("a");
    let x = Term::free("x", &a);
    let r = Thm::refl(&x).map_err(|e| format!("refl: {e}"))?;
    let universal = r.all_intro("x", &a).map_err(|e| format!("all-intro: {e}"))?;
    let bytes_ty = PureType::bytes();
    let inst = universal
        .inst_tfree("a", &bytes_ty)
        .map_err(|e| format!("inst-tfree: {e}"))?;
    Ok(inst.render())
}
