//! Integration tests for the `cov:pure@0.1.0` host bindings.
//!
//! These tests exercise the WIT-generated `Host*` traits directly,
//! without authoring a real guest WASM component. Each test follows
//! the same arc a guest would:
//!
//! 1. Build types and terms through the resource constructors.
//! 2. Apply rule API methods to derive a theorem.
//! 3. Inspect the result via `concl` / `hyps` / `render`.
//!
//! Authoring a guest .wasm that imports `cov:pure/api` lives in a
//! follow-up — it's a significant chunk of wit-bindgen+wit-component
//! work that doesn't change what's verified here: the host-side
//! bindings correctly thread the kernel rules through the resource
//! table.

#![cfg(feature = "runtime")]

// The bindgen-generated traits share names with our backing structs
// (e.g. `HostPureType`), so we rename them to `*Api` for use in UFCS
// calls below. Method-call syntax (`h.foo(...)`) is ambiguous because
// the four resource traits all have `equals`, `render`, `drop`, etc.
use covalence_wasm::pure::{
    PureHost,
    cov::pure::api::{
        HostPureType as TypeApi, HostTerm as TermApi, HostTermSet as TermSetApi, HostThm as ThmApi,
    },
};
use wasmtime::component::Resource;

fn unwrap_trappable<T>(r: wasmtime::Result<Result<T, String>>, ctx: &str) -> T {
    r.unwrap_or_else(|e| panic!("trap in {ctx}: {e}"))
        .unwrap_or_else(|e| panic!("err in {ctx}: {e}"))
}

/// Helper: construct a borrow handle from a resource we hold by rep.
/// All non-`drop` resource methods on borrowed resources work fine
/// against handles created via `Resource::new_borrow`.
fn borrow<T>(rep: u32) -> Resource<T> {
    Resource::new_borrow(rep)
}

// ============================================================================
// Tier 1: smoke — types and terms exist and round-trip through the table.
// ============================================================================

#[test]
fn pure_type_prop_render() {
    let mut h = PureHost::new();
    let prop = TypeApi::prop(&mut h).expect("prop");
    let s = TypeApi::render(&mut h, borrow(prop.rep())).expect("render");
    assert_eq!(s, "prop");
    assert!(TypeApi::is_prop(&mut h, borrow(prop.rep())).expect("is-prop"));
    TypeApi::drop(&mut h, prop).expect("drop");
}

#[test]
fn pure_type_fun_render() {
    let mut h = PureHost::new();
    let b1 = TypeApi::bytes(&mut h).expect("bytes");
    let b2 = TypeApi::bytes(&mut h).expect("bytes");
    let f = TypeApi::fun(&mut h, borrow(b1.rep()), borrow(b2.rep())).expect("fun");
    let s = TypeApi::render(&mut h, borrow(f.rep())).expect("render");
    // The kernel renders function types with `⇒`.
    assert!(s.contains("⇒") || s.contains("=>"), "got: {s}");
    assert!(!TypeApi::is_prop(&mut h, borrow(f.rep())).expect("is-prop"));
}

#[test]
fn term_type_of_blob_is_bytes() {
    let mut h = PureHost::new();
    let t = TermApi::blob(&mut h, vec![1, 2, 3]).expect("blob");
    let ty = unwrap_trappable(TermApi::type_of(&mut h, borrow(t.rep())), "type-of");
    let bytes = TypeApi::bytes(&mut h).expect("bytes");
    let eq = TypeApi::equals(&mut h, borrow(ty.rep()), borrow(bytes.rep())).expect("equals");
    assert!(eq, "blob should have type bytes");
}

#[test]
fn term_equals_is_alpha_equivalence() {
    let mut h = PureHost::new();
    let bytes_ty = TypeApi::bytes(&mut h).expect("bytes");

    // λx:bytes. x  and  λy:bytes. y  are α-equivalent.
    let body1 = TermApi::bound(&mut h, 0).expect("bound");
    let body2 = TermApi::bound(&mut h, 0).expect("bound");
    let abs1 = TermApi::abs(
        &mut h,
        "x".to_string(),
        borrow(bytes_ty.rep()),
        borrow(body1.rep()),
    )
    .expect("abs1");
    let abs2 = TermApi::abs(
        &mut h,
        "y".to_string(),
        borrow(bytes_ty.rep()),
        borrow(body2.rep()),
    )
    .expect("abs2");
    let eq = TermApi::equals(&mut h, borrow(abs1.rep()), borrow(abs2.rep())).expect("equals");
    assert!(eq, "λx:bytes. x and λy:bytes. y should be α-equivalent");
}

// ============================================================================
// Tier 2: minimal proof — `⊢ x ≡ x` via `refl`.
// ============================================================================

#[test]
fn prove_refl_blob() {
    let mut h = PureHost::new();
    let t = TermApi::blob(&mut h, b"hello".to_vec()).expect("blob");
    let th = unwrap_trappable(ThmApi::refl(&mut h, borrow(t.rep())), "refl");

    // Conclusion should be `t ≡ t`.
    let concl = ThmApi::concl(&mut h, borrow(th.rep())).expect("concl");
    let render = TermApi::render(&mut h, borrow(concl.rep())).expect("render");
    assert!(
        render.contains("≡") || render.contains("="),
        "got: {render}"
    );

    // No hypotheses.
    let hyps = ThmApi::hyps(&mut h, borrow(th.rep())).expect("hyps");
    assert!(TermSetApi::is_empty(&mut h, borrow(hyps.rep())).expect("is-empty"));
    assert_eq!(TermSetApi::len(&mut h, borrow(hyps.rep())).expect("len"), 0);

    // The theorem has no observations.
    assert!(ThmApi::has_no_obs(&mut h, borrow(th.rep())).expect("has-no-obs"));
}

#[test]
fn prove_refl_free_var() {
    let mut h = PureHost::new();
    let bytes_ty = TypeApi::bytes(&mut h).expect("bytes");
    let x = TermApi::free(&mut h, "x".to_string(), borrow(bytes_ty.rep())).expect("free");
    let th = unwrap_trappable(ThmApi::refl(&mut h, borrow(x.rep())), "refl");

    let s = ThmApi::render(&mut h, borrow(th.rep())).expect("render");
    assert!(s.starts_with("⊢"), "got: {s}");
}

// ============================================================================
// Tier 3: equational chain — `trans` + `sym` + `cong-app`.
// ============================================================================

/// Prove `⊢ a ≡ a` then `⊢ a ≡ a` again, chain via trans → `⊢ a ≡ a`.
/// Trivial, but exercises the trans path through the host bindings.
#[test]
fn trans_two_refls() {
    let mut h = PureHost::new();
    let a = TermApi::blob(&mut h, b"a".to_vec()).expect("blob");

    let r1 = unwrap_trappable(ThmApi::refl(&mut h, borrow(a.rep())), "refl1");
    let r2 = unwrap_trappable(ThmApi::refl(&mut h, borrow(a.rep())), "refl2");
    let chained = unwrap_trappable(
        ThmApi::trans(&mut h, borrow(r1.rep()), borrow(r2.rep())),
        "trans",
    );

    // Conclusion: `a ≡ a`.
    let concl = ThmApi::concl(&mut h, borrow(chained.rep())).expect("concl");
    let lhs = TermApi::render(&mut h, borrow(a.rep())).expect("a");
    let render = TermApi::render(&mut h, borrow(concl.rep())).expect("concl");
    assert!(
        render.contains(&lhs),
        "concl {render:?} should mention {lhs:?}"
    );
}

/// Prove `⊢ a ≡ a` then derive `⊢ a ≡ a` by sym.
#[test]
fn sym_of_refl() {
    let mut h = PureHost::new();
    let a = TermApi::blob(&mut h, b"a".to_vec()).expect("blob");
    let r = unwrap_trappable(ThmApi::refl(&mut h, borrow(a.rep())), "refl");
    let s = unwrap_trappable(ThmApi::sym(&mut h, borrow(r.rep())), "sym");

    let concl_r = ThmApi::concl(&mut h, borrow(r.rep())).expect("concl r");
    let concl_s = ThmApi::concl(&mut h, borrow(s.rep())).expect("concl s");
    let eq = TermApi::equals(&mut h, borrow(concl_r.rep()), borrow(concl_s.rep())).expect("eq");
    assert!(eq, "sym of refl should be refl");
}

/// Prove `⊢ f a ≡ f a` via cong-app(refl f, refl a).
#[test]
fn cong_app_two_refls() {
    let mut h = PureHost::new();
    let bytes_ty = TypeApi::bytes(&mut h).expect("bytes");
    let bytes_ty2 = TypeApi::bytes(&mut h).expect("bytes2");
    let arrow =
        TypeApi::fun(&mut h, borrow(bytes_ty.rep()), borrow(bytes_ty2.rep())).expect("arrow");

    let f = TermApi::free(&mut h, "f".to_string(), borrow(arrow.rep())).expect("free f");
    let a = TermApi::free(&mut h, "a".to_string(), borrow(bytes_ty.rep())).expect("free a");
    let fa = TermApi::app(&mut h, borrow(f.rep()), borrow(a.rep())).expect("f a");

    let refl_f = unwrap_trappable(ThmApi::refl(&mut h, borrow(f.rep())), "refl f");
    let refl_a = unwrap_trappable(ThmApi::refl(&mut h, borrow(a.rep())), "refl a");
    let cong = unwrap_trappable(
        ThmApi::cong_app(&mut h, borrow(refl_f.rep()), borrow(refl_a.rep())),
        "cong-app",
    );

    // Conclusion: f a ≡ f a. Verify by comparing to refl(f a).
    let refl_fa = unwrap_trappable(ThmApi::refl(&mut h, borrow(fa.rep())), "refl fa");
    let c1 = ThmApi::concl(&mut h, borrow(cong.rep())).expect("c1");
    let c2 = ThmApi::concl(&mut h, borrow(refl_fa.rep())).expect("c2");
    let eq = TermApi::equals(&mut h, borrow(c1.rep()), borrow(c2.rep())).expect("eq");
    assert!(eq);
}

// ============================================================================
// Tier 4: β-conversion and the LF rules.
// ============================================================================

/// `⊢ (λx:bytes. x) "hi" ≡ "hi"` via beta-conv.
#[test]
fn beta_conv_identity() {
    let mut h = PureHost::new();
    let bytes_ty = TypeApi::bytes(&mut h).expect("bytes");

    // λx:bytes. bound(0)
    let body = TermApi::bound(&mut h, 0).expect("bound 0");
    let id = TermApi::abs(
        &mut h,
        "x".to_string(),
        borrow(bytes_ty.rep()),
        borrow(body.rep()),
    )
    .expect("abs");

    // arg = "hi"
    let hi = TermApi::blob(&mut h, b"hi".to_vec()).expect("blob");
    let app = TermApi::app(&mut h, borrow(id.rep()), borrow(hi.rep())).expect("app");

    let th = unwrap_trappable(ThmApi::beta_conv(&mut h, borrow(app.rep())), "beta-conv");
    let s = ThmApi::render(&mut h, borrow(th.rep())).expect("render");
    // Pure renders blobs as `blob[<len>]`. Both sides should mention it.
    assert!(s.contains("blob["), "got: {s}");

    // Cross-check the conclusion is `((λx:bytes. bound 0) "hi") ≡ "hi"`.
    let concl = ThmApi::concl(&mut h, borrow(th.rep())).expect("concl");
    let expected_lhs = TermApi::app(&mut h, borrow(id.rep()), borrow(hi.rep())).expect("lhs");
    let expected = TermApi::mk_eq(&mut h, borrow(expected_lhs.rep()), borrow(hi.rep()))
        .expect("expected concl");
    assert!(
        TermApi::equals(&mut h, borrow(concl.rep()), borrow(expected.rep())).expect("eq"),
        "beta-conv concl mismatch: {s}"
    );

    // No hypotheses.
    let hyps = ThmApi::hyps(&mut h, borrow(th.rep())).expect("hyps");
    assert!(TermSetApi::is_empty(&mut h, borrow(hyps.rep())).expect("is-empty"));
}

/// `{φ} ⊢ φ` via assume; hyp set has exactly that φ.
#[test]
fn assume_records_hypothesis() {
    let mut h = PureHost::new();
    let prop = TypeApi::prop(&mut h).expect("prop");
    let p = TermApi::free(&mut h, "p".to_string(), borrow(prop.rep())).expect("free p");
    let th = unwrap_trappable(ThmApi::assume(&mut h, borrow(p.rep())), "assume");

    let hyps = ThmApi::hyps(&mut h, borrow(th.rep())).expect("hyps");
    assert_eq!(TermSetApi::len(&mut h, borrow(hyps.rep())).expect("len"), 1);
    assert!(TermSetApi::contains(&mut h, borrow(hyps.rep()), borrow(p.rep())).expect("contains"));

    // The single hyp at index 0 is α-equal to p.
    let h0 = TermSetApi::at(&mut h, borrow(hyps.rep()), 0)
        .expect("at")
        .expect("some");
    let eq = TermApi::equals(&mut h, borrow(h0.rep()), borrow(p.rep())).expect("eq");
    assert!(eq);

    // Out-of-range returns none.
    assert!(
        TermSetApi::at(&mut h, borrow(hyps.rep()), 5)
            .expect("at-oob")
            .is_none()
    );
}

/// Prove `⊢ p ⟹ p` via assume + imp-intro.
#[test]
fn imp_intro_discharges_hypothesis() {
    let mut h = PureHost::new();
    let prop = TypeApi::prop(&mut h).expect("prop");
    let p = TermApi::free(&mut h, "p".to_string(), borrow(prop.rep())).expect("free p");

    let assumed = unwrap_trappable(ThmApi::assume(&mut h, borrow(p.rep())), "assume");
    let derived = unwrap_trappable(
        ThmApi::imp_intro(&mut h, borrow(assumed.rep()), borrow(p.rep())),
        "imp-intro",
    );

    // Empty hyps.
    let hyps = ThmApi::hyps(&mut h, borrow(derived.rep())).expect("hyps");
    assert!(TermSetApi::is_empty(&mut h, borrow(hyps.rep())).expect("is-empty"));

    // Concl: p ⟹ p — compare to the manual term.
    let p_imp_p = TermApi::imp(&mut h, borrow(p.rep()), borrow(p.rep())).expect("p⟹p");
    let concl = ThmApi::concl(&mut h, borrow(derived.rep())).expect("concl");
    let eq = TermApi::equals(&mut h, borrow(concl.rep()), borrow(p_imp_p.rep())).expect("eq");
    assert!(eq);
}

/// Prove `⊢ ⋀x:bytes. x ≡ x` by abstracting over a refl.
#[test]
fn all_intro_over_refl() {
    let mut h = PureHost::new();
    let bytes_ty = TypeApi::bytes(&mut h).expect("bytes");
    let x = TermApi::free(&mut h, "x".to_string(), borrow(bytes_ty.rep())).expect("free");

    let r = unwrap_trappable(ThmApi::refl(&mut h, borrow(x.rep())), "refl x");
    let universal = unwrap_trappable(
        ThmApi::all_intro(
            &mut h,
            borrow(r.rep()),
            "x".to_string(),
            borrow(bytes_ty.rep()),
        ),
        "all-intro",
    );

    let s = ThmApi::render(&mut h, borrow(universal.rep())).expect("render");
    assert!(
        s.contains("⋀") || s.contains("forall") || s.contains("/\\"),
        "got: {s}"
    );

    // Specialize back: `⊢ "hi" ≡ "hi"`.
    let hi = TermApi::blob(&mut h, b"hi".to_vec()).expect("blob");
    let specialized = unwrap_trappable(
        ThmApi::all_elim(&mut h, borrow(universal.rep()), borrow(hi.rep())),
        "all-elim",
    );
    // After specialization: `⊢ "hi" ≡ "hi"`. Verify by α-equality
    // against the manually constructed `refl("hi")`.
    let refl_hi = unwrap_trappable(ThmApi::refl(&mut h, borrow(hi.rep())), "refl hi");
    let c1 = ThmApi::concl(&mut h, borrow(specialized.rep())).expect("c1");
    let c2 = ThmApi::concl(&mut h, borrow(refl_hi.rep())).expect("c2");
    assert!(
        TermApi::equals(&mut h, borrow(c1.rep()), borrow(c2.rep())).expect("eq"),
        "all-elim of universal refl should give refl",
    );
}

// ============================================================================
// Tier 5: error paths through the WIT (trappable result mapping).
// ============================================================================

#[test]
fn refl_on_open_term_errors() {
    let mut h = PureHost::new();
    // bound(0) is an open term — type_of fails, so refl fails.
    let open = TermApi::bound(&mut h, 0).expect("bound");
    let outer = ThmApi::refl(&mut h, borrow(open.rep())).expect("outer");
    let err = outer.expect_err("refl of bound-0 must fail at the WIT layer");
    // Just sanity-check the error is non-empty.
    assert!(!err.is_empty(), "expected non-empty error string");
}

#[test]
fn imp_intro_on_non_prop_errors() {
    let mut h = PureHost::new();
    // refl of "hi" → ⊢ "hi" ≡ "hi". Trying to imp-intro on a non-prop
    // φ should fail through the WIT.
    let hi = TermApi::blob(&mut h, b"hi".to_vec()).expect("blob");
    let refl = unwrap_trappable(ThmApi::refl(&mut h, borrow(hi.rep())), "refl");
    // φ = `"hi"` is type `bytes`, not `prop` → imp-intro should err.
    let outer = ThmApi::imp_intro(&mut h, borrow(refl.rep()), borrow(hi.rep())).expect("outer");
    let err = outer.expect_err("imp-intro on non-prop must fail");
    assert!(!err.is_empty());
}

// ============================================================================
// Tier 6: `inst_tfree` and `define` parity with the Rust kernel.
// ============================================================================

#[test]
fn inst_tfree_specializes_type_var() {
    let mut h = PureHost::new();
    // `⋀x:'a. x ≡ x` over an arbitrary type 'a.
    let a_ty = TypeApi::tfree(&mut h, "a".to_string()).expect("tfree");
    let x = TermApi::free(&mut h, "x".to_string(), borrow(a_ty.rep())).expect("free x");
    let refl = unwrap_trappable(ThmApi::refl(&mut h, borrow(x.rep())), "refl");
    let universal = unwrap_trappable(
        ThmApi::all_intro(
            &mut h,
            borrow(refl.rep()),
            "x".to_string(),
            borrow(a_ty.rep()),
        ),
        "all-intro",
    );

    // Substitute α ↦ bytes.
    let bytes_ty = TypeApi::bytes(&mut h).expect("bytes");
    let inst = unwrap_trappable(
        ThmApi::inst_tfree(
            &mut h,
            borrow(universal.rep()),
            "a".to_string(),
            borrow(bytes_ty.rep()),
        ),
        "inst-tfree",
    );

    let s = ThmApi::render(&mut h, borrow(inst.rep())).expect("render");
    assert!(s.contains("bytes") || s.contains("byte"), "got: {s}");
}
