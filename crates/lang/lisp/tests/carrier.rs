//! The **abstract S-expression carrier battery** — slice 1 of
//! `notes/vibes/lisp/abstract-sexpr-api.md` (§3.3 made operational).
//!
//! # What these tests pin
//!
//! - **Carrier-generic round-trips**: the same surface text quotes and
//!   renders identically through the free surface instance, the carved
//!   `sexpr` carrier (with and without an integer backend), the ACL2
//!   carrier, and a **fresh third carved instance** at another payload —
//!   written once against `AbstractSExpr`, no per-dialect copies.
//! - **Structural laws are genuine theorems**: `proj` / `inj_atom` /
//!   `induct` outputs are asserted `hyps().is_empty()` **and** equal to
//!   independently built conclusions (the shared check() style) — pure
//!   delegation to `covalence-init`, nothing minted.
//! - **The third carrier costs no new proofs**: `CarvedSExpr::build_with`
//!   at payload `int` + the same generic suites = the "same proofs at
//!   another payload" claim, operational.
//! - **Retargeting**: one generic function (`second_element`, the ground
//!   `car`/`cdr` walker) produces per-dialect theorems whose *statements
//!   differ* (carrier types, atom encodings) while the rendered value
//!   agrees — the differences are displayed, not erased. (The full §3.1
//!   metacircular two-dialect demonstration needs the slice-2/4 reduction
//!   seams and stays deferred; see the generated open-work index.)
//! - **Negative controls**: dialect-honest refusals (no integer atoms in
//!   `sector`, the ACL2 `asym "NIL"` contract, `NatVariant` negatives,
//!   stuck `proj`) error cleanly, minting nothing.
#![cfg(feature = "hol")]

use std::sync::{Arc, OnceLock};

use covalence_core::subst;
use covalence_hol_eval::EvalThm as Thm;
use covalence_hol_eval::derived::DerivedRules;
use covalence_hol_eval::{mk_blob, mk_int};
use covalence_init::init::eq::beta_expand;
use covalence_init::init::ext::{TermExt, ThmExt};
use covalence_init::init::inductive::carved::{CarvedSExpr, carved};
use covalence_init::{Term, Type};
use covalence_lisp::carrier::{Acl2Carrier, CarvedCarrier, KernelSExpr, acl2_payload_ty};
use covalence_lisp::hol::HolError;
use covalence_lisp::int_backend::{IntBackend, IntVariant, NatVariant};
use covalence_lisp::reader::{read_book_with, read_scheme_with};
use covalence_sexp::abstract_sexpr::{
    AbstractSExpr, NumeralPolicy, PayloadLit, PayloadOwned, SurfaceSExpr,
};
use covalence_sexp::{SExpr, parse, prettyprint};
use covalence_sexpr_api::{ProperList, SExprF, SExprView as BackendSExprView};
use covalence_types::Int;

// ============================================================================
// Fixtures
// ============================================================================

fn one(src: &str) -> SExpr {
    let mut v = parse(src).expect("parse");
    assert_eq!(v.len(), 1, "expected one form in {src:?}");
    v.pop().unwrap()
}

fn pp(e: &SExpr) -> String {
    let mut buf = Vec::new();
    prettyprint(std::slice::from_ref(e), &mut buf).expect("prettyprint");
    String::from_utf8(buf).expect("utf8")
}

fn int(n: i64) -> Int {
    Int::from(i128::from(n))
}

/// The **fresh third carved instance** (§3.3): the same construction run at
/// payload `int` — no new proofs, one process-global build.
fn int_cell() -> &'static CarvedSExpr {
    static CELL: OnceLock<CarvedSExpr> = OnceLock::new();
    // Initializer calls `build_with` directly (re-entrancy discipline).
    CELL.get_or_init(|| CarvedSExpr::build_with(Type::int(), "test.icell").expect("icell build"))
}

fn icell_carrier() -> CarvedCarrier {
    CarvedCarrier::over(int_cell()).with_quote_policy(NumeralPolicy::Int)
}

/// The `sector+int` configuration: the flagship carve + the signed backend.
fn sector_int_carrier() -> CarvedCarrier {
    let cs = carved().expect("carved");
    let t = Term::app(cs.atom.clone(), mk_blob(b"t".to_vec()));
    let nil = Term::app(cs.atom.clone(), mk_blob(b"nil".to_vec()));
    let be: Arc<dyn IntBackend + Send + Sync> = Arc::new(IntVariant::new(cs.tau.clone(), t, nil));
    CarvedCarrier::with_int(be).expect("with_int")
}

fn sector_nat_carrier() -> CarvedCarrier {
    let cs = carved().expect("carved");
    let t = Term::app(cs.atom.clone(), mk_blob(b"t".to_vec()));
    let nil = Term::app(cs.atom.clone(), mk_blob(b"nil".to_vec()));
    let be: Arc<dyn IntBackend + Send + Sync> = Arc::new(NatVariant::new(cs.tau.clone(), t, nil));
    CarvedCarrier::with_int(be).expect("with_int")
}

fn symbol_payload(atom: &covalence_sexp::Atom) -> Result<PayloadOwned, HolError> {
    Ok(match atom {
        covalence_sexp::Atom::Symbol(symbol) => PayloadOwned::Sym(symbol.as_bytes().to_vec()),
        covalence_sexp::Atom::Str { bytes, .. } => PayloadOwned::Sym(bytes.to_vec()),
    })
}

#[test]
fn dialect_readers_target_kernel_inductive_carriers() {
    let scheme_carrier = CarvedCarrier::sector().expect("carved carrier");
    let scheme = read_scheme_with(&scheme_carrier, "'MixedCase", &symbol_payload)
        .expect("read Scheme into carved data");
    let scheme_items = ProperList::as_list(&scheme_carrier, &scheme[0])
        .expect("observe Scheme datum")
        .expect("quote expansion is proper");
    assert!(matches!(
        BackendSExprView::view(&scheme_carrier, &scheme_items[1]).unwrap(),
        SExprF::Atom(PayloadOwned::Sym(bytes)) if bytes == b"MixedCase"
    ));

    let acl2_carrier = Acl2Carrier::new().expect("ACL2 carrier");
    let acl2 = read_book_with(&acl2_carrier, "'MixedCase", &symbol_payload)
        .expect("read ACL2 into ACL2 data");
    let acl2_items = ProperList::as_list(&acl2_carrier, &acl2[0])
        .expect("observe ACL2 datum")
        .expect("quote expansion is proper");
    assert!(matches!(
        BackendSExprView::view(&acl2_carrier, &acl2_items[1]).unwrap(),
        SExprF::Atom(PayloadOwned::Sym(bytes)) if bytes == b"mixedcase"
    ));
}

// ============================================================================
// Carrier-generic suites (written ONCE)
// ============================================================================

/// Quote `src`, render it back, and assert the pretty-printed text.
fn roundtrip<C: AbstractSExpr>(c: &C, src: &str, want: &str)
where
    C::Error: std::fmt::Debug,
{
    let data = one(src);
    let v = c.quote(&data).expect("quote");
    let back = c.render(&v).expect("datum must render");
    assert_eq!(pp(&back), want, "round-trip mismatch for {src:?}");
}

/// The structural-law suite (§3.3): exact-statement `proj` and `inj_atom`
/// checks over any kernel carrier, at two distinct payload terms `p1`, `p2`
/// with `atom_of` building the carrier's atom-constructor application.
fn structural_suite<C>(c: &C, p1: &Term, p2: &Term, atom_of: &dyn Fn(&Term) -> Term)
where
    C: KernelSExpr<Error = HolError>,
{
    let check = |thm: &Thm, expected: &Term, what: &str| {
        assert!(thm.hyps().is_empty(), "{what}: hypotheses must be empty");
        assert_eq!(thm.concl(), expected, "{what}: exact statement");
    };

    let x = atom_of(p1);
    let y = atom_of(p2);
    let nil = c.nil();
    let pair = c.cons(x.clone(), nil.clone()).expect("cons");

    // Observers (syntactic; negative controls across shapes).
    assert_eq!(c.as_cons(&pair), Some((x.clone(), nil.clone())));
    assert!(c.as_cons(&x).is_none());
    assert!(c.is_nil(&nil));
    assert!(!c.is_nil(&pair));
    assert!(c.as_atom(&pair).is_none());

    // ⊢ car (cons x nil) = x  /  ⊢ cdr (cons x nil) = nil.
    let car_pair = c.proj(false, &pair).expect("car law");
    let expected = Term::app(c.proj_op(false), pair.clone())
        .equals(x.clone())
        .expect("eq");
    check(&car_pair, &expected, "car (cons x nil)");
    let cdr_pair = c.proj(true, &pair).expect("cdr law");
    let expected = Term::app(c.proj_op(true), pair.clone())
        .equals(nil.clone())
        .expect("eq");
    check(&cdr_pair, &expected, "cdr (cons x nil)");

    // Leaf defaults: ⊢ car nil = nil, ⊢ cdr (atom p1) = nil.
    let car_nil = c.proj(false, &nil).expect("car nil law");
    let expected = Term::app(c.proj_op(false), nil.clone())
        .equals(nil.clone())
        .expect("eq");
    check(&car_nil, &expected, "car nil");
    let cdr_atom = c.proj(true, &x).expect("cdr atom law");
    let expected = Term::app(c.proj_op(true), x.clone())
        .equals(nil.clone())
        .expect("eq");
    check(&cdr_atom, &expected, "cdr (atom p1)");

    // ⊢ (atom p1 = atom p2) ⟹ p1 = p2 — atom-constructor injectivity.
    let inj = c.inj_atom(p1, p2).expect("inj_atom");
    let expected = x
        .clone()
        .equals(y.clone())
        .expect("eq")
        .imp(p1.clone().equals(p2.clone()).expect("eq"))
        .expect("imp");
    check(&inj, &expected, "atom injectivity");

    // Negative control: `proj` at a non-value (a free variable) is a clean
    // error — no theorem is minted for a stuck term.
    let stuck = Term::free("__not_a_value", c.tau());
    assert!(
        c.proj(false, &stuck).is_err(),
        "proj must reject non-values"
    );
}

/// Structural induction through the seam, at the motive `λs. s = s`:
/// the three case obligations are built generically (β-expansion of `refl`)
/// and `induct` must conclude exactly `⊢ ∀s. (λs. s = s) s`, hyp-free.
fn induct_suite<C>(c: &C, payload: &Type, atom_of: &dyn Fn(&Term) -> Term)
where
    C: KernelSExpr<Error = HolError>,
{
    let tau = c.tau();
    let motive = {
        let s = Term::free("__gs", tau.clone());
        let body = s.clone().equals(s).expect("eq");
        Term::abs(tau.clone(), subst::close(&body, "__gs"))
    };
    let refl_case = |target: Term| -> Thm {
        beta_expand(&motive, target.clone(), Thm::refl(target).expect("refl")).expect("beta")
    };
    // Case `atom`: ⊢ P (atom b), free `b` (the load-bearing hint name).
    let case_atom = refl_case(atom_of(&Term::free("b", payload.clone())));
    // Case `nil`: ⊢ P nil.
    let case_nil = refl_case(c.nil());
    // Case `cons`: ⊢ P h ⟹ P t ⟹ P (cons h t), free `h`, `t`.
    let h = Term::free("h", tau.clone());
    let t = Term::free("t", tau.clone());
    let p_h = Term::app(motive.clone(), h.clone());
    let p_t = Term::app(motive.clone(), t.clone());
    let case_cons = refl_case(c.cons(h, t).expect("cons"))
        .imp_intro(&p_t)
        .expect("imp_intro")
        .imp_intro(&p_h)
        .expect("imp_intro");

    let thm = c
        .induct(&motive, vec![case_atom, case_nil, case_cons])
        .expect("induct");
    assert!(thm.hyps().is_empty(), "induction: hypotheses must be empty");
    let expected = Term::app(motive.clone(), Term::free("__ss", tau.clone()))
        .forall("__ss", tau.clone())
        .expect("forall");
    assert_eq!(thm.concl(), &expected, "induction: exact statement");

    // Negative control: wrong case count is a clean error.
    assert!(c.induct(&motive, vec![]).is_err());
}

/// **The retargeting demonstration (slice-1 level).** One generic ground
/// walker — `second_element`: quote the datum, then prove
/// `⊢ car (cdr v) = <second>` by composing the carrier's projection laws —
/// run over multiple kernel dialects. Returns the composite theorem and the
/// quoted input so callers can pin the *per-dialect* statements.
fn second_element<C>(c: &C, data: &SExpr) -> Result<(Thm, Term), HolError>
where
    C: KernelSExpr<Error = HolError>,
{
    let v = c.quote(data)?;
    let (_, tail) = c
        .as_cons(&v)
        .ok_or_else(|| HolError::Stuck("not a cons".into()))?;
    let cdr_thm = c.proj(true, &v)?; // ⊢ cdr v = tail
    let car_thm = c.proj(false, &tail)?; // ⊢ car tail = second
    let composed = cdr_thm
        .cong_arg(c.proj_op(false))
        .map_err(|e| HolError::Kernel(e.to_string()))? // ⊢ car (cdr v) = car tail
        .trans(car_thm)
        .map_err(|e| HolError::Kernel(e.to_string()))?; // ⊢ car (cdr v) = second
    Ok((composed, v))
}

/// Pin `second_element` on carrier `c`: hyp-free, exactly
/// `⊢ car (cdr (quote data)) = expected`, and the value renders as `want`.
fn check_second<C>(c: &C, src: &str, expected_second: &Term, want: &str, what: &str)
where
    C: KernelSExpr<Error = HolError>,
{
    let data = one(src);
    let (thm, v) = second_element(c, &data).expect(what);
    assert!(thm.hyps().is_empty(), "{what}: hypotheses must be empty");
    let lhs = Term::app(c.proj_op(false), Term::app(c.proj_op(true), v));
    let expected = lhs.equals(expected_second.clone()).expect("eq");
    assert_eq!(thm.concl(), &expected, "{what}: exact statement");
    // The printed value is read off the theorem's RHS.
    let (_, rhs) = thm.concl().as_eq().expect("equation");
    assert_eq!(
        c.render(rhs).map(|e| pp(&e)),
        Some(want.to_string()),
        "{what}: rendered value"
    );
}

// ============================================================================
// Round-trips (one source, every carrier)
// ============================================================================

#[test]
fn roundtrip_all_carriers() {
    let surface = SurfaceSExpr::new();
    let sector = CarvedCarrier::sector().expect("sector");
    let sector_int = sector_int_carrier();
    let acl2 = Acl2Carrier::new().expect("acl2");
    let icell = icell_carrier();

    // Symbol data: identical text through every symbol-capable carrier.
    for (src, want) in [
        ("foo", "foo"),
        ("()", "()"),
        ("(a b c)", "(a b c)"),
        ("(a (b c) () d)", "(a (b c) () d)"),
    ] {
        roundtrip(&surface, src, want);
        roundtrip(&sector, src, want);
        roundtrip(&sector_int, src, want);
        roundtrip(&acl2, src, want);
    }

    // Numeral data: same TEXT everywhere, different underlying atoms —
    // uninterpreted symbols (`sector`, quote policy `Sym`) vs genuine
    // integer payloads (ACL2 `aint`, the int-payload cell).
    for c in [&sector, &sector_int] {
        roundtrip(c, "(1 2 3)", "(1 2 3)");
        assert_eq!(
            c.as_atom(&c.quote(&one("7")).expect("quote")),
            Some(PayloadOwned::Sym(b"7".to_vec())),
            "carved data numerals stay symbol atoms"
        );
    }
    roundtrip(&acl2, "(1 2 3)", "(1 2 3)");
    assert_eq!(
        acl2.as_atom(&acl2.quote(&one("7")).expect("quote")),
        Some(PayloadOwned::Int(int(7))),
        "ACL2 data numerals are genuine integer payload"
    );
    roundtrip(&icell, "(1 2 3)", "(1 2 3)");
    assert_eq!(
        icell.as_atom(&icell.quote(&one("7")).expect("quote")),
        Some(PayloadOwned::Int(int(7))),
        "int-payload cell numerals are genuine integer payload"
    );

    // ACL2 canonicalization pinned: `nil`/`t` (any case) → `anil` / the
    // canonical `t` (observing as the symbol payload `"T"`).
    roundtrip(&acl2, "(x nil t)", "(x () T)");
    assert!(acl2.is_nil(&acl2.quote(&one("NIL")).expect("quote")));
    assert_eq!(acl2.quote(&one("t")).expect("quote"), acl2.t());
}

// ============================================================================
// Structural laws + induction (the same generic suites, three carriers)
// ============================================================================

#[test]
fn structural_laws_carved_bytes() {
    let c = CarvedCarrier::sector().expect("sector");
    let cs = c.theory();
    let p1 = mk_blob(b"a".to_vec());
    let p2 = mk_blob(b"b".to_vec());
    let atom_of = |p: &Term| Term::app(cs.atom.clone(), p.clone());
    structural_suite(&c, &p1, &p2, &atom_of);
    induct_suite(&c, &Type::bytes(), &atom_of);
}

#[test]
fn structural_laws_acl2() {
    let c = Acl2Carrier::new().expect("acl2");
    let th = c.theory();
    // Two distinct payloads across BOTH payload arms: `inl 1` and `inr "a"`.
    let p1 = covalence_hol_eval::defs::inl(Type::int(), Type::bytes())
        .apply(mk_int(int(1)))
        .expect("inl");
    let p2 = covalence_hol_eval::defs::inr(Type::int(), Type::bytes())
        .apply(mk_blob(b"a".to_vec()))
        .expect("inr");
    let atom_of = |p: &Term| Term::app(th.atom.clone(), p.clone());
    structural_suite(&c, &p1, &p2, &atom_of);
    induct_suite(&c, &acl2_payload_ty(), &atom_of);
}

#[test]
fn structural_laws_third_carrier_int_payload() {
    // §3.3: a fresh `build_with` instance at payload `int` — the SAME
    // generic suites pass with no new proofs anywhere.
    let c = icell_carrier();
    let cs = c.theory();
    let p1 = mk_int(int(1));
    let p2 = mk_int(int(2));
    let atom_of = |p: &Term| Term::app(cs.atom.clone(), p.clone());
    structural_suite(&c, &p1, &p2, &atom_of);
    induct_suite(&c, &Type::int(), &atom_of);
}

// ============================================================================
// ACL2 derived-form projection laws (aint / asym unfold + leaf default)
// ============================================================================

#[test]
fn acl2_proj_at_derived_payload_forms() {
    let c = Acl2Carrier::new().expect("acl2");
    let two = c.atom(PayloadLit::Int(&int(2))).expect("aint 2");
    let sym = c.atom(PayloadLit::Sym(b"x")).expect("asym x");
    for (v, what) in [(&two, "cdr (aint 2)"), (&sym, "cdr (asym x)")] {
        // ⊢ cdr v = anil — stated about the DERIVED form (via its defining
        // unfold + the leaf default), hypothesis-free.
        let thm = c.proj(true, v).expect(what);
        assert!(thm.hyps().is_empty(), "{what}: hypotheses must be empty");
        let expected = Term::app(c.proj_op(true), v.clone())
            .equals(c.nil())
            .expect("eq");
        assert_eq!(thm.concl(), &expected, "{what}: exact statement");
    }
}

// ============================================================================
// Retargeting: one walker, three kernel dialects
// ============================================================================

#[test]
fn retarget_second_element_across_dialects() {
    // Same program text over the carved `sexpr` carrier…
    let sector = CarvedCarrier::sector().expect("sector");
    let cs = sector.theory();
    let b_atom = Term::app(cs.atom.clone(), mk_blob(b"b".to_vec()));
    check_second(&sector, "(a b c)", &b_atom, "b", "carved second");

    // …the ACL2 carrier (different carrier type, different atom encoding,
    // same rendered value)…
    let acl2 = Acl2Carrier::new().expect("acl2");
    let b_asym = acl2.atom(PayloadLit::Sym(b"b")).expect("asym b");
    check_second(&acl2, "(a b c)", &b_asym, "b", "acl2 second");

    // …and the fresh int-payload carrier (numerals now genuine payload).
    let icell = icell_carrier();
    let two_atom = icell.atom(PayloadLit::Int(&int(2))).expect("atom 2");
    check_second(&icell, "(1 2 3)", &two_atom, "2", "icell second");

    // ACL2 numerals retarget too: second of `(1 2 3)` is `aint 2`.
    let two_aint = acl2.atom(PayloadLit::Int(&int(2))).expect("aint 2");
    check_second(&acl2, "(1 2 3)", &two_aint, "2", "acl2 int second");

    // The statements genuinely differ: distinct carrier types, distinct
    // atom terms for the same rendered "b".
    assert_ne!(sector.tau(), acl2.tau());
    assert_ne!(b_atom, b_asym);
}

// ============================================================================
// Dialect-honest negative controls
// ============================================================================

#[test]
fn negative_controls() {
    // `sector` has no integer atoms — `atom(Int)` is a clean error.
    let sector = CarvedCarrier::sector().expect("sector");
    assert!(sector.atom(PayloadLit::Int(&int(2))).is_err());

    // `sector+int` builds `(int 2)` and observes it back; `sector`'s
    // observers do NOT see it as an atom (no backend installed).
    let sector_int = sector_int_carrier();
    let two = sector_int.atom(PayloadLit::Int(&int(2))).expect("(int 2)");
    assert_eq!(sector_int.as_atom(&two), Some(PayloadOwned::Int(int(2))));
    assert_eq!(sector.as_atom(&two), None);

    // The `nat` flavour rejects negative literals; the signed one accepts.
    let nat = sector_nat_carrier();
    assert!(nat.atom(PayloadLit::Int(&int(-1))).is_err());
    let m1 = sector_int
        .atom(PayloadLit::Int(&int(-1)))
        .expect("(int -1)");
    assert_eq!(sector_int.as_atom(&m1), Some(PayloadOwned::Int(int(-1))));

    // ACL2 representation contract: never `asym "NIL"`.
    let acl2 = Acl2Carrier::new().expect("acl2");
    assert!(acl2.atom(PayloadLit::Sym(b"NIL")).is_err());
    assert!(acl2.atom(PayloadLit::Sym(b"nil")).is_err());
    // …and string literals are not ACL2 objects.
    assert!(acl2.quote(&one("\"s\"")).is_err());

    // The int-payload cell has no symbol atoms.
    assert!(icell_carrier().atom(PayloadLit::Sym(b"a")).is_err());
}
