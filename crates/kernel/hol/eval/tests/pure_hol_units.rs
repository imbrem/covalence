//! **Pure-HOL unit tests** for the cert families (stage E3 of
//! `notes/vibes/handoff/defs-out-of-core.md`, decision D5): for sample
//! values, derive the equation a cert family mints *from the definitions*
//! — the twin defining theorems + definitional unfolding — and assert
//! conclusion-equality with the cert-minted [`EvalThm`] fact. A mismatch
//! is a soundness finding: the catalogue definition and the native
//! `covalence-pure-eval` computation would disagree, and the two derivable
//! facts would mint `⊢ litₐ = lit_b` for distinct literals.
//!
//! ## What is (and is not) derivable at the pure tier — the honest scoping
//!
//! `Thm<CoreLang>` (the pure-HOL tier, `PureThm` below) admits NO literal
//! axioms: kernel literals `⌜n⌝` (n > 0) are *opaque leaves* there — by
//! design, that is exactly the trust the tier split removes from pure HOL.
//! The literal↔numeral bridge (`⊢ succ ⌜n⌝ = ⌜n+1⌝`, the `SuccCert`
//! literal-denotation axiom) and even `⊢ T` (via `LitEqCert`) live at the
//! eval tier, dying with the literal leaves (decision D3). So an equation
//! between *distinct literal leaves* is not derivable at `Thm<CoreLang>` at
//! all — no test can "prove `nat.add ⌜2⌝ ⌜3⌝ = ⌜5⌝` purely" while literals
//! are kernel leaves. What each test here does instead:
//!
//! 1. **The pure δ/β spine** (`Thm<CoreLang>`): the op's definitional
//!    unfolding on the sample literals, as far as pure rules reach —
//!    pinning that *the definition itself* needs no eval axiom.
//! 2. **The definitional derivation** (eval tier, but *never invoking the
//!    family under test*): the op's proved defining/recursion theorems from
//!    `covalence-init` (derived from the definitions via the recursion
//!    theorem — HOL rules only) + the D3 literal-denotation bridge.
//! 3. **The cert fact**: [`reduce`] (the family certificate rule), asserted
//!    conclusion-equal to (2).
//!
//! The numeral-form computations in (2) use only HOL rules end-to-end, but
//! `covalence-init` pins its theorems at `EvalThm` today, so the *Rust
//! type* of (2) is the eval tier; making init's derivations tier-generic
//! (so they land at `Thm<CoreLang>` verbatim) is recorded follow-up work
//! (`SKELETONS.md`).
//!
//! Family coverage: `nat.add` (NatArithCert), `int.add` (IntArithCert),
//! `bytes.cat` (BytesCert), `u8.add` (FixedWidthCert). The bytes and
//! fixed-width *definitional evaluations* are blocked (list recursion
//! pending / intentionally declaration-only conversions — see the module
//! notes on each test); their body-forcing differentials live in
//! `tests/audit_reduce.rs::audit_reduce_matches_body`.

use covalence_core::seam::HolTier;
use covalence_core::{IntTag, Term, TermKind, Type};
use covalence_hol_eval::defs;
use covalence_hol_eval::defs::IntOp;
use covalence_hol_eval::{EvalThm, mk_blob, mk_int, mk_nat, reduce};

/// The pure-HOL tier: `covalence_core::Thm` defaults to `Thm<CoreLang>`,
/// which admits the HOL rule catalogue alone — no cert / toHOL /
/// literal-denotation axioms. Everything typed `PureThm` in this file is
/// pure-tier by construction (the type parameter IS the trust declaration).
type PureThm = covalence_core::Thm;

// ============================================================================
// Helpers
// ============================================================================

fn nat(n: u64) -> Term {
    mk_nat(n)
}

fn app2(f: Term, a: Term, b: Term) -> Term {
    Term::app(Term::app(f, a), b)
}

fn app3(f: Term, a: Term, b: Term, c: Term) -> Term {
    Term::app(Term::app(Term::app(f, a), b), c)
}

/// The RHS of a `⊢ lhs = rhs` conclusion.
fn rhs_of<L: HolTier>(thm: &covalence_core::Thm<L>) -> Term {
    let (_, rhs) = thm.concl().as_eq().expect("not an equation");
    rhs.clone()
}

/// Spine of an application: `(head, [arg1, …, argn])`.
fn spine(t: &Term) -> (Term, Vec<Term>) {
    let mut head = t.clone();
    let mut args = Vec::new();
    while let TermKind::App(f, x) = head.kind() {
        args.push(x.clone());
        head = f.clone();
    }
    args.reverse();
    (head, args)
}

/// `⊢ t = t'` at the PURE tier, where `t = (spec a₁ … aₙ)` and `t'` is the
/// spec's definitional body applied to the args with every β-redex on the
/// left spine contracted. Uses only `Thm<CoreLang>` rules: the kernel
/// δ-unfold rule for the head, `mk_comb` congruence, `beta_conv`, `trans`.
fn pure_spine(t: &Term) -> PureThm {
    let (head, args) = spine(t);
    let mut acc = PureThm::unfold_term_spec(head).expect("head must be a let-style spec");
    for a in args {
        acc = acc
            .mk_comb(PureThm::refl(a).unwrap())
            .expect("congruence over an argument");
        let cur = rhs_of(&acc);
        if let TermKind::App(f, _) = cur.kind()
            && matches!(f.kind(), TermKind::Abs(..))
        {
            acc = acc.trans(PureThm::beta_conv(cur).unwrap()).unwrap();
        }
    }
    acc
}

/// Common assertions for a pure spine: hypothesis-free, an equation whose
/// LHS is exactly the original redex.
fn assert_pure_spine(spine_thm: &PureThm, redex: &Term) {
    assert!(spine_thm.hyps().is_empty(), "pure spine is hypothesis-free");
    let (lhs, _) = spine_thm
        .concl()
        .as_eq()
        .expect("spine concl is an equation");
    assert_eq!(lhs, redex, "spine LHS is the original redex");
}

/// `⊢ succ ⌜n⌝ = ⌜n+1⌝` — the D3 literal-denotation bridge (`SuccCert`;
/// the ONLY eval-tier axiom the nat definitional derivation consumes).
fn fold_succ(n: u64) -> EvalThm {
    reduce(&Term::app(Term::succ(), nat(n))).expect("succ on a literal reduces")
}

// ============================================================================
// nat.add ⌜2⌝ ⌜3⌝ = ⌜5⌝  (NatArithCert)
// ============================================================================

/// `⊢ nat.add ⌜a⌝ ⌜b⌝ = ⌜a+b⌝` derived **from the definition**: `nat.add`'s
/// proved recursion equations (`covalence-init`'s `add_base`/`add_step`,
/// derived from the catalogue body via the recursion theorem — HOL rules
/// only) plus the [`fold_succ`] literal bridge. `NatArithCert` is never
/// invoked: the only certificate consumed is the `succ` literal denotation.
fn nat_add_by_definition(a: u64, b: u64) -> EvalThm {
    use covalence_init::init::nat::{add_base, add_step};

    // ⊢ nat.add ⌜0⌝ ⌜b⌝ = ⌜b⌝ — the base equation (⌜0⌝ IS the kernel zero).
    let mut acc = add_base().all_elim(nat(b)).unwrap();
    // Peel `a` successors: given acc : ⊢ nat.add ⌜k⌝ ⌜b⌝ = ⌜k+b⌝, derive
    // acc' : ⊢ nat.add ⌜k+1⌝ ⌜b⌝ = ⌜k+1+b⌝.
    for k in 0..a {
        // nat.add ⌜k+1⌝ ⌜b⌝ = nat.add (succ ⌜k⌝) ⌜b⌝   [literal bridge, cong]
        let cong = EvalThm::refl(defs::nat_add())
            .unwrap()
            .mk_comb(fold_succ(k).sym().unwrap())
            .unwrap()
            .mk_comb(EvalThm::refl(nat(b)).unwrap())
            .unwrap();
        // = succ (nat.add ⌜k⌝ ⌜b⌝)                      [add_step]
        let step = add_step()
            .all_elim(nat(k))
            .unwrap()
            .all_elim(nat(b))
            .unwrap();
        // = succ ⌜k+b⌝                                  [IH under succ]
        let under = EvalThm::refl(Term::succ()).unwrap().mk_comb(acc).unwrap();
        // = ⌜k+1+b⌝                                     [literal bridge]
        acc = cong
            .trans(step)
            .unwrap()
            .trans(under)
            .unwrap()
            .trans(fold_succ(k + b))
            .unwrap();
    }
    acc
}

#[test]
fn pure_hol_unit_nat_add_2_3() {
    let redex = app2(defs::nat_add(), nat(2), nat(3));

    // (1) The pure δ/β spine, at Thm<CoreLang>:
    //     ⊢ nat.add ⌜2⌝ ⌜3⌝ = iter ⌜2⌝ succ ⌜3⌝.
    let spine_thm = pure_spine(&redex);
    assert_pure_spine(&spine_thm, &redex);
    let expected_body = app3(defs::iter(Type::nat()), nat(2), Term::succ(), nat(3));
    assert_eq!(
        rhs_of(&spine_thm),
        expected_body,
        "nat.add unfolds to its `iter n succ m` definition on the sample"
    );

    // (2) The definitional derivation (recursion equations + literal bridge).
    let by_def = nat_add_by_definition(2, 3);
    assert!(by_def.hyps().is_empty());

    // (3) The cert fact — conclusion-equal to (2).
    let by_cert = reduce(&redex).expect("NatArithCert decides the sample");
    assert_eq!(
        by_def.concl(),
        by_cert.concl(),
        "definition and native nat.add disagree on 2 + 3 — soundness finding"
    );
    assert_eq!(rhs_of(&by_def), nat(5));
}

/// A second, asymmetric sample (7 + 0 exercises the base equation last,
/// 0 + 4 exercises it first) — cheap insurance that the agreement is not
/// an artifact of one shape.
#[test]
fn pure_hol_unit_nat_add_more_samples() {
    for (a, b) in [(0, 4), (1, 1), (4, 0)] {
        let by_def = nat_add_by_definition(a, b);
        let by_cert = reduce(&app2(defs::nat_add(), nat(a), nat(b))).unwrap();
        assert_eq!(by_def.concl(), by_cert.concl(), "mismatch at {a} + {b}");
    }
}

// ============================================================================
// int.add ⌜-2⌝ ⌜0⌝ = ⌜-2⌝  (IntArithCert)
// ============================================================================

/// The int sample goes through `covalence-init`'s **proved ring theory**:
/// `⊢ ∀a. a + 0 = a` is derived through the whole Grothendieck quotient
/// construction (components, well-definedness, literal-`0` coherence), not
/// through `IntArithCert` on the sample. Instantiating it at `⌜-2⌝` must
/// agree with the direct cert fact.
///
/// (Caveat, recorded: init's literal-`0` coherence lemma itself pins
/// `⌜0⌝ = MK(0,0)` using the two readings of `0 + 0` — one of which is the
/// cert path. So this differential checks per-instance agreement of the
/// definitional reading with the cert, not full cert-independence; the
/// literal denotation is D3 residue either way.)
#[test]
fn pure_hol_unit_int_add_neg2_0() {
    let redex = app2(defs::int_add(), mk_int(-2), mk_int(0));

    // (1) The pure δ/β spine at Thm<CoreLang>: int.add unfolds to its
    //     Grothendieck body on the samples (shape not pinned — the body is
    //     the quotient construction; LHS/hyps are the invariants).
    let spine_thm = pure_spine(&redex);
    assert_pure_spine(&spine_thm, &redex);

    // (2) The definitional derivation: the proved ring axiom, instantiated.
    let by_def = covalence_init::init::int::add_zero()
        .all_elim(mk_int(-2))
        .unwrap();
    assert!(by_def.hyps().is_empty());

    // (3) The cert fact.
    let by_cert = reduce(&redex).expect("IntArithCert decides the sample");
    assert_eq!(
        by_def.concl(),
        by_cert.concl(),
        "definitional int ring theory and native int.add disagree on -2 + 0"
    );
    assert_eq!(rhs_of(&by_cert), mk_int(-2));
}

// ============================================================================
// bytes.cat ⌜b"ab"⌝ ⌜b"cd"⌝ = ⌜b"abcd"⌝  (BytesCert)
// ============================================================================

/// The bytes definitional *evaluation* is blocked: the `Blob` literal ↔
/// `list u8` bridge and the list recursion theorem are pending (see
/// `covalence-init`'s `init/SKELETONS.md` — cons-side list theory), so no
/// derivation reaches `⌜b"abcd"⌝` from `bytes.cat`'s body yet. What IS
/// checkable today: the pure δ/β spine (the definition unfolds at
/// `Thm<CoreLang>`) and the cert fact's semantics.
#[test]
fn pure_hol_unit_bytes_cat_spine_and_cert() {
    let redex = app2(
        defs::bytes_cat(),
        mk_blob(b"ab".to_vec()),
        mk_blob(b"cd".to_vec()),
    );

    // (1) Pure spine at Thm<CoreLang>.
    let spine_thm = pure_spine(&redex);
    assert_pure_spine(&spine_thm, &redex);

    // (3) Cert fact (BytesCert) — value pinned by tests/audit_reduce.rs;
    //     re-asserted here as the target the definitional evaluation must
    //     eventually reach.
    let by_cert = reduce(&redex).expect("BytesCert decides the sample");
    assert!(by_cert.hyps().is_empty());
    assert_eq!(rhs_of(&by_cert), mk_blob(b"abcd".to_vec()));
}

// ============================================================================
// u8.add ⌜200⌝ ⌜100⌝ = ⌜44⌝  (FixedWidthCert)
// ============================================================================

/// The fixed-width definitional *evaluation* bottoms out at the
/// `toNat`/`fromNat` conversions, which are **intentionally
/// declaration-only** (the primitive reducible interface — not a stub): the
/// full body-forced differential (cert-evaluating the inner ops) lives in
/// `tests/audit_reduce.rs::audit_reduce_matches_body`. Here: the pure δ/β
/// spine at `Thm<CoreLang>` plus the wrap-around cert fact.
#[test]
fn pure_hol_unit_u8_add_wrap_spine_and_cert() {
    let op = defs::int_op(IntTag::U8, IntOp::Add);
    let redex = app2(op, Term::u8_lit(200), Term::u8_lit(100));

    // (1) Pure spine at Thm<CoreLang>: the ring op has a let-style body.
    let spine_thm = pure_spine(&redex);
    assert_pure_spine(&spine_thm, &redex);

    // (3) Cert fact: wrap mod 2^8 — 200 + 100 = 44.
    let by_cert = reduce(&redex).expect("FixedWidthCert decides the sample");
    assert!(by_cert.hyps().is_empty());
    assert_eq!(rhs_of(&by_cert), Term::u8_lit(44));
}

// ============================================================================
// Tier hygiene: the pure spine lifts INTO the eval tier (never back)
// ============================================================================

/// The pure spine composes with eval-tier facts only after an explicit
/// `lift` — pinning the one-way trust direction of the tower.
#[test]
fn pure_spine_lifts_into_eval_tier() {
    let redex = app2(defs::nat_add(), nat(2), nat(3));
    let lifted: EvalThm = pure_spine(&redex).lift().unwrap();
    // ⊢ nat.add ⌜2⌝ ⌜3⌝ = iter ⌜2⌝ succ ⌜3⌝, now usable beside cert facts:
    // chain with the definitional derivation's conclusion via sym/trans.
    let by_def = nat_add_by_definition(2, 3);
    let chained = lifted.sym().unwrap().trans(by_def).unwrap();
    assert_eq!(
        chained.concl(),
        &covalence_core::hol::hol_eq(
            app3(defs::iter(Type::nat()), nat(2), Term::succ(), nat(3)),
            nat(5),
        ),
        "⊢ iter ⌜2⌝ succ ⌜3⌝ = ⌜5⌝ — the unfolded form evaluates too"
    );
}
