//! **S-expressions reified inside HOL** — the universal syntax carrier
//! (`notes/vibes/metatheory.md` §8.1). Every reified object language's concrete
//! syntax is an `SExpr`; this module gives the datatype, its constructors,
//! a recursor, and a structural induction principle, all as honest HOL
//! objects with no new kernel TCB.
//!
//! ## Encoding (same rationale as [`crate::init::prop`])
//!
//! We use a **Church / impredicative encoding** over a fresh result type
//! `'r`, rather than carving a kernel subtype through the recursion engine
//! ([`crate::init::inductive`]). For a first-order, directly-recursive
//! datatype this gives constructors, a recursor, *and* an induction
//! principle for free — each a one-line HOL term build / proof — and stays
//! rank-1 and TCB-free. (The `list`-carrier path in `defs/list.rs` is the
//! heavyweight alternative; its `cons` recursor is not even built yet, so
//! reusing it here would block on unfinished work — see the generated open-work index.)
//!
//! The grammar is `atom bytes | snil | scons SExpr SExpr` (atoms carry a
//! `bytes` payload — the parsed token; lists are nil/cons spines):
//!
//! ```text
//!   S⟨'r⟩  :=  (bytes → 'r)        -- atom
//!            → 'r                  -- snil
//!            → ('r → 'r → 'r)      -- scons
//!            → 'r
//! ```
//!
//! ## What is provided
//!
//! - constructors [`atom`], [`snil`], [`scons`];
//! - the recursor [`rec`] — `rec fa fn fc (C …) = f_C …` holds **by β**,
//!   witnessed per constructor by [`rec_atom`], [`rec_snil`], [`rec_scons`];
//! - a note on structural induction ([`induct_note`]): the *recursor* and
//!   its equations are what downstream impredicative soundness proofs use;
//!   genuine `SExpr` induction needs a well-formedness side condition and
//!   is deferred (see the function's docs + the generated open-work index).
//!
//! Distinct constructor applications are distinct HOL terms, so this is
//! genuine reified syntax (not a shallow embedding).

use covalence_core::{Result, Term, Type};
use covalence_hol_eval::EvalThm as Thm;

use crate::init::ext::TermExt;

// ============================================================================
// The carrier `S⟨'r⟩`
// ============================================================================

fn rty() -> Type {
    Type::tfree("r")
}

fn bytes() -> Type {
    Type::bytes()
}

/// `bytes → 'r` — the `atom` handler slot.
fn atom_h_ty() -> Type {
    Type::fun(bytes(), rty())
}

/// `'r → 'r → 'r` — the `scons` handler slot.
fn cons_h_ty() -> Type {
    Type::fun(rty(), Type::fun(rty(), rty()))
}

/// `S⟨'r⟩ = (bytes→'r) → 'r → ('r→'r→'r) → 'r`.
pub fn sexpr_ty() -> Type {
    Type::fun(atom_h_ty(), Type::fun(rty(), Type::fun(cons_h_ty(), rty())))
}

/// The three handler binder names, in fold order.
const HANDLERS: [(&str, crate::NullaryTypeHandler); 3] =
    [("fa", atom_h_ty), ("fn_", rty), ("fc", cons_h_ty)];

fn handler(name: &str) -> Term {
    let ty = HANDLERS
        .iter()
        .find(|(n, _)| *n == name)
        .map(|(_, t)| t())
        .expect("handler name");
    Term::free(name, ty)
}

/// Wrap a fold `body : 'r` in the three handler abstractions → `S⟨'r⟩`.
fn close_handlers(body: Term) -> Term {
    let mut t = body;
    for (name, ty) in HANDLERS.iter().rev() {
        t = Term::abs(ty(), covalence_core::subst::close(&t, name));
    }
    t
}

/// Apply an `S⟨'r⟩` to the three handlers, producing its fold `: 'r`.
fn apply_handlers(s: Term) -> Term {
    let mut t = s;
    for (name, _) in HANDLERS {
        t = Term::app(t, handler(name));
    }
    t
}

// ============================================================================
// Constructors
// ============================================================================

/// `atom b : S⟨'r⟩` — an atom carrying the `bytes` payload `b`.
pub fn atom(b: Term) -> Term {
    close_handlers(Term::app(handler("fa"), b))
}

/// `snil : S⟨'r⟩` — the empty list.
pub fn snil() -> Term {
    close_handlers(handler("fn_"))
}

/// `scons h t : S⟨'r⟩` — cons `h` onto list `t`.
pub fn scons(h: Term, t: Term) -> Term {
    let body = Term::app(
        Term::app(handler("fc"), apply_handlers(h)),
        apply_handlers(t),
    );
    close_handlers(body)
}

/// `[s₀, s₁, …] = scons s₀ (scons s₁ (… snil))` — an S-expression list.
pub fn slist(elems: Vec<Term>) -> Term {
    let mut acc = snil();
    for e in elems.into_iter().rev() {
        acc = scons(e, acc);
    }
    acc
}

// ============================================================================
// Recursor + its defining equations (by β)
// ============================================================================

/// `rec fa fn fc s : r` — the catamorphism, simply `s fa fn fc`. The
/// encoded `s : S⟨'r⟩` is polymorphic in the result type; we instantiate
/// `'r` to the handlers' concrete result type (read off `fn`'s type)
/// before applying, so e.g. `nat`-valued folds typecheck.
pub fn rec(fa: Term, fnil: Term, fc: Term, s: Term) -> Result<Term> {
    let r = fnil.type_of()?;
    let s_at = covalence_core::subst::subst_tfree_in_term(&s, "r", &r);
    s_at.apply(fa)?.apply(fnil)?.apply(fc)
}

/// `⊢ rec fa fn fc (atom b) = fa b` — the `atom` recursor equation.
pub fn rec_atom(fa: Term, fnil: Term, fc: Term, b: Term) -> Result<Thm> {
    let lhs = rec(fa.clone(), fnil.clone(), fc.clone(), atom(b.clone()))?;
    let rhs = fa.apply(b)?;
    prove_rec_eq(lhs, rhs)
}

/// `⊢ rec fa fn fc snil = fn` — the `snil` recursor equation.
pub fn rec_snil(fa: Term, fnil: Term, fc: Term) -> Result<Thm> {
    let lhs = rec(fa.clone(), fnil.clone(), fc.clone(), snil())?;
    prove_rec_eq(lhs, fnil)
}

/// `⊢ rec fa fn fc (scons h t) = fc (rec fa fn fc h) (rec fa fn fc t)` —
/// the `scons` recursor equation. The recursive calls on `h` and `t` are
/// exactly the folds the encoding plugs in.
pub fn rec_scons(fa: Term, fnil: Term, fc: Term, h: Term, t: Term) -> Result<Thm> {
    let lhs = rec(
        fa.clone(),
        fnil.clone(),
        fc.clone(),
        scons(h.clone(), t.clone()),
    )?;
    let rec_h = rec(fa.clone(), fnil.clone(), fc.clone(), h)?;
    let rec_t = rec(fa.clone(), fnil.clone(), fc.clone(), t)?;
    let rhs = fc.apply(rec_h)?.apply(rec_t)?;
    prove_rec_eq(lhs, rhs)
}

/// `⊢ lhs = rhs` by β-normalising `lhs` and checking it lands on `rhs`.
fn prove_rec_eq(lhs: Term, rhs: Term) -> Result<Thm> {
    // The recursor equations are pure β-conversions: normalise lhs.
    let conv = crate::init::eq::beta_nf(lhs.clone()); // ⊢ lhs = nf
    let nf = conv.concl().as_eq().expect("beta_nf equation").1.clone();
    let rhs_conv = crate::init::eq::beta_nf(rhs.clone()); // ⊢ rhs = nf'
    if nf == *rhs_conv.concl().as_eq().expect("eq").1 {
        // lhs = nf = nf' = rhs
        conv.trans(rhs_conv.sym()?)
    } else {
        Err(covalence_core::Error::ConnectiveRule(format!(
            "rec equation: lhs normalises to `{nf}`, expected `{rhs}`"
        )))
    }
}

// ============================================================================
// Structural induction — via the inductive-types API bundle
// ============================================================================

/// `⊢ (∀b. P (atom b)) ⟹ P snil ⟹ (∀h t. P h ⟹ P t ⟹ P (scons h t))
///      ⟹ ∀s. P s` is **not** derivable for the bare Church encoding
/// without a wellformedness side condition (junk terms inhabit `S⟨'r⟩`).
///
/// The *membership-relativized* form **is** now available: the
/// [`sexpr_theory`] bundle carries the well-formedness predicate
/// `Wf := λs. ∀d. Closed d ⟹ d s` as its `mem`, and its
/// `facts.induct(motive, cases)` concludes `⊢ ∀s. Wf s ⟹ motive s` — the
/// honest form for this encoding (the bare-type statement is false at
/// collapsing instances of `'r`). Downstream impredicative soundness
/// proofs ([`crate::init::prop::soundness`]) still only need the recursor
/// equations above.
pub fn induct_note() {}

// ============================================================================
// The inductive-types API realization (the flagship bundle)
// ============================================================================

use covalence_inductive::{ArgSort, CtorSpec, InductiveBackend, InductiveSpec, InductiveTheory};

use crate::init::inductive::ImpredicativeBackend;
use crate::init::inductive::hol::NativeHol;

/// The `sexpr` spec: `sexpr := atom bytes | snil | scons sexpr sexpr`.
pub fn sexpr_spec() -> InductiveSpec<Type> {
    InductiveSpec::new(
        "sexpr",
        vec![
            CtorSpec::new("atom", [("b", ArgSort::Ext(bytes()))]),
            CtorSpec::nullary("snil"),
            CtorSpec::new("scons", [("h", ArgSort::Rec), ("t", ArgSort::Rec)]),
        ],
    )
}

/// The impredicative backend configured to reproduce **this module's
/// encoding exactly** (same handler binder names, same `'r`), so the
/// bundle's constructors β-agree with [`atom`]/[`snil`]/[`scons`] and its
/// carrier *is* [`sexpr_ty`].
pub fn sexpr_backend() -> ImpredicativeBackend {
    ImpredicativeBackend::new().with_handler_names(["fa", "fn_", "fc"])
}

/// The `sexpr` theory bundle through the inductive-types API:
/// constructors, recursor computation laws (β), freeness (distinctness +
/// `atom`-payload injectivity), the `Wf` membership predicate, and genuine
/// `Wf`-relativized induction/cases — everything this module provides plus
/// the induction machinery it historically deferred.
pub fn sexpr_theory() -> Result<InductiveTheory<NativeHol>> {
    sexpr_backend()
        .realize(&NativeHol, &sexpr_spec())
        .map_err(|e| covalence_core::Error::ConnectiveRule(format!("sexpr_theory: {e}")))
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Concrete result type for testing the recursor equations.
    fn nat_r() -> Type {
        Type::nat()
    }

    /// The three constructors build well-typed `S⟨'r⟩` values, distinct
    /// as terms (genuine syntax, not collapsed to a meaning).
    #[test]
    fn constructors_typed_and_distinct() {
        let b = covalence_hol_eval::mk_blob(covalence_types::Bytes::from(vec![1u8, 2, 3]));
        let at = atom(b.clone());
        assert_eq!(at.type_of().unwrap(), sexpr_ty());
        assert_eq!(snil().type_of().unwrap(), sexpr_ty());
        let sc = scons(at.clone(), snil());
        assert_eq!(sc.type_of().unwrap(), sexpr_ty());
        assert_ne!(at, snil());
        assert_ne!(at, sc);
        assert_ne!(snil(), sc);
    }

    /// `slist` nests `scons` over `snil`, and is typed.
    #[test]
    fn slist_nests_scons() {
        let a0 = atom(covalence_hol_eval::mk_blob(covalence_types::Bytes::from(
            vec![0u8],
        )));
        let a1 = atom(covalence_hol_eval::mk_blob(covalence_types::Bytes::from(
            vec![1u8],
        )));
        let built = slist(vec![a0.clone(), a1.clone()]);
        assert_eq!(built, scons(a0, scons(a1, snil())));
        assert_eq!(built.type_of().unwrap(), sexpr_ty());
    }

    /// Test handlers at `'r := nat`: `fa = λb. 0`, `fn = 0`,
    /// `fc = λx y. succ y` (counts list length, ignoring atoms).
    fn handlers_count() -> (Term, Term, Term) {
        let bytes = Type::bytes();
        // fa = λ_:bytes. 0
        let fa = Term::abs(
            bytes,
            covalence_hol_eval::mk_nat(covalence_types::Nat::from_inner(0u32.into())),
        );
        // fn = 0
        let fnil = covalence_hol_eval::mk_nat(covalence_types::Nat::from_inner(0u32.into()));
        // fc = λx y:nat. succ y
        let y = Term::free("y", nat_r());
        let succ_y = Term::app(covalence_hol_eval::defs::nat_succ(), y.clone());
        let inner = Term::abs(nat_r(), covalence_core::subst::close(&succ_y, "y"));
        let fc = Term::abs(nat_r(), inner); // x ignored
        (fa, fnil, fc)
    }

    /// `rec fa fn fc snil = fn` — proved (β), genuine.
    #[test]
    fn rec_snil_holds() {
        let (fa, fnil, fc) = handlers_count();
        let thm = rec_snil(fa, fnil.clone(), fc).unwrap();
        assert!(thm.hyps().is_empty());
        assert_eq!(thm.concl().as_eq().unwrap().1, &fnil);
    }

    /// `rec fa fn fc (atom b) = fa b` — proved (β), genuine.
    #[test]
    fn rec_atom_holds() {
        let (fa, fnil, fc) = handlers_count();
        let b = covalence_hol_eval::mk_blob(covalence_types::Bytes::from(vec![7u8]));
        let thm = rec_atom(fa.clone(), fnil, fc, b.clone()).unwrap();
        assert!(thm.hyps().is_empty());
        // rhs = fa b, which β-reduces to 0; we only check the equation holds.
        let (lhs, _) = thm.concl().as_eq().unwrap();
        assert_eq!(
            lhs,
            &rec(
                fa.clone(),
                covalence_hol_eval::mk_nat(covalence_types::Nat::from_inner(0u32.into())),
                {
                    let (_, _, fc2) = handlers_count();
                    fc2
                },
                atom(b)
            )
            .unwrap()
        );
    }

    /// `rec fa fn fc (scons h t) = fc (rec … h) (rec … t)` — proved (β).
    #[test]
    fn rec_scons_holds() {
        let (fa, fnil, fc) = handlers_count();
        let h = atom(covalence_hol_eval::mk_blob(covalence_types::Bytes::from(
            vec![1u8],
        )));
        let t = snil();
        let thm = rec_scons(fa, fnil, fc, h, t).unwrap();
        assert!(thm.hyps().is_empty());
        assert!(thm.concl().as_eq().is_some());
    }

    /// End-to-end: the length of `[atom, atom]` computes to `2` through
    /// the recursor equations + βι reduction.
    #[test]
    fn length_of_two_element_list_is_two() {
        use crate::init::ext::TermExt;
        let (fa, fnil, fc) = handlers_count();
        let a0 = atom(covalence_hol_eval::mk_blob(covalence_types::Bytes::from(
            vec![0u8],
        )));
        let a1 = atom(covalence_hol_eval::mk_blob(covalence_types::Bytes::from(
            vec![1u8],
        )));
        let lst = slist(vec![a0, a1]);
        let len = rec(fa, fnil, fc, lst).unwrap();
        // βι-normalise: should reduce to the literal 2.
        let conv = len.reduce().unwrap();
        let rhs = conv.concl().as_eq().unwrap().1.clone();
        assert_eq!(
            rhs,
            covalence_hol_eval::mk_nat(covalence_types::Nat::from_inner(2u32.into()))
        );
    }
}

#[cfg(test)]
mod bundle_tests {
    use super::*;
    use crate::init::eq::beta_nf;
    use covalence_inductive::{InductiveError, conformance};
    use covalence_types::Bytes;

    fn blob(bs: &[u8]) -> Term {
        covalence_hol_eval::mk_blob(Bytes::from(bs.to_vec()))
    }

    /// The bundle's carrier is exactly this module's `S⟨'r⟩`.
    #[test]
    fn bundle_carrier_is_sexpr_ty() {
        let th = sexpr_theory().unwrap();
        assert_eq!(th.ty, sexpr_ty());
    }

    /// The bundle's constructors β-reduce to this module's hand-rolled
    /// encodings — `init/sexpr.rs` facts bridge over verbatim.
    #[test]
    fn bundle_ctors_bridge_to_hand_rolled() {
        let th = sexpr_theory().unwrap();
        let b = Term::free("b", bytes());
        let h = Term::free("h", sexpr_ty());
        let t = Term::free("t", sexpr_ty());

        // β-nf of the applied bundle constructor = the reduced hand form.
        let check = |applied: Term, reduced: Term| {
            let conv = beta_nf(applied); // ⊢ applied = nf
            let nf = conv.concl().as_eq().unwrap().1.clone();
            let rconv = beta_nf(reduced);
            assert_eq!(&nf, rconv.concl().as_eq().unwrap().1);
        };
        check(Term::app(th.ctors[0].clone(), b.clone()), atom(b));
        check(th.ctors[1].clone(), snil());
        check(
            Term::app(Term::app(th.ctors[2].clone(), h.clone()), t.clone()),
            scons(h, t),
        );
    }

    /// The full conformance suite (comp/induct/mem/distinct) passes — the
    /// genuine `Wf`-relativized induction the module historically deferred.
    #[test]
    fn bundle_conformance() {
        let th = sexpr_theory().unwrap();
        conformance::check_theory(&crate::init::inductive::hol::NativeHol, &th, &Type::nat())
            .unwrap();
    }

    /// Membership: `⊢ Wf (scons (atom b) snil)` assembled bottom-up from
    /// `mem_ctor`, hypothesis-free.
    #[test]
    fn wf_of_concrete_sexpr() {
        let th = sexpr_theory().unwrap();
        let b = blob(&[7]);
        let atom_t = Term::app(th.ctors[0].clone(), b.clone());
        let wa = th.facts.mem_ctor(0, &[b], vec![]).unwrap();
        let ws = th.facts.mem_ctor(1, &[], vec![]).unwrap();
        let m = th
            .facts
            .mem_ctor(2, &[atom_t.clone(), th.ctors[1].clone()], vec![wa, ws])
            .unwrap();
        assert!(m.hyps().is_empty());
        let expected = Term::app(
            th.mem.clone(),
            Term::app(Term::app(th.ctors[2].clone(), atom_t), th.ctors[1].clone()),
        );
        assert_eq!(m.concl(), &expected);
    }

    /// Freeness: distinctness between all constructor pairs and
    /// `atom`-payload injectivity are genuine theorems; injectivity at the
    /// recursive `scons` positions reports the documented capability gap.
    #[test]
    fn freeness_facts() {
        let th = sexpr_theory().unwrap();
        let b = Term::free("b", bytes());
        let b2 = Term::free("b2", bytes());
        let h = Term::free("h", sexpr_ty());
        let t = Term::free("t", sexpr_ty());

        for (i, j, xs, ys) in [
            (0usize, 1usize, vec![b.clone()], vec![]),
            (0, 2, vec![b.clone()], vec![h.clone(), t.clone()]),
            (1, 2, vec![], vec![h.clone(), t.clone()]),
        ] {
            let d = th.facts.distinct(i, j, &xs, &ys).unwrap();
            assert!(d.hyps().is_empty(), "distinct({i},{j}) must be closed");
        }

        let inj = th
            .facts
            .injective(0, 0, std::slice::from_ref(&b), std::slice::from_ref(&b2))
            .unwrap();
        assert!(inj.hyps().is_empty());
        // Conclusion ends in `b = b2`.
        let (_, concl_rhs) = inj.concl().as_app().unwrap();
        assert_eq!(concl_rhs, &b.clone().equals(b2).unwrap());

        assert!(matches!(
            th.facts.injective(2, 0, &[h.clone(), t.clone()], &[t, h]),
            Err(InductiveError::Unsupported { .. })
        ));
        assert!(!th.facts.caps().rec_injective);
    }

    /// Exhaustiveness through the bundle: `⊢ ∀s. Wf s ⟹ (∃b. s = atom b)
    /// ∨ (s = snil ∨ ∃h t. s = scons h t)` — a real theorem now.
    #[test]
    fn cases_theorem() {
        let th = sexpr_theory().unwrap();
        let c = th.facts.cases().unwrap();
        assert!(c.hyps().is_empty());
        assert!(c.concl().type_of().unwrap().is_bool());
    }
}
