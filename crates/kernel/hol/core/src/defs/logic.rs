//! The propositional connectives and quantifiers, as ordinary
//! `defs/` definitions over the two logical primitives `=`
//! ([`crate::TermKind::Eq`]) and `ε` ([`crate::TermKind::Select`]).
//!
//! This is the HOL Light bootstrap (`bool.ml`) expressed in the
//! catalogue: every connective is a let-style [`TermSpec`] whose body
//! is the standard definition. Two consequences follow for free:
//!
//! - [`crate::Thm::unfold_term_spec`] hands back the defining equation
//!   `⊢ c = <body>` — the same way it does for `natAdd` — so the
//!   connectives' introduction / elimination rules are *derived*
//!   downstream, never postulated.
//! - the derivations are ordinary equality reasoning, so the whole
//!   calculus lives at the pure `CoreLang` tier (no certificate rule
//!   ever destructures a connective).
//!
//! `T` / `F` are the **defined constants** [`tru`] / [`fal`] (EG3b):
//! `tru ≡ (λp:bool.p) = (λp:bool.p)` and `fal ≡ ∀p:bool. p`, and the
//! connective bodies below reference *them*, so the whole derived
//! connective calculus (`covalence-hol-eval::derived`) bottoms out in a
//! `⊢ tru` derivable at the pure `CoreLang` tier — no certificate.
//! The transitional `TermKind::Bool` literals `⌜T⌝`/`⌜F⌝` still exist
//! (the closed-computation certificate path produces them, e.g.
//! `⊢ (2+2=4) = ⌜T⌝`) and are bridged to the defined constants by
//! *derived* eval-tier theorems (`⊢ tru = ⌜T⌝`, `⊢ fal = ⌜F⌝` in
//! `covalence-hol-eval::boolean`) until the literal-leaf endgame (EG5)
//! deletes them.
//!
//! ## Definition order
//!
//! The bodies reference each other, so the `LazyLock`s force in
//! dependency order (acyclic):
//!
//! ```text
//! tru          ←  (=)            (no deps)
//! and, forall  ←  (=, tru)
//! imp          ←  and
//! fal          ←  forall
//! not          ←  imp, fal
//! or, exists   ←  forall, imp
//! iff          ←  (=)
//! ```
//!
//! Since stage L2 NO kernel rule destructures these definitions — the
//! connective / quantifier intro-elim rules are executable derivations
//! in `covalence-hol-eval::derived`. The staying axiom rules
//! (`succ_eq_elim`, `select_intro`, `spec_intro`, the `spec_*` subtype laws,
//! `new_type_definition`) still *state* their conclusions with `imp` /
//! `not` / `or` / `exists` / `and` / `forall`, and the D3 residue type
//! catalogue quantifies with them — which is exactly why these
//! definitions are still core residue rather than eval catalogue: they
//! move out with the literal-leaf endgame (see the generated open-work index).

use crate::hol;
use crate::term::{Term, Type};

use super::canonical::Canonical;

// ============================================================================
// Helpers
// ============================================================================

fn b() -> Type {
    Type::bool()
}

/// `p ⟹ q` built from the `imp` spec (for use inside the bodies that
/// need implication before the local `hol_imp` would be circular-safe).
fn imp_app(p: Term, q: Term) -> Term {
    Term::app(Term::app(imp(), p), q)
}

// ============================================================================
// tru — `(λp:bool. p) = (λp:bool. p)`  (HOL Light `T_DEF`)
// ============================================================================

fn tru_body() -> Term {
    // λp:bool. p
    let p = Term::free("p", b());
    let id = hol::pub_abs("p", b(), p);
    hol::hol_eq(id.clone(), id)
}

let_term! {
    /// `T : bool` ≡ `(λp:bool. p) = (λp:bool. p)` — truth as a defined
    /// constant. `⊢ T` is derivable at the pure `CoreLang` tier
    /// (δ-unfold + `refl` + `eq_mp`), with no certificate.
    tru_spec, tru, Canonical::True, tru_body()
}

// ============================================================================
// and — `λp q. (λf. f p q) = (λf. f T T)`
// ============================================================================

fn and_body() -> Term {
    // `f : bool → bool → bool`
    let bbb = Type::fun(b(), Type::fun(b(), b()));
    let p = Term::free("p", b());
    let q = Term::free("q", b());
    let f = Term::free("f", bbb.clone());

    // λf. f p q
    let f_p_q = Term::app(Term::app(f.clone(), p.clone()), q.clone());
    let lhs = hol::pub_abs("f", bbb.clone(), f_p_q);
    // λf. f T T  (the DEFINED T)
    let f_t_t = Term::app(Term::app(f, tru()), tru());
    let rhs = hol::pub_abs("f", bbb, f_t_t);

    let eq = hol::hol_eq(lhs, rhs);
    hol::pub_abs("p", b(), hol::pub_abs("q", b(), eq))
}

let_term! {
    /// `(/\) : bool → bool → bool` ≡ `λp q. (λf. f p q) = (λf. f T T)`.
    and_spec, and, Canonical::And, and_body()
}

// ============================================================================
// imp — `λp q. (p /\ q) = p`
// ============================================================================

fn imp_body() -> Term {
    let p = Term::free("p", b());
    let q = Term::free("q", b());
    let and_pq = Term::app(Term::app(and(), p.clone()), q.clone());
    let eq = hol::hol_eq(and_pq, p.clone());
    hol::pub_abs("p", b(), hol::pub_abs("q", b(), eq))
}

let_term! {
    /// `(==>) : bool → bool → bool` ≡ `λp q. (p /\ q) = p`.
    imp_spec, imp, Canonical::Imp, imp_body()
}

// ============================================================================
// not — `λp. p ==> F`
// ============================================================================

fn not_body() -> Term {
    let p = Term::free("p", b());
    let body = imp_app(p.clone(), fal());
    hol::pub_abs("p", b(), body)
}

let_term! {
    /// `(~) : bool → bool` ≡ `λp. p ==> F`.
    not_spec, not, Canonical::Not, not_body()
}

// ============================================================================
// iff — `λp q. p = q`
// ============================================================================

fn iff_body() -> Term {
    let p = Term::free("p", b());
    let q = Term::free("q", b());
    let eq = hol::hol_eq(p.clone(), q.clone());
    hol::pub_abs("p", b(), hol::pub_abs("q", b(), eq))
}

let_term! {
    /// `(<=>) : bool → bool → bool` ≡ `λp q. p = q`.
    iff_spec, iff, Canonical::Iff, iff_body()
}

// ============================================================================
// forall — `λP. P = (λx. T)`
// ============================================================================

fn forall_body() -> Term {
    let alpha = Type::tfree("a");
    let pred_ty = Type::fun(alpha.clone(), b());
    let pred = Term::free("P", pred_ty.clone());
    // λx:α. T  (the DEFINED T; x unused; `pub_abs` close is a no-op but keeps shape)
    let lam_x = hol::pub_abs("x", alpha, tru());
    let eq = hol::hol_eq(pred, lam_x);
    hol::pub_abs("P", pred_ty, eq)
}

poly_let_term! {
    /// `(!) : ('a → bool) → bool` ≡ `λP. P = (λx. T)`.
    forall_spec, forall(alpha), Canonical::Forall, forall_body()
}

// ============================================================================
// fal — `∀p:bool. p`  (HOL Light `F_DEF`)
// ============================================================================

fn fal_body() -> Term {
    let p = Term::free("p", b());
    hol_forall("p", b(), p)
}

let_term! {
    /// `F : bool` ≡ `∀p:bool. p` — falsity as a defined constant.
    /// Ex falso is a *derivation* (`unfold` + `∀`-elim at the target),
    /// not a kernel rule.
    fal_spec, fal, Canonical::False, fal_body()
}

// ============================================================================
// or — `λp q. !r. (p ==> r) ==> (q ==> r) ==> r`
// ============================================================================

fn or_body() -> Term {
    let p = Term::free("p", b());
    let q = Term::free("q", b());
    let r = Term::free("r", b());
    let p_r = imp_app(p.clone(), r.clone());
    let q_r = imp_app(q.clone(), r.clone());
    let inner = imp_app(p_r, imp_app(q_r, r.clone()));
    let forall_r = hol_forall("r", b(), inner);
    hol::pub_abs("p", b(), hol::pub_abs("q", b(), forall_r))
}

let_term! {
    /// `(\/) : bool → bool → bool` ≡
    /// `λp q. !r. (p ==> r) ==> (q ==> r) ==> r`.
    or_spec, or, Canonical::Or, or_body()
}

// ============================================================================
// exists — `λP. !q. (!x. P x ==> q) ==> q`
// ============================================================================

fn exists_body() -> Term {
    let alpha = Type::tfree("a");
    let pred_ty = Type::fun(alpha.clone(), b());
    let pred = Term::free("P", pred_ty.clone());
    let q = Term::free("q", b());
    let x = Term::free("x", alpha.clone());
    let p_x = Term::app(pred.clone(), x);
    let p_x_q = imp_app(p_x, q.clone());
    let inner_forall = hol_forall("x", alpha, p_x_q);
    let imp2 = imp_app(inner_forall, q.clone());
    let forall_q = hol_forall("q", b(), imp2);
    hol::pub_abs("P", pred_ty, forall_q)
}

poly_let_term! {
    /// `(?) : ('a → bool) → bool` ≡ `λP. !q. (!x. P x ==> q) ==> q`.
    exists_spec, exists(alpha), Canonical::Exists, exists_body()
}

// ============================================================================
// Defined-connective term builders (crate-internal, stage A3)
// ============================================================================
//
// Application-chain sugar over the catalogue specs above. These moved
// here from `crate::hol` (which is now `defs`-free): they belong next to
// the definitions they apply, and they die together at the literal-leaf
// endgame. Crate-internal consumers: the D3 residue bodies in `defs/*.rs`
// and the two staying connective-built rules (`SpecRepAbsBack`,
// `NewTypeDefRule`). Everyone else uses the public copies in
// `covalence-hol-eval::hol` (the untrusted home).

/// HOL `p ⟹ q : bool` — `imp` applied to `p` and `q`.
pub(crate) fn hol_imp(p: Term, q: Term) -> Term {
    imp_app(p, q)
}

/// HOL `p ∧ q : bool`.
pub(crate) fn hol_and(p: Term, q: Term) -> Term {
    Term::app(Term::app(and(), p), q)
}

/// HOL `p ∨ q : bool`.
pub(crate) fn hol_or(p: Term, q: Term) -> Term {
    Term::app(Term::app(or(), p), q)
}

/// HOL `¬ p : bool` — `not` applied to `p`.
pub(crate) fn hol_not(p: Term) -> Term {
    Term::app(not(), p)
}

/// HOL `∃x:α. body[x]` — `exists[α] (λx:α. body[Bound 0])`.
pub(crate) fn hol_exists(hint: &str, alpha: Type, body: Term) -> Term {
    Term::app(exists(alpha.clone()), hol::pub_abs(hint, alpha, body))
}

/// HOL `∀x:α. body[x]` — `forall[α] (λx:α. body[Bound 0])`. The free
/// variable `Free(hint, α)` in `body` is closed into `Bound(0)`.
pub(crate) fn hol_forall(hint: &str, alpha: Type, body: Term) -> Term {
    Term::app(forall(alpha.clone()), hol::pub_abs(hint, alpha, body))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::TermKind;

    /// Pin the pure tier: `Thm<CoreLang>` unit tests (stage E1).
    type Thm = crate::Thm;

    fn bin() -> Type {
        Type::fun(b(), Type::fun(b(), b()))
    }

    #[test]
    fn connectives_have_expected_types() {
        assert_eq!(tru().type_of().unwrap(), b());
        assert_eq!(fal().type_of().unwrap(), b());
        assert_eq!(and().type_of().unwrap(), bin());
        assert_eq!(or().type_of().unwrap(), bin());
        assert_eq!(imp().type_of().unwrap(), bin());
        assert_eq!(iff().type_of().unwrap(), bin());
        assert_eq!(not().type_of().unwrap(), Type::fun(b(), b()));
        // `!` / `?` at α: (α → bool) → bool.
        let a = Type::tfree("x");
        let quant = Type::fun(Type::fun(a.clone(), b()), b());
        assert_eq!(forall(a.clone()).type_of().unwrap(), quant);
        assert_eq!(exists(a).type_of().unwrap(), quant);
    }

    /// The whole point of making the connectives `defs/` specs: each
    /// one unfolds to its standard definition via `unfold_term_spec`
    /// — no postulate, sound by the let-style denotation. This is the
    /// hook downstream `covalence-hol` uses to *derive* the connective
    /// rules.
    #[test]
    fn connectives_unfold_to_their_definitions() {
        for op in [tru(), fal(), and(), or(), imp(), iff(), not()] {
            let thm = Thm::unfold_term_spec(op.clone()).unwrap();
            // `⊢ op = <body>`: empty hyps, conclusion is an equation
            // whose LHS is the connective itself.
            assert!(thm.hyps().is_empty(), "unfold must be axiom-free");
            let TermKind::App(eq_lhs, _body) = thm.concl().kind() else {
                panic!("unfold concl not an application: {:?}", thm.concl());
            };
            let TermKind::App(eq_head, lhs) = eq_lhs.kind() else {
                panic!("unfold concl LHS not an application");
            };
            assert!(matches!(eq_head.kind(), TermKind::Eq(_)));
            assert_eq!(lhs, &op);
        }
    }

    /// `⊢ T` for the **defined** `T`, at the pure `CoreLang` tier — the
    /// EG3b keystone: the δ-unfold gives `⊢ T = ((λp.p) = (λp.p))`,
    /// `refl` gives the right-hand side, and `eq_mp` (backwards through
    /// `sym`) concludes. No certificate, no computation TCB, no axiom.
    #[test]
    fn defined_truth_derives_at_core_lang() {
        let def = Thm::unfold_term_spec(tru()).unwrap(); // ⊢ T = ((λp.p) = (λp.p))
        let rhs = def.concl().as_eq().unwrap().1.clone();
        // `rhs` is itself the equation `(λp.p) = (λp.p)`; `refl` on its
        // left side rebuilds it as a THEOREM.
        let id_lambda = rhs.as_eq().unwrap().0.clone();
        let refl = Thm::refl(id_lambda).unwrap(); // ⊢ (λp.p) = (λp.p)
        assert_eq!(refl.concl(), &rhs);
        let truth = def.sym().unwrap().eq_mp(refl).unwrap(); // ⊢ T
        assert!(truth.hyps().is_empty());
        assert_eq!(truth.concl(), &tru());
    }

    #[test]
    fn polymorphic_connectives_unfold() {
        for op in [forall(Type::nat()), exists(Type::nat())] {
            let thm = Thm::unfold_term_spec(op.clone()).unwrap();
            assert!(thm.hyps().is_empty());
            let TermKind::App(eq_lhs, _body) = thm.concl().kind() else {
                panic!("unfold concl not an application");
            };
            let TermKind::App(eq_head, lhs) = eq_lhs.kind() else {
                panic!("unfold concl LHS not an application");
            };
            assert!(matches!(eq_head.kind(), TermKind::Eq(_)));
            assert_eq!(lhs, &op);
        }
    }
}
