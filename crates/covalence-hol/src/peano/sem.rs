//! **The two-sorted Church/HOAS semantic carrier** for PA — the
//! re-packaging that makes the impredicative soundness theorem
//! (`⊢ Derivable_PA ⌜A⌝ ⟹ ⟦A⟧`) provable, exactly the way
//! [`crate::init::prop`] proves `⊢ Derivable_Prop A ⟹ ⟦A⟧ v`.
//!
//! ## Why a *second* carrier, and why two-sorted
//!
//! [`super::fol`] reifies PA syntax as a single-sorted, locally-nameless
//! Church carrier `Φ⟨'r⟩` (terms and formulas both fold into one `'r`, bound
//! variables are de Bruijn `bvar` calls). That carrier is perfect for
//! *syntax* — the substitution laws live there — but it **cannot be the
//! `inst`-target of the impredicative soundness proof**, for two reasons:
//!
//! 1. **PA is two-sorted** (terms denote into `nat`, formulas into `bool`),
//!    so `eq : 'r → 'r → 'r` is unsatisfiable at a single instance: at
//!    `'r := bool` the term layer breaks, at `'r := nat` the formula layer
//!    breaks. The fold needs **two** result-type variables — `'t` for terms,
//!    `'r` for formulas — so it can be pinned at `'t := nat, 'r := bool`.
//! 2. **Quantifiers need HOAS, not de Bruijn**, to *denote*. A de Bruijn
//!    `all : 'r → 'r` receives an already-folded body in which the bound
//!    variable was collapsed by the `bvar` handler — there is no value left to
//!    range over, so it cannot become a real HOL `∀`. Making `all`'s argument
//!    a **function** `('t → 'r) → 'r` (higher-order abstract syntax) lets the
//!    denotation re-bind it with a genuine HOL `∀x:nat. …`.
//!
//! So here we add the *semantic* carrier `Φ_sem⟨'t,'r⟩` (formulas) /
//! `Θ_sem⟨'t,'r⟩` (terms) with HOAS quantifiers, plus an encoder
//! [`SemFol::encode_form`] that lowers the locally-nameless [`super::fol::Fol`]
//! AST into it (de Bruijn → HOAS). The **denotation** `⟦A⟧` is then literally
//! *the encoded formula applied to the standard `nat`/`bool` handlers*, a
//! single fold — which is what lets the soundness proof `inst` the predicate
//! variable `d := ⟦·⟧` and β-reduce, exactly as `prop.rs` does.
//!
//! Nothing here is added to `covalence-core`: every handler is built from the
//! kernel's existing `nat` operations and `bool` connectives.

use covalence_core::subst::close;
use covalence_core::{Term, Type, defs};
use covalence_types::Nat;

use super::fol::Fol;
use crate::init::ext::TermExt;

// ============================================================================
// The two result-type variables + the handler signature
// ============================================================================

/// The term result-type variable `'t`.
pub fn tty() -> Type {
    Type::tfree("t")
}

/// The formula result-type variable `'r`.
pub fn rty() -> Type {
    Type::tfree("r")
}

fn nat() -> Type {
    Type::nat()
}

/// The handler binder names + their slot-type builders, in fold order. Each
/// slot is parametric in the term result `t` and the formula result `r`.
///
/// | slot   | type             | sort                          |
/// |--------|------------------|-------------------------------|
/// | `fvar` | `nat → 't`       | free variable atom            |
/// | `zero` | `'t`             | constant `0`                  |
/// | `succ` | `'t → 't`        | successor                     |
/// | `add`  | `'t → 't → 't`   | `+`                           |
/// | `mul`  | `'t → 't → 't`   | `·`                           |
/// | `eq`   | `'t → 't → 'r`   | atomic `=` (term→term→formula)|
/// | `neg`  | `'r → 'r`        | `¬`                           |
/// | `and`  | `'r → 'r → 'r`   | `∧`                           |
/// | `or`   | `'r → 'r → 'r`   | `∨`                           |
/// | `imp`  | `'r → 'r → 'r`   | `⟹`                           |
/// | `all`  | `('t → 'r) → 'r` | `∀` (HOAS body)               |
/// | `ex`   | `('t → 'r) → 'r` | `∃` (HOAS body)               |
pub const HANDLERS: [(&str, fn(&Type, &Type) -> Type); 12] = [
    ("fvar", |t, _r| Type::fun(nat(), t.clone())),
    ("zero", |t, _r| t.clone()),
    ("succ", |t, _r| Type::fun(t.clone(), t.clone())),
    ("add", |t, _r| {
        Type::fun(t.clone(), Type::fun(t.clone(), t.clone()))
    }),
    ("mul", |t, _r| {
        Type::fun(t.clone(), Type::fun(t.clone(), t.clone()))
    }),
    ("eq", |t, r| {
        Type::fun(t.clone(), Type::fun(t.clone(), r.clone()))
    }),
    ("neg", |_t, r| Type::fun(r.clone(), r.clone())),
    ("and", |_t, r| {
        Type::fun(r.clone(), Type::fun(r.clone(), r.clone()))
    }),
    ("or", |_t, r| {
        Type::fun(r.clone(), Type::fun(r.clone(), r.clone()))
    }),
    ("imp", |_t, r| {
        Type::fun(r.clone(), Type::fun(r.clone(), r.clone()))
    }),
    ("all", |t, r| {
        Type::fun(Type::fun(t.clone(), r.clone()), r.clone())
    }),
    ("ex", |t, r| {
        Type::fun(Type::fun(t.clone(), r.clone()), r.clone())
    }),
];

/// The slot type of handler `name` at `('t, 'r)`.
fn handler_ty(name: &str, t: &Type, r: &Type) -> Type {
    HANDLERS
        .iter()
        .find(|(n, _)| *n == name)
        .map(|(_, f)| f(t, r))
        .expect("sem: unknown handler name")
}

/// A free handler variable by name, at `('t, 'r)`.
pub fn handler(t: &Type, r: &Type, name: &str) -> Term {
    Term::free(name, handler_ty(name, t, r))
}

/// `Φ_sem⟨t,r⟩ = (fvar)→…→(ex)→r` — a **formula** at result types `(t, r)`.
pub fn phi_at(t: &Type, r: &Type) -> Type {
    let mut acc = r.clone();
    for (name, _) in HANDLERS.iter().rev() {
        acc = Type::fun(handler_ty(name, t, r), acc);
    }
    acc
}

/// `Θ_sem⟨t,r⟩ = (fvar)→…→(ex)→t` — a **term** at result types `(t, r)`.
pub fn theta_at(t: &Type, r: &Type) -> Type {
    let mut acc = t.clone();
    for (name, _) in HANDLERS.iter().rev() {
        acc = Type::fun(handler_ty(name, t, r), acc);
    }
    acc
}

/// `Φ_sem⟨'t,'r⟩` — the polymorphic formula carrier.
pub fn phi() -> Type {
    phi_at(&tty(), &rty())
}

/// `Φ_sem⟨nat,bool⟩` — the formula carrier pinned at the denotation instance.
pub fn phi_at_std() -> Type {
    phi_at(&nat(), &Type::bool())
}

/// `λfvar zero … ex. body` — wrap a fold `body` in the twelve handler
/// abstractions. The result is a `Φ_sem`/`Θ_sem` value depending on `body`'s
/// type.
fn close_handlers(t: &Type, r: &Type, body: Term) -> Term {
    let mut acc = body;
    for (name, _) in HANDLERS.iter().rev() {
        acc = Term::abs(handler_ty(name, t, r), close(&acc, name));
    }
    acc
}

// ============================================================================
// The encoder: locally-nameless `Fol` → HOAS semantic carrier
//
// We carry a Rust `Vec<Term>` of the HOAS-bound HOL variables the enclosing
// quantifiers introduced (each of type `'t`), innermost last. `BVar i` reads
// the `i`-th from the top. A quantifier introduces a fresh HOL free variable
// of type `'t`, encodes the body under it, then HOL-`close`s it into a real
// `λ` fed to the `all`/`ex` handler — turning de Bruijn into HOAS.
// ============================================================================

/// A reified PA formula/term lowered into the semantic carrier. The wrapper
/// keeps the result-type pair `('t, 'r)` so the encoder threads them.
struct SemFol<'a> {
    t: &'a Type,
    r: &'a Type,
}

impl<'a> SemFol<'a> {
    /// Encode a **term** node into a fold body `: 't` (un-wrapped). `ctx` holds
    /// the enclosing HOAS-bound HOL variables (innermost last).
    fn term_body(&self, f: &Fol, ctx: &[Term]) -> Term {
        match f {
            Fol::BVar(i) => {
                let n = ctx.len();
                let idx = *i as usize;
                assert!(idx < n, "sem: dangling BVar {i} (ctx depth {n})");
                ctx[n - 1 - idx].clone()
            }
            Fol::FVar(k) => Term::app(self.h("fvar"), Term::nat_lit(Nat::from_inner((*k).into()))),
            Fol::Zero => self.h("zero"),
            Fol::Succ(a) => Term::app(self.h("succ"), self.term_body(a, ctx)),
            Fol::Add(a, b) => self.bin_t("add", a, b, ctx),
            Fol::Mul(a, b) => self.bin_t("mul", a, b, ctx),
            _ => panic!("sem::term_body: formula node where a term was expected"),
        }
    }

    /// Encode a **formula** node into a fold body `: 'r` (un-wrapped).
    fn form_body(&self, f: &Fol, ctx: &[Term]) -> Term {
        match f {
            Fol::Eq(a, b) => Term::app(
                Term::app(self.h("eq"), self.term_body(a, ctx)),
                self.term_body(b, ctx),
            ),
            Fol::Neg(a) => Term::app(self.h("neg"), self.form_body(a, ctx)),
            Fol::And(a, b) => self.bin_f("and", a, b, ctx),
            Fol::Or(a, b) => self.bin_f("or", a, b, ctx),
            Fol::Imp(a, b) => self.bin_f("imp", a, b, ctx),
            Fol::All(body) => Term::app(self.h("all"), self.hoas(body, ctx)),
            Fol::Ex(body) => Term::app(self.h("ex"), self.hoas(body, ctx)),
            _ => panic!("sem::form_body: term node where a formula was expected"),
        }
    }

    /// `λx:'t. ⟪body⟫` — the HOAS body for a quantifier: introduce a fresh HOL
    /// `'t`-variable, encode the body with it pushed on `ctx`, close it.
    fn hoas(&self, body: &Fol, ctx: &[Term]) -> Term {
        let name = format!("__pa_q{}", ctx.len());
        let x = Term::free(&name, self.t.clone());
        let mut ctx2 = ctx.to_vec();
        ctx2.push(x.clone());
        let inner = self.form_body(body, &ctx2);
        Term::abs(self.t.clone(), close(&inner, &name))
    }

    fn bin_t(&self, op: &str, a: &Fol, b: &Fol, ctx: &[Term]) -> Term {
        Term::app(
            Term::app(self.h(op), self.term_body(a, ctx)),
            self.term_body(b, ctx),
        )
    }

    fn bin_f(&self, op: &str, a: &Fol, b: &Fol, ctx: &[Term]) -> Term {
        Term::app(
            Term::app(self.h(op), self.form_body(a, ctx)),
            self.form_body(b, ctx),
        )
    }

    fn h(&self, name: &str) -> Term {
        handler(self.t, self.r, name)
    }
}

/// `enc(A) : Φ_sem⟨t,r⟩` — encode a closed PA **formula** `A` into the
/// semantic carrier at result types `(t, r)`.
pub fn encode_form_at(a: &Fol, t: &Type, r: &Type) -> Term {
    let sf = SemFol { t, r };
    let body = sf.form_body(a, &[]);
    close_handlers(t, r, body)
}

/// `enc(A) : Φ_sem⟨'t,'r⟩` — encode at the polymorphic carrier.
pub fn encode_form(a: &Fol) -> Term {
    encode_form_at(a, &tty(), &rty())
}

/// The HOAS body `Q : 't → 'r` of a quantified formula `∀.body` / `∃.body` —
/// the argument the `all`/`ex` handler is applied to in
/// [`encode_form`]`(All/Ex …)`. Used by the induction schema (the motive).
pub fn hoas_arg_of_quantifier(quantified: &Fol, t: &Type, r: &Type) -> Term {
    let body = match quantified {
        Fol::All(b) | Fol::Ex(b) => b,
        _ => panic!("hoas_arg_of_quantifier: not a quantifier"),
    };
    let sf = SemFol { t, r };
    sf.hoas(body, &[])
}

// ============================================================================
// Constructor helpers used by the closure clauses (`Closed_PA`)
//
// The induction clause is a SCHEMA over a motive `Q : 't → 'r` — the HOAS body
// of a `∀`, exactly the shape `encode_form(All …)` feeds the `all` handler.
// The clause refers to four `Φ_sem` values built from `Q`:
//
//   all_cons Q     = ⌜∀x. Q x⌝
//   q_at Q x       = ⌜Q x⌝          (x : 't a fold-level term value)
//   q_at_zero Q    = ⌜Q 0⌝
//   q_at_succ Q x  = ⌜Q (S x)⌝
//
// Each is `close_handlers` of a fold body; under the denotation `⟦·⟧` they
// β-reduce to `∀x. Q'' x`, `Q'' x`, `Q'' 0`, `Q'' (S x)` (with `Q''` the
// denoted motive), so the clause's denotation is exactly `Thm::nat_induct`.
// ============================================================================

/// `⌜∀x. Q x⌝ : Φ_sem⟨t,r⟩` — wrap the HOAS body `Q : 't → 'r` under `all`.
pub fn all_cons(t: &Type, r: &Type, q: Term) -> Term {
    close_handlers(t, r, Term::app(handler(t, r, "all"), q))
}

/// `⌜∃x. Q x⌝ : Φ_sem⟨t,r⟩`.
pub fn ex_cons(t: &Type, r: &Type, q: Term) -> Term {
    close_handlers(t, r, Term::app(handler(t, r, "ex"), q))
}

/// `⌜Q v⌝ : Φ_sem⟨t,r⟩` — the motive body specialised at the fold-level term
/// value `v : 't`, re-wrapped as a `Φ_sem` formula.
pub fn q_at(t: &Type, r: &Type, q: &Term, v: Term) -> Term {
    close_handlers(t, r, Term::app(q.clone(), v))
}

/// `⌜Q 0⌝ : Φ_sem⟨t,r⟩`.
pub fn q_at_zero(t: &Type, r: &Type, q: &Term) -> Term {
    q_at(t, r, q, handler(t, r, "zero"))
}

/// `⌜Q (S x)⌝ : Φ_sem⟨t,r⟩` for a fold-level `x : 't`.
pub fn q_at_succ(t: &Type, r: &Type, q: &Term, x: Term) -> Term {
    let sx = Term::app(handler(t, r, "succ"), x);
    q_at(t, r, q, sx)
}

/// `⌜a = b⌝ : Φ_sem⟨t,r⟩` from two fold-level term values `a, b : 't` — the
/// atomic-equality constructor (used by the Leibniz closure clause).
pub fn eq_cons(t: &Type, r: &Type, a: Term, b: Term) -> Term {
    let body = Term::app(Term::app(handler(t, r, "eq"), a), b);
    close_handlers(t, r, body)
}

/// `⌜∀x. Q x ⟹ Q (S x)⌝ : Φ_sem⟨t,r⟩` — the induction *step* formula from a
/// motive `Q : 't → 'r`. The HOAS body of the `∀` is `λx. imp (Q x) (Q (S x))`.
pub fn all_step_cons(t: &Type, r: &Type, q: &Term) -> Term {
    let x = Term::free("__sx", t.clone());
    let qx = Term::app(q.clone(), x.clone());
    let qsx = Term::app(q.clone(), Term::app(handler(t, r, "succ"), x.clone()));
    let body = Term::app(Term::app(handler(t, r, "imp"), qx), qsx);
    let hoas = Term::abs(t.clone(), close(&body, "__sx"));
    close_handlers(t, r, Term::app(handler(t, r, "all"), hoas))
}

/// `⌜A ⟹ B⌝ : Φ_sem⟨t,r⟩` from two `Φ_sem` formulas — the `imp` constructor
/// used by the MP closure clause. (Unwraps `A`/`B` back to fold bodies via the
/// handlers, applies the `imp` handler, re-wraps.)
pub fn imp_cons(t: &Type, r: &Type, a: &Term, b: &Term) -> Term {
    let body = Term::app(
        Term::app(handler(t, r, "imp"), apply_to_handlers(t, r, a.clone())),
        apply_to_handlers(t, r, b.clone()),
    );
    close_handlers(t, r, body)
}

/// Apply an encoded `Φ_sem` value to the twelve handlers, recovering its fold
/// body `: 'r`. Inverse of [`close_handlers`] up to β.
fn apply_to_handlers(t: &Type, r: &Type, enc: Term) -> Term {
    let mut acc = enc;
    for (name, _) in HANDLERS {
        acc = Term::app(acc, handler(t, r, name));
    }
    acc
}

// ============================================================================
// The standard `nat`/`bool` handlers — the denotation fold
// ============================================================================

/// The twelve standard handlers `(fvar, zero, succ, add, mul, eq, neg, and,
/// or, imp, all, ex)` at `'t := nat, 'r := bool`, in fold order.
///
/// - `fvar k = pa.v{k}` — the standard PA free-variable interpretation, so a
///   free atom denotes to the named HOL `nat` free variable (matching
///   [`super::deep::fvar_hol`] and letting the induction schema discharge to
///   [`Thm::nat_induct`](covalence_core::Thm::nat_induct)).
/// - arithmetic handlers are the real `nat` operations;
/// - the connectives are the real `bool` operations;
/// - `all`/`ex` are real HOL `∀`/`∃` over `nat` (`P : nat → bool ↦ ∀x. P x`).
pub fn std_handlers() -> Vec<Term> {
    let n = nat();
    let b = Type::bool();

    // fvar : nat → nat   = λk. pa.v{?}.  PA free atoms denote to named HOL
    // free vars; but a fold handler must be a *uniform* function of the atom
    // index `k : nat`. The standard interpretation uses a single environment
    // function `pa.env : nat → nat` mapping atom index ↦ its value, so
    // `fvar := pa.env`. (Concrete metatheorems specialise `pa.env` or, for the
    // closed formulas PA states, never reach a free atom.)
    let fvar = Term::free("pa.env", Type::fun(n.clone(), n.clone()));

    let zero = Term::nat_lit(Nat::zero());
    let succ = defs::nat_succ();
    let add = defs::nat_add();
    let mul = defs::nat_mul();

    // eq : nat → nat → bool
    let eq = Term::eq_op(n.clone());

    // neg : bool → bool = λp. ¬p
    let p = Term::free("p", b.clone());
    let q = Term::free("q", b.clone());
    let neg = Term::abs(b.clone(), close(&p.clone().not().expect("sem: ¬"), "p"));
    let bin = |body: Term| -> Term {
        let inner = Term::abs(b.clone(), close(&body, "q"));
        Term::abs(b.clone(), close(&inner, "p"))
    };
    let and = bin(p.clone().and(q.clone()).expect("sem: ∧"));
    let or = bin(p.clone().or(q.clone()).expect("sem: ∨"));
    let imp = bin(p.clone().imp(q.clone()).expect("sem: ⟹"));

    // all : (nat → bool) → bool = λP. ∀x. P x
    let big_p = Term::free("P", Type::fun(n.clone(), b.clone()));
    let pp_all = {
        let x = Term::free("__x", n.clone());
        let body = big_p
            .clone()
            .apply(x.clone())
            .expect("sem: all body")
            .forall("__x", n.clone())
            .expect("sem: ∀");
        Term::abs(Type::fun(n.clone(), b.clone()), close(&body, "P"))
    };
    let pp_ex = {
        let x = Term::free("__x", n.clone());
        let body = big_p
            .clone()
            .apply(x.clone())
            .expect("sem: ex body")
            .exists("__x", n.clone())
            .expect("sem: ∃");
        Term::abs(Type::fun(n.clone(), b.clone()), close(&body, "P"))
    };

    vec![
        fvar, zero, succ, add, mul, eq, neg, and, or, imp, pp_all, pp_ex,
    ]
}

/// `⟦A⟧ : bool` — the standard denotation of an encoded formula `A`. Pins the
/// carrier at `'t := nat, 'r := bool` and folds with the standard handlers:
/// `A[nat,bool] (fvar) (zero) … (ex)`. Accepts `A` at `Φ_sem⟨'t,'r⟩` or already
/// pinned. **This is a single fold**, so a predicate `λA. ⟦A⟧` can be
/// `inst`'d into `Derivable_PA` and β-reduced (the whole point).
pub fn denote(a: Term) -> Term {
    let a = covalence_core::subst::subst_tfree_in_term(&a, "t", &nat());
    let a = covalence_core::subst::subst_tfree_in_term(&a, "r", &Type::bool());
    apply_std(a)
}

/// Apply the standard handlers to an *already `Φ_sem⟨nat,bool⟩`-typed* term.
fn apply_std(a: Term) -> Term {
    let mut acc = a;
    for h in std_handlers() {
        acc = Term::app(acc, h);
    }
    acc
}

/// `λA:Φ_sem⟨nat,bool⟩. ⟦A⟧` — the **denotation predicate**, the impredicative
/// instantiation `d := ⟦·⟧` the soundness proof feeds into `Derivable_PA`.
/// `d A` β-reduces to `denote(A)` for any encoded `A`, the property soundness
/// rests on.
pub fn denote_pred() -> Term {
    let big_a = Term::free("A", phi_at_std());
    let body = apply_std(big_a); // ⟦A⟧ with A free
    Term::abs(phi_at_std(), close(&body, "A"))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::init::eq::beta_nf;

    fn norm(t: Term) -> Term {
        beta_nf(t).concl().as_eq().unwrap().1.clone()
    }

    /// Encoded formulas are well-typed at the carrier `Φ_sem⟨'t,'r⟩`.
    #[test]
    fn encode_is_typed() {
        let f = Fol::Eq(Box::new(Fol::FVar(0)), Box::new(Fol::Zero));
        assert_eq!(encode_form(&f).type_of().unwrap(), phi());
        // ∀x. x = 0
        let q = Fol::All(Box::new(Fol::Eq(
            Box::new(Fol::BVar(0)),
            Box::new(Fol::Zero),
        )));
        assert_eq!(encode_form(&q).type_of().unwrap(), phi());
    }

    /// The denotation of a closed atomic formula β-reduces to the HOL `nat`
    /// equation — the same standard interpretation `deep.rs` builds by hand.
    #[test]
    fn denote_atomic_matches_deep() {
        // 0 = 0
        let f = Fol::Eq(Box::new(Fol::Zero), Box::new(Fol::Zero));
        let d = denote(encode_form(&f));
        assert_eq!(d.type_of().unwrap(), Type::bool());
        let expected = super::super::deep::denote_closed(&f);
        assert_eq!(norm(d), norm(expected));
    }

    /// A universally-quantified formula denotes to a real HOL `∀x:nat. …`,
    /// matching `deep.rs`'s hand-built standard interpretation up to β.
    #[test]
    fn denote_forall_matches_deep() {
        // ∀x. x = x
        let f = Fol::All(Box::new(Fol::Eq(
            Box::new(Fol::BVar(0)),
            Box::new(Fol::BVar(0)),
        )));
        let d = denote(encode_form(&f));
        let expected = super::super::deep::denote_closed(&f);
        assert_eq!(norm(d), norm(expected));
    }

    /// The induction-clause constructors denote to exactly `nat_induct`'s
    /// shape: `all_cons Q ↦ ∀x. Q'' x`, `q_at_zero Q ↦ Q'' 0`,
    /// `q_at_succ Q x ↦ Q'' (S x)`. We check the closed `∀x. x = x` motive.
    #[test]
    fn induction_constructors_denote_to_nat_induct_shape() {
        let t = tty();
        let r = rty();
        // Q := λx:'t. (eq x x)  — the body of ⌜∀x. x = x⌝.
        let x = Term::free("__qx", t.clone());
        let qbody = Term::app(Term::app(handler(&t, &r, "eq"), x.clone()), x.clone());
        let q = Term::abs(t.clone(), close(&qbody, "__qx"));

        // all_cons Q must denote like encode_form(∀x. x = x).
        let direct = Fol::All(Box::new(Fol::Eq(
            Box::new(Fol::BVar(0)),
            Box::new(Fol::BVar(0)),
        )));
        assert_eq!(
            norm(denote(all_cons(&t, &r, q.clone()))),
            norm(denote(encode_form(&direct)))
        );

        // q_at_zero Q denotes to (0 = 0).
        let zero_eq = Fol::Eq(Box::new(Fol::Zero), Box::new(Fol::Zero));
        assert_eq!(
            norm(denote(q_at_zero(&t, &r, &q))),
            norm(denote(encode_form(&zero_eq)))
        );
    }

    /// Nested quantifiers index the HOAS context correctly: `∀x.∀y. x = y`.
    #[test]
    fn denote_nested_forall_matches_deep() {
        let f = Fol::All(Box::new(Fol::All(Box::new(Fol::Eq(
            Box::new(Fol::BVar(1)),
            Box::new(Fol::BVar(0)),
        )))));
        let d = denote(encode_form(&f));
        let expected = super::super::deep::denote_closed(&f);
        assert_eq!(norm(d), norm(expected));
    }
}
