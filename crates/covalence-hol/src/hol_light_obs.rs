//! HOL Light bootstrap on top of `covalence-pure`.
//!
//! ## What this module is
//!
//! A single Rust `enum` ([`HolLight`]) that carries every HOL Light
//! primitive — `bool`, `=`, `T`, `F`, `⟹`, `¬`, `∧`, `∨`, `↔`, `∀`,
//! `∃`, `ε`, plus `Trueprop` — as variants of one observer family.
//! Plus the polymorphic `eq_reflection` axiom that bridges HOL
//! bool-equality to Pure meta-equality. That's it.
//!
//! All observers and the `eq_reflection` axiom are process-global
//! lazy statics. [`HolLightCtx`] is a zero-sized handle over them —
//! constructing one is free.
//!
//! ## Mapping to Isabelle/HOL
//!
//! `covalence-pure` plays the role of Isabelle/Pure: the meta-logic
//! with `prop`, meta-`⋀`, meta-`⟹`, meta-`≡`, plus the standard
//! inference rules (`assume`, `imp_intro/elim`, `all_intro/elim`,
//! `refl`/`trans`/`sym`, `cong_app`/`cong_abs`, `beta_conv`,
//! `eta_conv`, `eq_mp`, `inst_tfree`).
//!
//! `covalence-hol` plays the role of Isabelle/HOL: HOL as a *theory*
//! built on top of the meta-logic. Standard Isabelle/HOL ships with:
//!
//! - `bool` as a separate type (we encode it as `TyConObs(Bool_obs, "bool", [])`).
//! - `Trueprop : bool ⇒ prop` as the explicit coercion (our [`HolLight::Trueprop`]).
//! - HOL `=` as a constant at `'a ⇒ 'a ⇒ bool` (our [`HolLight::Eq`]).
//! - One bridge axiom — `eq_reflection : (x = y) ⟹ (x ≡ y)` — that
//!   we mirror exactly in [`HolLightCtx::eq_reflection_axiom`].
//!
//! From the `eq_reflection` axiom plus Pure's primitives, every HOL
//! Light rule derives the way Isabelle does it. The audit-trail
//! discipline matches HOL Light's: any HOL theorem that relies on
//! `eq_reflection` carries it in the hypothesis set.
//!
//! ## Tarski-T encoding
//!
//! HOL judgements live in Pure as `⊢_Pure Trueprop p`. A HOL theorem
//! `Γ ⊢_HOL p` (with `p : bool` and each `h ∈ Γ : bool`) is the Pure
//! theorem
//!
//! ```text
//! {eq_reflection, ETA, SELECT, INFINITY, …} ∪ {Trueprop h | h ∈ Γ}
//!     ⊢_Pure Trueprop p
//! ```
//!
//! Pure's hypothesis set carries every axiom the conclusion depends
//! on (eq_reflection plus whichever standard HOL axioms apply) and
//! the HOL hypotheses lifted through Trueprop.
//!
//! ## The 10 HOL Light rules
//!
//! Status: all 10 derive via `eq_reflection` plus Pure's primitives.
//! The (forthcoming) `PureHol` kernel adapter wires each one up.
//!
//! | HOL Light rule    | Derived from                        |
//! |-------------------|-------------------------------------|
//! | REFL              | Pure `refl` + eq_reflection (bwd)   |
//! | TRANS             | eq_reflection (fwd) + Pure `trans` + eq_reflection (bwd) |
//! | MK_COMB           | eq_reflection (fwd) + Pure `cong_app` + eq_reflection (bwd) |
//! | ABS               | eq_reflection (fwd) + Pure `cong_abs` (checks "x not free in hyps") + eq_reflection (bwd) |
//! | BETA              | Pure `beta_conv` + eq_reflection (bwd) |
//! | ASSUME            | Pure `assume` on `Trueprop p` directly |
//! | EQ_MP at bool     | eq_reflection (fwd) + Pure `eq_mp` |
//! | DEDUCT_ANTISYM    | Pure `imp_intro` + iff_def (defined HOL constant) |
//! | INST              | Pure `all_intro` (checks "x not free in hyps") + `all_elim` |
//! | INST_TYPE         | Pure `inst_tfree` directly          |
//!
//! Pure's primitives already enforce the hypothesis-side-conditions
//! the conditioned HOL Light rules require (ABS, INST), and apply
//! substitutions uniformly across the hypothesis set (INST, INST_TYPE).
//! There's no soundness gap to engineer around.
//!
//! ## Why we don't use the "axiomless" approach
//!
//! An earlier version of this module attempted to avoid the
//! eq_reflection axiom by recognising HOL-Light-derivable shapes
//! directly in the [`covalence_core::ObsTrue`] and
//! [`covalence_core::ObsImp`] policies. The pattern looked appealing
//! — fewer hypotheses, no axiom to thread through — but the analysis
//! showed that ABS and INST cannot soundly fit. The pattern was
//! removed. See the project's `audit` commit for the analysis.

use covalence_core::{HolOp, Term, TermKind, Type};

// ============================================================================
// HOL bridge axioms (still postulated)
// ============================================================================
//
// `Bool`, `Eq`, `True`, `False`, `Imp`, `Not`, `And`, `Or`, `Iff`,
// `Forall`, `Exists`, `Select`, `Trueprop` are no longer observer
// objects — they are first-class kernel atoms (`Type::bool()`,
// `Term::Bool(_)`, `Term::HolOp(_, _)`). The HOL bridge axioms
// below stay postulated as lazy theorems for now.

// ============================================================================
// HolLightCtx — zero-sized handle on the process-global HOL primitives
// ============================================================================

/// Zero-sized handle on the process-global HOL Light primitives.
/// Constructing one is free — there are no fields. Methods delegate
/// to the module-level `LazyLock` statics. Two `HolLightCtx` values
/// are interchangeable.
#[derive(Clone, Copy, Debug, Default)]
pub struct HolLightCtx;

impl HolLightCtx {
    /// Construct a handle. Free; no allocation.
    pub fn new() -> Self {
        Self
    }

    // ---- HOL types ----

    /// HOL `bool` — the cached canonical `Type::bool()` instance.
    /// HOL is folded into the kernel, so `bool` is a regular kernel
    /// type, not a `TyConObs` over an observer identity.
    pub fn bool_type(&self) -> Type {
        Type::bool()
    }

    /// Pure function type α → β. HOL doesn't add a new function-type
    /// constructor; we re-use Pure's `Fun`.
    pub fn fun_type(&self, a: Type, b: Type) -> Type {
        Type::fun(a, b)
    }

    // ---- HOL constants — now folded into core via TermKind::HolOp ----

    /// HOL `=` instantiated at `α → α → bool`.
    pub fn eq_at(&self, alpha: Type) -> Term {
        let ty = Type::fun(alpha.clone(), Type::fun(alpha, self.bool_type()));
        Term::hol_op(HolOp::Eq, ty)
    }

    /// `t = u : bool`, given `t` and `u` of the same type α. Errors
    /// if `t` is ill-typed.
    pub fn mk_eq(&self, lhs: Term, rhs: Term) -> Result<Term, covalence_core::Error> {
        let alpha = lhs.type_of()?;
        let eq = self.eq_at(alpha);
        Ok(Term::app(Term::app(eq, lhs), rhs))
    }

    /// HOL `T : bool` — a kernel literal.
    pub fn t(&self) -> Term {
        Term::bool_lit(true)
    }

    /// HOL `F : bool` — a kernel literal.
    pub fn f(&self) -> Term {
        Term::bool_lit(false)
    }

    fn bool_binop_ty(&self) -> Type {
        let b = self.bool_type();
        Type::fun(b.clone(), Type::fun(b.clone(), b))
    }

    /// HOL `==>` at `bool → bool → bool`.
    pub fn imp_op(&self) -> Term {
        Term::hol_op(HolOp::Imp, self.bool_binop_ty())
    }
    /// HOL `p ==> q`.
    pub fn mk_imp(&self, p: Term, q: Term) -> Term {
        Term::app(Term::app(self.imp_op(), p), q)
    }

    /// HOL `~` at `bool → bool`.
    pub fn not_op(&self) -> Term {
        let b = self.bool_type();
        Term::hol_op(HolOp::Not, Type::fun(b.clone(), b))
    }
    /// HOL `~ p`.
    pub fn mk_not(&self, p: Term) -> Term {
        Term::app(self.not_op(), p)
    }

    /// HOL `/\` at `bool → bool → bool`.
    pub fn and_op(&self) -> Term {
        Term::hol_op(HolOp::And, self.bool_binop_ty())
    }
    /// HOL `p /\ q`.
    pub fn mk_and(&self, p: Term, q: Term) -> Term {
        Term::app(Term::app(self.and_op(), p), q)
    }

    /// HOL `\/` at `bool → bool → bool`.
    pub fn or_op(&self) -> Term {
        Term::hol_op(HolOp::Or, self.bool_binop_ty())
    }
    /// HOL `p \/ q`.
    pub fn mk_or(&self, p: Term, q: Term) -> Term {
        Term::app(Term::app(self.or_op(), p), q)
    }

    /// HOL `<=>` at `bool → bool → bool`.
    pub fn iff_op(&self) -> Term {
        Term::hol_op(HolOp::Iff, self.bool_binop_ty())
    }
    /// HOL `p <=> q`.
    pub fn mk_iff(&self, p: Term, q: Term) -> Term {
        Term::app(Term::app(self.iff_op(), p), q)
    }

    /// HOL `∀` at `(α → bool) → bool`.
    pub fn forall_at(&self, alpha: Type) -> Term {
        let pred = Type::fun(alpha, self.bool_type());
        Term::hol_op(HolOp::Forall, Type::fun(pred, self.bool_type()))
    }
    /// HOL `∀x:α. body` — `Forall (λx:α. body)`. Auto-closes free
    /// occurrences of `hint` in `body` to `Bound(0)` so that
    /// `Thm::all_elim` correctly substitutes a witness for them.
    pub fn mk_forall(&self, hint: &str, alpha: Type, body: Term) -> Term {
        let closed = covalence_core::subst::close(&body, hint);
        let lambda = Term::abs(hint, alpha.clone(), closed);
        Term::app(self.forall_at(alpha), lambda)
    }

    /// HOL `∃` at `(α → bool) → bool`.
    pub fn exists_at(&self, alpha: Type) -> Term {
        let pred = Type::fun(alpha, self.bool_type());
        Term::hol_op(HolOp::Exists, Type::fun(pred, self.bool_type()))
    }
    /// HOL `∃x:α. body` — `Exists (λx:α. body)`. Auto-closes free
    /// occurrences of `hint` in `body` so the binder actually binds.
    pub fn mk_exists(&self, hint: &str, alpha: Type, body: Term) -> Term {
        let closed = covalence_core::subst::close(&body, hint);
        let lambda = Term::abs(hint, alpha.clone(), closed);
        Term::app(self.exists_at(alpha), lambda)
    }

    /// HOL `ε` (Hilbert's choice) at `(α → bool) → α`.
    pub fn select_at(&self, alpha: Type) -> Term {
        let pred = Type::fun(alpha.clone(), self.bool_type());
        Term::hol_op(HolOp::Select, Type::fun(pred, alpha))
    }
    /// HOL `ε x:α. body` — `Select (λx:α. body)`. Auto-closes free
    /// occurrences of `hint` in `body` so the binder actually binds.
    pub fn mk_select(&self, hint: &str, alpha: Type, body: Term) -> Term {
        let closed = covalence_core::subst::close(&body, hint);
        let lambda = Term::abs(hint, alpha.clone(), closed);
        Term::app(self.select_at(alpha), lambda)
    }

    // ---- Identity check helpers ----

    /// `true` iff `t` is the HOL `T` literal.
    pub fn is_true(&self, t: &Term) -> bool {
        matches!(t.kind(), TermKind::Bool(true))
    }

    /// `true` iff `t` is the HOL `F` literal.
    pub fn is_false(&self, t: &Term) -> bool {
        matches!(t.kind(), TermKind::Bool(false))
    }
}

// `HolLight` enum + `IsHolLight` marker trait removed:
// HOL primitives are now first-class kernel atoms (`Type::bool()`,
// `Term::Bool(_)`, `Term::HolOp(_, _)`), not an observer family.
