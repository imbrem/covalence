//! HOL term/type builder over the `covalence-core` kernel.
//!
//! ## What this module is
//!
//! [`HolLightCtx`] — a zero-sized handle whose methods construct HOL
//! terms and types out of the kernel's first-class atoms. It is pure
//! syntax plumbing: every method returns a [`Term`] or [`Type`], not a
//! [`covalence_core::Thm`], so nothing here can widen the TCB.
//!
//! ## Why it's so thin
//!
//! HOL is folded into the kernel. `bool`, `=`, `T`, `F`, `⟹`, `¬`,
//! `∧`, `∨`, `↔`, `∀`, `∃`, `ε` are not an observer family layered on
//! a separate meta-logic — they are kernel atoms directly:
//!
//! - `bool` is [`Type::bool`].
//! - `T` / `F` are the [`TermKind::Bool`] literals.
//! - `=` / `ε` are the primitive [`TermKind::Eq`] / [`TermKind::Select`]
//!   constants; the connectives (`∧ ∨ ¬ ⟹ ⟺ ∀ ∃`) are the defined
//!   constants in `covalence_core::defs::logic`, applied via `App`.
//!
//! There is no `Trueprop` coercion and no `eq_reflection` bridge
//! axiom: a HOL judgement `Γ ⊢ p` is just a kernel `Thm` whose
//! conclusion and hypotheses are `bool`-typed terms. The kernel's 10
//! primitive + 8 derived rules already operate directly on these
//! atoms, so this module only has to *spell the terms*, not bridge
//! between two logics.
//!
//! ## The one subtlety: binders auto-close
//!
//! The kernel represents bound variables locally-namelessly
//! ([`Bound`](covalence_core::TermKind::Bound)). A caller assembling a
//! quantifier body naturally writes free variables
//! ([`Term::free`]); [`HolLightCtx::mk_forall`] / [`mk_exists`] /
//! [`mk_select`] therefore call [`covalence_core::subst::close`] to
//! bind the named free variable before wrapping it in [`Term::abs`].
//! Skip that and the binder binds nothing, so `Thm::all_elim` has no
//! position to substitute into.
//!
//! [`mk_exists`]: HolLightCtx::mk_exists
//! [`mk_select`]: HolLightCtx::mk_select

use covalence_core::{Term, TermKind, Type, defs};

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
    /// constructor; we re-use the kernel's `Fun`.
    pub fn fun_type(&self, a: Type, b: Type) -> Type {
        Type::fun(a, b)
    }

    // ---- HOL constants ----
    //
    // `=` is the primitive `TermKind::Eq`; the connectives are the
    // defined constants in `covalence_core::defs::logic` (applied
    // `Spec` leaves). These builders just spell the application chains.

    /// HOL `=` instantiated at `α → α → bool`.
    pub fn eq_at(&self, alpha: Type) -> Term {
        Term::eq_op(alpha)
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

    /// HOL `==>` — the `imp` connective.
    pub fn imp_op(&self) -> Term {
        defs::imp()
    }
    /// HOL `p ==> q`.
    pub fn mk_imp(&self, p: Term, q: Term) -> Term {
        Term::app(Term::app(self.imp_op(), p), q)
    }

    /// HOL `~` — the `not` connective.
    pub fn not_op(&self) -> Term {
        defs::not()
    }
    /// HOL `~ p`.
    pub fn mk_not(&self, p: Term) -> Term {
        Term::app(self.not_op(), p)
    }

    /// HOL `/\` — the `and` connective.
    pub fn and_op(&self) -> Term {
        defs::and()
    }
    /// HOL `p /\ q`.
    pub fn mk_and(&self, p: Term, q: Term) -> Term {
        Term::app(Term::app(self.and_op(), p), q)
    }

    /// HOL `\/` — the `or` connective.
    pub fn or_op(&self) -> Term {
        defs::or()
    }
    /// HOL `p \/ q`.
    pub fn mk_or(&self, p: Term, q: Term) -> Term {
        Term::app(Term::app(self.or_op(), p), q)
    }

    /// HOL `<=>` — the `iff` connective.
    pub fn iff_op(&self) -> Term {
        defs::iff()
    }
    /// HOL `p <=> q`.
    pub fn mk_iff(&self, p: Term, q: Term) -> Term {
        Term::app(Term::app(self.iff_op(), p), q)
    }

    /// HOL `∀` at `(α → bool) → bool` — the `forall` spec at `α`.
    pub fn forall_at(&self, alpha: Type) -> Term {
        defs::forall(alpha)
    }
    /// HOL `∀x:α. body` — `Forall (λx:α. body)`. Auto-closes free
    /// occurrences of `hint` in `body` to `Bound(0)` so that
    /// `Thm::all_elim` correctly substitutes a witness for them.
    pub fn mk_forall(&self, hint: &str, alpha: Type, body: Term) -> Term {
        let closed = covalence_core::subst::close(&body, hint);
        let lambda = Term::abs(hint, alpha.clone(), closed);
        Term::app(self.forall_at(alpha), lambda)
    }

    /// HOL `∃` at `(α → bool) → bool` — the `exists` spec at `α`.
    pub fn exists_at(&self, alpha: Type) -> Term {
        defs::exists(alpha)
    }
    /// HOL `∃x:α. body` — `Exists (λx:α. body)`. Auto-closes free
    /// occurrences of `hint` in `body` so the binder actually binds.
    pub fn mk_exists(&self, hint: &str, alpha: Type, body: Term) -> Term {
        let closed = covalence_core::subst::close(&body, hint);
        let lambda = Term::abs(hint, alpha.clone(), closed);
        Term::app(self.exists_at(alpha), lambda)
    }

    /// HOL `ε` (Hilbert's choice) at `(α → bool) → α` — the primitive
    /// `TermKind::Select`.
    pub fn select_at(&self, alpha: Type) -> Term {
        Term::select_op(alpha)
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

// `HolLight` enum + `IsHolLight` marker trait removed: HOL primitives
// are now kernel atoms (`Type::bool()`, `Term::bool_lit(_)`, the `Eq` /
// `Select` leaves) and the `defs::logic` connectives, not an observer
// family.
