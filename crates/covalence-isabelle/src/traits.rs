//! Traits for Isabelle/Pure-style type theory.
//!
//! Three stacked traits decouple type construction, term construction, and
//! theorem proving so that multiple backends (PureKernel, NullKernel,
//! remote proxy, etc.) can implement the same API.
//!
//! All associated types (`Type`, `Term`, `Thm`) are `Copy` index handles
//! in the concrete implementations.

use smol_str::SmolStr;

use crate::types::*;

/// Type-level operations for an Isabelle/Pure-style system.
pub trait IsabelleTypes {
    /// The representation of types (lightweight Copy handle).
    type Type: Copy + std::fmt::Debug;

    // -- Well-known identifiers --

    /// Name ID for the function type constructor (`fun`).
    fn fun_id(&self) -> NameId;

    /// Name ID for the proposition type constructor (`prop`).
    fn prop_id(&self) -> NameId;

    // -- Constructors (allocate → &mut self) --

    /// Construct a free type variable: `'a::sort`.
    fn mk_tfree(&mut self, name: NameId, sort: Sort) -> Self::Type;

    /// Construct a schematic type variable: `?'a.i::sort`.
    fn mk_tvar(&mut self, name: IndexName, sort: Sort) -> Self::Type;

    /// Construct a type constructor application.
    fn mk_type(&mut self, name: NameId, args: Vec<Self::Type>) -> Self::Type;

    /// The `prop` type.
    fn prop_type(&mut self) -> Self::Type;

    /// The function type `a => b`.
    fn fun_type(&mut self, a: Self::Type, b: Self::Type) -> Self::Type;

    // -- Inspection (&self) --

    /// Destruct a free type variable, returning `(name, sort)`.
    fn dest_tfree(&self, ty: Self::Type) -> Option<(NameId, Sort)>;

    /// Destruct a schematic type variable, returning `(indexname, sort)`.
    fn dest_tvar(&self, ty: Self::Type) -> Option<(IndexName, Sort)>;

    /// Destruct a type constructor application, returning `(constructor, args)`.
    fn dest_type(&self, ty: Self::Type) -> Option<(NameId, Vec<Self::Type>)>;

    /// Type equality.
    fn type_eq(&self, a: Self::Type, b: Self::Type) -> bool;

    /// Collect free type variables.
    fn tyfrees(&self, ty: Self::Type) -> Vec<(NameId, Sort)>;

    /// Collect schematic type variables.
    fn tyvars(&self, ty: Self::Type) -> Vec<(IndexName, Sort)>;

    /// Instantiate schematic type variables.
    /// `pairs` is `(new_type, old_indexname)`.
    fn instantiate_typ(&mut self, ty: Self::Type, pairs: &[(Self::Type, IndexName)]) -> Self::Type;
}

/// Term-level operations for an Isabelle/Pure-style system.
pub trait IsabelleTerms: IsabelleTypes {
    /// The representation of terms (lightweight Copy handle).
    type Term: Copy + std::fmt::Debug;

    // -- Well-known identifiers --

    /// Name ID for `Pure.imp` (`==>`).
    fn imp_id(&self) -> NameId;

    /// Name ID for `Pure.all` (`!!`).
    fn all_id(&self) -> NameId;

    /// Name ID for `Pure.eq` (`==`).
    fn eq_id(&self) -> NameId;

    // -- Constructors (allocate → &mut self) --

    /// Construct a bound variable (de Bruijn index).
    fn mk_bound(&mut self, i: u32) -> Self::Term;

    /// Construct a free variable.
    fn mk_free(&mut self, name: NameId, ty: Self::Type) -> Self::Term;

    /// Construct a schematic variable.
    fn mk_var(&mut self, name: IndexName, ty: Self::Type) -> Self::Term;

    /// Construct a constant term.
    fn mk_const(&mut self, name: NameId, ty: Self::Type) -> Self::Term;

    /// Construct an application `f x`.
    fn mk_app(&mut self, f: Self::Term, x: Self::Term) -> Self::Term;

    /// Construct a lambda abstraction `Abs(hint, ty, body)`.
    fn mk_abs(&mut self, hint: NameId, ty: Self::Type, body: Self::Term) -> Self::Term;

    /// Construct an implication `A ==> B`.
    fn mk_imp(&mut self, a: Self::Term, b: Self::Term) -> Self::Term;

    /// Construct a universal quantification `!!x::ty. body`.
    fn mk_all(&mut self, hint: NameId, ty: Self::Type, body: Self::Term) -> Self::Term;

    /// Construct an equality `a == b`.
    fn mk_eq(&mut self, a: Self::Term, b: Self::Term) -> Self::Term;

    // -- Inspection (&self) --

    /// Destruct a bound variable, returning its index.
    fn dest_bound(&self, tm: Self::Term) -> Option<u32>;

    /// Destruct a free variable, returning `(name, type)`.
    fn dest_free(&self, tm: Self::Term) -> Option<(NameId, Self::Type)>;

    /// Destruct a schematic variable, returning `(indexname, type)`.
    fn dest_var(&self, tm: Self::Term) -> Option<(IndexName, Self::Type)>;

    /// Destruct a constant, returning `(name, type)`.
    fn dest_const(&self, tm: Self::Term) -> Option<(NameId, Self::Type)>;

    /// Destruct an application, returning `(f, x)`.
    fn dest_app(&self, tm: Self::Term) -> Option<(Self::Term, Self::Term)>;

    /// Destruct an abstraction, returning `(hint, type, body)`.
    fn dest_abs(&self, tm: Self::Term) -> Option<(NameId, Self::Type, Self::Term)>;

    /// Destruct an implication `A ==> B`, returning `(A, B)`.
    fn dest_imp(&self, tm: Self::Term) -> Option<(Self::Term, Self::Term)>;

    /// Destruct a universal `!!x::ty. body`, returning `(hint, ty, body)`.
    fn dest_all(&self, tm: Self::Term) -> Option<(NameId, Self::Type, Self::Term)>;

    /// Destruct an equality `a == b`, returning `(a, b)`.
    fn dest_eq(&self, tm: Self::Term) -> Option<(Self::Term, Self::Term)>;

    /// Get the type of a term (may allocate for Abs).
    fn type_of(&mut self, tm: Self::Term) -> Self::Type;

    /// Term equality (structural, including de Bruijn — this IS alpha-eq).
    fn term_eq(&self, a: Self::Term, b: Self::Term) -> bool;

    /// Collect free variables.
    fn frees(&self, tm: Self::Term) -> Vec<(NameId, Self::Type)>;

    /// Collect schematic variables.
    fn vars(&self, tm: Self::Term) -> Vec<(IndexName, Self::Type)>;

    /// Check if a free variable occurs in a term.
    fn free_in(&self, name: NameId, ty: Self::Type, tm: Self::Term) -> bool;
}

/// Theorem-proving operations for an Isabelle/Pure kernel.
pub trait IsabelleKernel: IsabelleTerms {
    /// The representation of theorems (lightweight Copy handle).
    type Thm: Copy + std::fmt::Debug;

    // -- Theorem inspection --

    /// Get the hypotheses of a theorem.
    fn hyps(&self, th: Self::Thm) -> Vec<Self::Term>;

    /// Get the conclusion of a theorem.
    fn concl(&self, th: Self::Thm) -> Self::Term;

    // -- 11 primitive inference rules --

    /// `assume A`: `{A} ⊢ A` (A must have type prop).
    fn assume(&mut self, tm: Self::Term) -> Result<Self::Thm, PureError>;

    /// `implies_intr A th`: `Γ\{A} ⊢ A ==> B` (from `Γ ⊢ B`).
    fn implies_intr(&mut self, a: Self::Term, th: Self::Thm) -> Result<Self::Thm, PureError>;

    /// `implies_elim th1 th2`: `⊢ B` (from `⊢ A ==> B` and `⊢ A`).
    fn implies_elim(&mut self, th1: Self::Thm, th2: Self::Thm) -> Result<Self::Thm, PureError>;

    /// `forall_intr x ty th`: `Γ ⊢ !!x::ty. B` (from `Γ ⊢ B`, x not free in Γ).
    fn forall_intr(
        &mut self,
        x: NameId,
        ty: Self::Type,
        th: Self::Thm,
    ) -> Result<Self::Thm, PureError>;

    /// `forall_elim t th`: `⊢ B[t/x]` (from `⊢ !!x::ty. B`).
    fn forall_elim(&mut self, t: Self::Term, th: Self::Thm) -> Result<Self::Thm, PureError>;

    /// `reflexive t`: `⊢ t ≡ t`.
    fn reflexive(&mut self, t: Self::Term) -> Result<Self::Thm, PureError>;

    /// `symmetric th`: `⊢ t ≡ s` (from `⊢ s ≡ t`).
    fn symmetric(&mut self, th: Self::Thm) -> Result<Self::Thm, PureError>;

    /// `transitive th1 th2`: `⊢ s ≡ u` (from `⊢ s ≡ t` and `⊢ t ≡ u`).
    fn transitive(&mut self, th1: Self::Thm, th2: Self::Thm) -> Result<Self::Thm, PureError>;

    /// `beta_conversion t`: `⊢ (λx. b)(a) ≡ b[a/x]`.
    fn beta_conversion(&mut self, t: Self::Term) -> Result<Self::Thm, PureError>;

    /// `combination th1 th2`: `⊢ f(a) ≡ g(b)` (from `⊢ f ≡ g` and `⊢ a ≡ b`).
    fn combination(&mut self, th1: Self::Thm, th2: Self::Thm) -> Result<Self::Thm, PureError>;

    /// `abstraction x ty th`: `⊢ (λx. s) ≡ (λx. t)` (from `⊢ s ≡ t`, x not free in hyps).
    fn abstraction(
        &mut self,
        x: NameId,
        ty: Self::Type,
        th: Self::Thm,
    ) -> Result<Self::Thm, PureError>;

    // -- Instantiation --

    /// Instantiate schematic type variables in a theorem.
    /// `pairs` is `(new_type, old_indexname)`.
    fn instantiate_typ_rule(
        &mut self,
        pairs: &[(Self::Type, IndexName)],
        th: Self::Thm,
    ) -> Result<Self::Thm, PureError>;

    /// Instantiate schematic term variables in a theorem.
    /// `pairs` is `(new_term, old_indexname, old_type)`.
    fn instantiate_rule(
        &mut self,
        pairs: &[(Self::Term, IndexName, Self::Type)],
        th: Self::Thm,
    ) -> Result<Self::Thm, PureError>;

    // -- Theory management --

    /// Look up a named axiom.
    fn axiom(&self, name: &str) -> Result<Self::Thm, PureError>;

    /// Add a named axiom (conclusion must be a prop).
    fn add_axiom(&mut self, name: SmolStr, tm: Self::Term) -> Result<Self::Thm, PureError>;

    /// Register a new type constructor with the given arity.
    fn add_type(&mut self, name: NameId, arity: usize) -> Result<(), PureError>;

    /// Register a new constant with its most-general type.
    fn add_constant(&mut self, name: NameId, ty: Self::Type) -> Result<(), PureError>;

    /// Add a class to the sort algebra.
    fn add_class(&mut self, class: NameId) -> Result<(), PureError>;

    /// Add a subclass relation.
    fn add_subclass(&mut self, sub: NameId, sup: NameId) -> Result<(), PureError>;

    /// Add an arity declaration.
    fn add_arity(
        &mut self,
        tycon: NameId,
        arg_sorts: Vec<Sort>,
        class: NameId,
    ) -> Result<(), PureError>;
}
