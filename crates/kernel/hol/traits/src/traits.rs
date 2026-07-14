//! Traits for HOL Light-style type theory.
//!
//! Three stacked traits decouple type construction, term construction, and
//! theorem proving so that multiple backends (sound kernel, null kernel,
//! remote proxy, etc.) can implement the same API.
//!
//! All allocating methods take `&mut self` (plain `Vec` arenas, no `RefCell`).

use crate::types::*;

/// Type-level operations for a HOL Light-style system.
pub trait HolLightTypes {
    /// The representation of types (a `Copy` index handle).
    type Type: Clone + std::fmt::Debug;

    // -- Well-known identifiers --

    /// Name ID for the function type constructor (`->`).
    fn fun_id(&self) -> NameId;

    /// Name ID for the boolean type constructor.
    fn bool_id(&self) -> NameId;

    /// Inform the backend that `name_id` maps to the string `name`.
    ///
    /// HOL Light names live in the OpenTheory `NameTable`'s flat
    /// `u64` namespace, but kernel-backed implementations (e.g.
    /// `HolPrim` on `covalence-kernel`) need the string to drive
    /// shell-level rewrites such as the Forall/Exists/Imp fold on
    /// `Comb(Const "!", _)`. Default impl is a no-op for backends
    /// that key everything off `NameId`.
    fn register_name(&mut self, _name_id: NameId, _name: &str) {}

    // -- Constructors (allocate → &mut self) --

    /// Construct a type variable.
    fn mk_tyvar(&mut self, name: NameId) -> Self::Type;

    /// Construct a type-constructor application (unvalidated).
    fn mk_tyapp(&mut self, name: NameId, args: Vec<Self::Type>) -> Self::Type;

    /// The boolean type.
    fn bool_type(&mut self) -> Self::Type;

    /// The function type `a -> b`.
    fn fun_type(&mut self, a: Self::Type, b: Self::Type) -> Self::Type;

    // -- Inspection (&self) --

    /// Destruct a type variable, returning its name.
    fn dest_tyvar(&self, ty: Self::Type) -> Option<NameId>;

    /// Destruct a type application, returning `(constructor, args)`.
    fn dest_tyapp(&self, ty: Self::Type) -> Option<(NameId, Vec<Self::Type>)>;

    /// Type equality (structural).
    fn type_eq(&self, a: Self::Type, b: Self::Type) -> bool;

    /// Collect all type variables in a type.
    fn tyvars(&self, ty: Self::Type) -> Vec<NameId>;

    /// Apply a type substitution: `pairs` is `(new_type, old_tyvar_name)`.
    fn type_inst(&mut self, ty: Self::Type, pairs: &[(Self::Type, NameId)]) -> Self::Type;
}

/// Term-level operations for a HOL Light-style system.
///
/// Requires `HolLightTypes` for the type layer.
pub trait HolLightTerms: HolLightTypes {
    /// The representation of terms (a `Copy` index handle).
    type Term: Clone + std::fmt::Debug;

    // -- Well-known identifiers --

    /// Name ID for the equality constant (`=`).
    fn eq_id(&self) -> NameId;

    // -- Constructors (allocate → &mut self) --

    /// Construct a variable term.
    fn mk_var(&mut self, name: NameId, ty: Self::Type) -> Self::Term;

    /// Construct a constant term (unvalidated — does not check the constant exists).
    fn mk_const(&mut self, name: NameId, ty: Self::Type) -> Self::Term;

    /// Construct an application `f x`.
    fn mk_comb(&mut self, f: Self::Term, x: Self::Term) -> Self::Term;

    /// Construct a lambda abstraction `\var. body`.
    fn mk_abs(&mut self, var: Self::Term, body: Self::Term) -> Self::Term;

    /// Construct an equality term `lhs = rhs`.
    fn mk_eq(&mut self, lhs: Self::Term, rhs: Self::Term) -> Self::Term;

    // -- Inspection (&self) --

    /// Destruct a variable, returning `(name, type)`.
    fn dest_var(&self, tm: Self::Term) -> Option<(NameId, Self::Type)>;

    /// Destruct a constant, returning `(name, type)`.
    fn dest_const(&self, tm: Self::Term) -> Option<(NameId, Self::Type)>;

    /// Destruct an application, returning `(f, x)`.
    fn dest_comb(&self, tm: Self::Term) -> Option<(Self::Term, Self::Term)>;

    /// Destruct an abstraction, returning `(var, body)`.
    ///
    /// Takes `&mut self` to allow locally-nameless backends to open
    /// the binder by allocating a fresh variable. Named-binder
    /// backends can ignore the mutability.
    fn dest_abs(&mut self, tm: Self::Term) -> Option<(Self::Term, Self::Term)>;

    /// Destruct an equation `lhs = rhs`.
    fn dest_eq(&self, tm: Self::Term) -> Option<(Self::Term, Self::Term)>;

    /// Get the type of a term. May allocate for `Abs` case.
    fn type_of(&mut self, tm: Self::Term) -> Self::Type;

    /// Syntactic term equality (structural).
    fn term_eq(&self, a: Self::Term, b: Self::Term) -> bool;

    /// Alpha-equivalence.
    fn aconv(&self, a: Self::Term, b: Self::Term) -> bool;

    /// Collect free variables.
    ///
    /// Takes `&mut self` so locally-nameless backends can re-allocate
    /// `Var` terms for the returned set.
    fn frees(&mut self, tm: Self::Term) -> Vec<Self::Term>;

    /// Check if a variable occurs free in a term.
    fn vfree_in(&self, var: Self::Term, tm: Self::Term) -> bool;

    // -- Substitution (allocates → &mut self) --

    /// Term-variable substitution. `pairs` is `(new_term, old_var)`.
    fn vsubst(
        &mut self,
        tm: Self::Term,
        pairs: &[(Self::Term, Self::Term)],
    ) -> Result<Self::Term, HolError>;

    /// Type instantiation on terms. `pairs` is `(new_type, old_tyvar_name)`.
    fn inst_term(&mut self, tm: Self::Term, pairs: &[(Self::Type, NameId)]) -> Self::Term;
}

/// Theorem-proving operations for a HOL Light-style kernel.
///
/// All inference rules return `Result` so that null/remote/sealed backends
/// can fail uniformly. All methods take `&mut self` since they may allocate.
pub trait HolLightKernel: HolLightTerms {
    /// The representation of theorems (a `Copy` index handle).
    type Thm: Clone + std::fmt::Debug;

    // -- Theorem inspection --

    /// Get the hypotheses of a theorem.
    fn hyps(&self, th: Self::Thm) -> Vec<Self::Term>;

    /// Get the conclusion of a theorem.
    fn concl(&self, th: Self::Thm) -> Self::Term;

    // -- 10 primitive inference rules --

    /// `REFL tm`: `|- tm = tm`
    fn refl(&mut self, tm: Self::Term) -> Result<Self::Thm, HolError>;

    /// `TRANS th1 th2`: `|- s = t` + `|- t = u` → `|- s = u`
    fn trans(&mut self, th1: Self::Thm, th2: Self::Thm) -> Result<Self::Thm, HolError>;

    /// `MK_COMB th1 th2`: `|- f = g` + `|- x = y` → `|- f x = g y`
    fn mk_comb_rule(&mut self, th1: Self::Thm, th2: Self::Thm) -> Result<Self::Thm, HolError>;

    /// `ABS var th`: `|- s = t` → `|- (\var.s) = (\var.t)`
    fn abs_rule(&mut self, var: Self::Term, th: Self::Thm) -> Result<Self::Thm, HolError>;

    /// `BETA tm`: `|- (\x.t) x = t`
    fn beta_conv(&mut self, tm: Self::Term) -> Result<Self::Thm, HolError>;

    /// `ASSUME tm`: `{tm} |- tm`
    fn assume_rule(&mut self, tm: Self::Term) -> Result<Self::Thm, HolError>;

    /// `EQ_MP th1 th2`: `|- p = q` + `|- p` → `|- q`
    fn eq_mp(&mut self, th1: Self::Thm, th2: Self::Thm) -> Result<Self::Thm, HolError>;

    /// `DEDUCT_ANTISYM_RULE th1 th2`:
    /// `A1 |- p` + `A2 |- q` → `(A1 - {q}) ∪ (A2 - {p}) |- p <=> q`
    fn deduct_antisym(&mut self, th1: Self::Thm, th2: Self::Thm) -> Result<Self::Thm, HolError>;

    /// `INST pairs th`: term variable instantiation.
    /// `pairs` is `(new_term, old_var)`.
    fn inst_rule(
        &mut self,
        pairs: &[(Self::Term, Self::Term)],
        th: Self::Thm,
    ) -> Result<Self::Thm, HolError>;

    /// `INST_TYPE pairs th`: type variable instantiation.
    /// `pairs` is `(new_type, old_tyvar_name)`.
    fn inst_type_rule(
        &mut self,
        pairs: &[(Self::Type, NameId)],
        th: Self::Thm,
    ) -> Result<Self::Thm, HolError>;

    // -- Definitions --

    /// Introduce an axiom `|- tm` (tm must be boolean).
    fn new_axiom(&mut self, tm: Self::Term) -> Result<Self::Thm, HolError>;

    /// Define a new constant from `c = t`.
    fn new_basic_definition(&mut self, tm: Self::Term) -> Result<Self::Thm, HolError>;

    /// Define a new abstract type from an existence theorem.
    ///
    /// `tyvars` is the **article-declared type-parameter order** (OpenTheory's
    /// `defineTypeOp` name list). Backends that canonicalise type-variable
    /// order internally must remember this order so later `opType`
    /// applications instantiate positionally as the article intends.
    ///
    /// `abs_var_name` and `rep_var_name` are the variable names to use in the
    /// generated theorems (e.g. `"a"` and `"r"` in the OpenTheory convention).
    fn new_basic_type_definition(
        &mut self,
        tyname: NameId,
        abs_name: NameId,
        rep_name: NameId,
        tyvars: &[NameId],
        abs_var_name: NameId,
        rep_var_name: NameId,
        th: Self::Thm,
    ) -> Result<(Self::Thm, Self::Thm), HolError>;

    // -- State / validated constructors --

    /// Register a new type constructor.
    fn new_type(&mut self, name: NameId, arity: usize) -> Result<(), HolError>;

    /// Register a new constant with its most-general type.
    fn new_constant(&mut self, name: NameId, ty: Self::Type) -> Result<(), HolError>;

    /// Get the list of axioms.
    fn get_axioms(&self) -> Vec<Self::Thm>;

    /// Construct a type application with validation (checks arity, existence).
    fn mk_type_validated(
        &mut self,
        name: NameId,
        args: Vec<Self::Type>,
    ) -> Result<Self::Type, HolError>;

    /// Construct a constant term with validation (checks type instance).
    fn mk_const_validated(&mut self, name: NameId, ty: Self::Type) -> Result<Self::Term, HolError>;
}
