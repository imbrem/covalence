//! The **signature** of a basic inductive type — the data the recursion
//! engine ([`super::graph`]) consumes to build a recursor generically.
//!
//! "Basic" here means: single-sorted, parametric, first-order,
//! strictly-positive, and *directly* recursive — every recursive argument
//! has the inductive type `T` itself, never `F⟨T⟩` under some other
//! functor `F`. That covers `nat` (`zero`, `succ`), `list` (`nil`,
//! `cons`), binary trees, and the like; nested / mutual / infinitary
//! types are deliberately out of scope (see the generated open-work index).
//!
//! A signature is a *description*, not a proof: it names the type, the
//! impredicative relation variable used in the graph construction, and
//! each constructor with its argument shape. The engine turns that into
//! the recursion graph, its totality / determinacy proofs, and finally
//! the recursor — but those steps additionally need the *freeness* and
//! *induction* facts the kernel or the carrier supplies separately.
//!
//! ## Generic over the HOL representation
//!
//! The data model is generic over the **term** (`Tm`) and **type** (`Ty`)
//! representations so the engine can run over any [`Hol`](super::hol::Hol)
//! backend. The bare names [`Arg`] / [`Constructor`] / [`InductiveSig`] are
//! the **native** instantiations (`covalence-core` `Term` / `Type`), so
//! existing call sites are unchanged; the engine's generic functions use
//! [`GenArg`] / [`GenConstructor`] / [`GenSig`] at `H::Term` / `H::Type`.

use covalence_core::{Term, Type};

/// One argument position of a [`GenConstructor`].
///
/// The `name` fields are binder hints: the engine quantifies over these
/// names when it builds the closure / induction clauses, so choosing
/// readable names (`"m"`, `"xs"`) makes the generated terms — and any
/// proof that assumes them — legible.
#[derive(Clone, Debug)]
pub enum GenArg<Ty> {
    /// A non-recursive parameter of type `ty` (may mention the inductive
    /// type's parameters `α⃗`, but not `T` itself), bound as `name`.
    Param { ty: Ty, name: &'static str },
    /// A direct recursive occurrence of the inductive type `T`. In a
    /// closure / induction clause the sub-term is bound as `name` and its
    /// recursive image (a value of the recursor's result type `β`) as
    /// `image`.
    Rec {
        name: &'static str,
        image: &'static str,
    },
}

impl<Ty: Clone> GenArg<Ty> {
    /// The type of this argument, given the inductive type `t` (`= T`).
    pub fn ty(&self, t: &Ty) -> Ty {
        match self {
            GenArg::Param { ty, .. } => ty.clone(),
            GenArg::Rec { .. } => t.clone(),
        }
    }
}

impl<Ty> GenArg<Ty> {
    /// The binder name of the argument itself.
    pub fn name(&self) -> &'static str {
        match self {
            GenArg::Param { name, .. } | GenArg::Rec { name, .. } => name,
        }
    }

    /// The image (recursive-result) binder name, for a recursive arg.
    pub fn image(&self) -> Option<&'static str> {
        match self {
            GenArg::Rec { image, .. } => Some(image),
            GenArg::Param { .. } => None,
        }
    }

    /// Whether this is a non-recursive parameter.
    pub fn is_param(&self) -> bool {
        matches!(self, GenArg::Param { .. })
    }

    /// Whether this is a recursive occurrence of `T`.
    pub fn is_rec(&self) -> bool {
        matches!(self, GenArg::Rec { .. })
    }
}

/// A single constructor `C : A₁ → … → Aₙ → T`.
#[derive(Clone, Debug)]
pub struct GenConstructor<Tm, Ty> {
    /// The constructor as a term, ready to be applied to its [`GenArg`]s
    /// left-to-right (e.g. the `succ` function, or the `nil` / `zero`
    /// constant for a nullary constructor).
    pub ctor: Tm,
    /// The argument signature, in declaration order.
    pub args: Vec<GenArg<Ty>>,
}

impl<Tm, Ty> GenConstructor<Tm, Ty> {
    /// A nullary constructor (a constant of type `T`, e.g. `zero` / `nil`).
    pub fn nullary(ctor: Tm) -> Self {
        GenConstructor {
            ctor,
            args: Vec::new(),
        }
    }

    /// A constructor with the given argument signature.
    pub fn new(ctor: Tm, args: Vec<GenArg<Ty>>) -> Self {
        GenConstructor { ctor, args }
    }

    /// The recursive argument positions, in order.
    pub fn rec_args(&self) -> impl Iterator<Item = &GenArg<Ty>> {
        self.args.iter().filter(|a| a.is_rec())
    }

    /// Whether the constructor has any recursive argument.
    pub fn is_recursive(&self) -> bool {
        self.args.iter().any(GenArg::is_rec)
    }
}

/// The signature of a basic inductive type.
#[derive(Clone, Debug)]
pub struct GenSig<Tm, Ty> {
    /// The inductive type `T`, at the chosen type parameters (e.g.
    /// `nat`, `list α`).
    pub ty: Ty,
    /// Binder name for the impredicative relation variable
    /// `G : T → β → bool` the graph construction quantifies over.
    pub relation: &'static str,
    /// The constructors, in declaration order. The engine expects one
    /// *step term* per constructor in the same order.
    pub ctors: Vec<GenConstructor<Tm, Ty>>,
}

impl<Tm, Ty> GenSig<Tm, Ty> {
    /// Number of constructors (= the recursor's number of step arguments).
    pub fn arity(&self) -> usize {
        self.ctors.len()
    }
}

/// One argument position, at the native `covalence-core` representation.
pub type Arg = GenArg<Type>;
/// A constructor, at the native `covalence-core` representation.
pub type Constructor = GenConstructor<Term, Type>;
/// An inductive-type signature, at the native `covalence-core`
/// representation. The engine's generic functions take a
/// [`GenSig`]`<H::Term, H::Type>`.
pub type InductiveSig = GenSig<Term, Type>;
