//! The **signature** of a basic inductive type — the data the recursion
//! engine ([`super::graph`]) consumes to build a recursor generically.
//!
//! "Basic" here means: single-sorted, parametric, first-order,
//! strictly-positive, and *directly* recursive — every recursive argument
//! has the inductive type `T` itself, never `F⟨T⟩` under some other
//! functor `F`. That covers `nat` (`zero`, `succ`), `list` (`nil`,
//! `cons`), binary trees, and the like; nested / mutual / infinitary
//! types are deliberately out of scope (see `SKELETONS.md`).
//!
//! A signature is a *description*, not a proof: it names the type, the
//! impredicative relation variable used in the graph construction, and
//! each constructor with its argument shape. The engine turns that into
//! the recursion graph, its totality / determinacy proofs, and finally
//! the recursor — but those steps additionally need the *freeness* and
//! *induction* facts the kernel or the carrier supplies separately.

use covalence_core::{Term, Type};

/// One argument position of a [`Constructor`].
///
/// The `name` fields are binder hints: the engine quantifies over these
/// names when it builds the closure / induction clauses, so choosing
/// readable names (`"m"`, `"xs"`) makes the generated terms — and any
/// proof that `Thm::assume`s them — legible.
#[derive(Clone, Debug)]
pub enum Arg {
    /// A non-recursive parameter of type `ty` (may mention the inductive
    /// type's parameters `α⃗`, but not `T` itself), bound as `name`.
    Param { ty: Type, name: &'static str },
    /// A direct recursive occurrence of the inductive type `T`. In a
    /// closure / induction clause the sub-term is bound as `name` and its
    /// recursive image (a value of the recursor's result type `β`) as
    /// `image`.
    Rec {
        name: &'static str,
        image: &'static str,
    },
}

impl Arg {
    /// The type of this argument, given the inductive type `t` (`= T`).
    pub fn ty(&self, t: &Type) -> Type {
        match self {
            Arg::Param { ty, .. } => ty.clone(),
            Arg::Rec { .. } => t.clone(),
        }
    }

    /// The binder name of the argument itself.
    pub fn name(&self) -> &'static str {
        match self {
            Arg::Param { name, .. } | Arg::Rec { name, .. } => name,
        }
    }

    /// The image (recursive-result) binder name, for a recursive arg.
    pub fn image(&self) -> Option<&'static str> {
        match self {
            Arg::Rec { image, .. } => Some(image),
            Arg::Param { .. } => None,
        }
    }

    /// Whether this is a non-recursive parameter.
    pub fn is_param(&self) -> bool {
        matches!(self, Arg::Param { .. })
    }

    /// Whether this is a recursive occurrence of `T`.
    pub fn is_rec(&self) -> bool {
        matches!(self, Arg::Rec { .. })
    }
}

/// A single constructor `C : A₁ → … → Aₙ → T`.
#[derive(Clone, Debug)]
pub struct Constructor {
    /// The constructor as a term, ready to be applied to its [`Arg`]s
    /// left-to-right (e.g. the `succ` function, or the `nil` / `zero`
    /// constant for a nullary constructor).
    pub ctor: Term,
    /// The argument signature, in declaration order.
    pub args: Vec<Arg>,
}

impl Constructor {
    /// A nullary constructor (a constant of type `T`, e.g. `zero` / `nil`).
    pub fn nullary(ctor: Term) -> Self {
        Constructor { ctor, args: Vec::new() }
    }

    /// A constructor with the given argument signature.
    pub fn new(ctor: Term, args: Vec<Arg>) -> Self {
        Constructor { ctor, args }
    }

    /// The recursive argument positions, in order.
    pub fn rec_args(&self) -> impl Iterator<Item = &Arg> {
        self.args.iter().filter(|a| a.is_rec())
    }

    /// Whether the constructor has any recursive argument.
    pub fn is_recursive(&self) -> bool {
        self.args.iter().any(Arg::is_rec)
    }
}

/// The signature of a basic inductive type.
#[derive(Clone, Debug)]
pub struct InductiveSig {
    /// The inductive type `T`, at the chosen type parameters (e.g.
    /// `nat`, `list α`).
    pub ty: Type,
    /// Binder name for the impredicative relation variable
    /// `G : T → β → bool` the graph construction quantifies over.
    pub relation: &'static str,
    /// The constructors, in declaration order. The engine expects one
    /// *step term* per constructor in the same order.
    pub ctors: Vec<Constructor>,
}

impl InductiveSig {
    /// Number of constructors (= the recursor's number of step arguments).
    pub fn arity(&self) -> usize {
        self.ctors.len()
    }
}
