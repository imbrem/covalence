//! A small egglog source AST — just enough to drive Fiat-only EUF proofs
//! end-to-end from `.egg` text.
//!
//! Scope deliberately minimal: this is *not* a complete egglog parser. It
//! covers the commands needed to declare a signature, assert ground
//! equalities, and designate a target equality to ingest as a [`Proof`].
//! Rewrites, datatypes-with-arity, schedules, relations, run/check, etc.
//! all sit outside the scope here — they belong to later Stages.
//!
//! The supported subset is in 1-1 correspondence with what
//! [`KernelEgglogBridge`](crate::KernelEgglogBridge) wires through
//! kernel-checked (i.e. without the `Rule` trust shim). Once we add the
//! external-egglog dep we'll consume real proof DAGs from upstream and
//! this AST stays small for hand-written fixtures and tests.

/// One top-level egglog command in the supported subset.
///
/// The subset is exactly what [`crate::lower::lower_program`] knows how to
/// translate to declarations + a Fiat-only [`crate::ProofStore`]. The
/// `Datatype` form is sugar for one [`Command::Sort`] plus one
/// [`Command::Constructor`] per variant.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Command {
    /// `(sort Name)` — declare an eqsort.
    Sort(String),

    /// `(constructor name (P₁ … Pₙ) R)` — declare a constructor of arity
    /// `n` whose result sort is `R`. 0-ary constructors (`(constructor a
    /// () U)`) are the common case for ground constants.
    Constructor {
        name: String,
        params: Vec<String>,
        result: String,
    },

    /// `(datatype Name (Ctor₁ A …) (Ctor₂ B …) …)` — sugar combining a
    /// `Sort` declaration with one `Constructor` per variant, all of whose
    /// result sorts are `Name`.
    Datatype {
        name: String,
        ctors: Vec<(String, Vec<String>)>,
    },

    /// `(union lhs rhs)` — assert that `lhs` and `rhs` are equal. Each
    /// `Union` lowers to one [`crate::Justification::Fiat`] proof node.
    Union(Expr, Expr),

    /// `(prove (= lhs rhs))` — designate `lhs = rhs` as the root of the
    /// proof we want the bridge to ingest. Egglog 2.0's `(prove …)`
    /// triggers proof-DAG materialisation; here, since we don't run a
    /// solver, we look up an existing Fiat with matching sides.
    Prove(Expr, Expr),
}

/// An egglog expression — either a bare symbol or a head-applied term.
///
/// `Eq + Hash` is required because [`crate::lower::lower_program`] uses
/// pairs of [`Expr`]s as HashMap keys to match `(prove (= a b))` against
/// the [`Command::Union`] that asserted the equality.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Expr {
    /// A bare symbol — typically a 0-ary constructor name.
    Sym(String),
    /// `(head arg₁ arg₂ …)`.
    App(String, Vec<Expr>),
}
