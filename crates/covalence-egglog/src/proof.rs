//! egglog 2.0 proof DAG, mirrored.
//!
//! Faithful re-encoding of the types in egglog's
//! [`src/proofs/proof_format.rs`](https://github.com/egraphs-good/egglog/blob/main/src/proofs/proof_format.rs).
//! Keeping the surface here lets the rest of the crate work without taking a
//! dependency on `egglog` itself; a future
//! `from_egglog_proofstore(&egglog::ProofStore) -> ProofStore` shim is the
//! only place upstream's representation needs to leak in.
//!
//! Two arenas:
//!   - a [`TermDag`] holding the first-order terms that appear in
//!     [`Proposition`]s, indexed by [`TermId`];
//!   - a [`ProofStore`] holding the [`Proof`] DAG, indexed by [`ProofId`].
//!
//! Both are append-only and assumed to be built bottom-up: a node's
//! dependencies have smaller indices than itself when constructed via
//! [`TermDag::alloc`] / [`ProofStore::alloc`]. The [`topological_order`]
//! helper produces a dependency-first walk for the driver.

use std::collections::{HashMap, HashSet};

/// Index of a [`Term`] inside a [`TermDag`].
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct TermId(pub u32);

/// A first-order term in the egglog universe.
///
/// Stage 0 only models user constants and user applications. Primitive
/// literals (`i64`, `String`, `Bool`) get their own variants once the kernel
/// bridge wires them up.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Term {
    /// A 0-ary user symbol — e.g. a declared `(let a (...))` or an enum
    /// constructor used with no arguments.
    Const(String),
    /// `name(args...)` — a user constructor applied to other terms in the
    /// same [`TermDag`].
    App(String, Vec<TermId>),
}

/// Append-only arena of [`Term`]s.
#[derive(Clone, Debug, Default)]
pub struct TermDag {
    nodes: Vec<Term>,
}

impl TermDag {
    /// Empty DAG.
    pub fn new() -> Self {
        Self::default()
    }

    /// Allocate `term`, returning its assigned [`TermId`]. Children referenced
    /// by `term` must already be present in `self` — the caller is
    /// responsible for bottom-up construction.
    pub fn alloc(&mut self, term: Term) -> TermId {
        let id = TermId(self.nodes.len() as u32);
        self.nodes.push(term);
        id
    }

    /// Look up a term by id.
    pub fn get(&self, id: TermId) -> Option<&Term> {
        self.nodes.get(id.0 as usize)
    }

    /// Number of allocated terms.
    pub fn len(&self) -> usize {
        self.nodes.len()
    }

    /// True if no terms have been allocated.
    pub fn is_empty(&self) -> bool {
        self.nodes.is_empty()
    }
}

/// An equality `lhs = rhs` between two terms in some [`TermDag`].
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct Proposition {
    pub lhs: TermId,
    pub rhs: TermId,
}

impl Proposition {
    pub fn new(lhs: TermId, rhs: TermId) -> Self {
        Self { lhs, rhs }
    }
}

/// Index of a [`Proof`] inside a [`ProofStore`].
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct ProofId(pub u32);

/// Why an equality holds.
///
/// Mirrors egglog 2.0's
/// [`Justification`](https://github.com/egraphs-good/egglog/blob/main/src/proofs/proof_format.rs)
/// enum exactly. Three variants are egglog axioms (`Trans`, `Sym`, `Congr`);
/// three correspond to user input or fired rules (`Fiat`, `Rule`, `MergeFn`).
#[derive(Clone, Debug)]
pub enum Justification {
    /// Top-level fact — either a `(union a b)` action or a primitive
    /// reflexive equality like `2 = 2`. egglog does **not** assume
    /// reflexivity in general: `t = t` is `Fiat`-justified only when `t`
    /// was added at the top level.
    Fiat,

    /// A user-declared rule fired under `substitution` after each premise
    /// equality was established by `premise_proofs[i]`.
    Rule {
        name: String,
        premise_proofs: Vec<ProofId>,
        substitution: HashMap<String, TermId>,
    },

    /// A merge function on `function` reconciled an old and a new row value.
    MergeFn {
        function: String,
        old_proof: ProofId,
        new_proof: ProofId,
    },

    /// `a = b ∧ b = c ⊢ a = c`.
    Trans(ProofId, ProofId),

    /// `a = b ⊢ b = a`.
    Sym(ProofId),

    /// Congruence at a single child position: extends `proof` (which
    /// concludes `t₁ = f(…, c_i, …)`) with `child_proof` (which concludes
    /// `c_i = c'`) to prove `t₁ = f(…, c', …)`.
    Congr {
        proof: ProofId,
        child_index: usize,
        child_proof: ProofId,
    },
}

/// One node in the proof DAG: a proposition and a justification for it.
#[derive(Clone, Debug)]
pub struct Proof {
    pub proposition: Proposition,
    pub justification: Justification,
}

/// Append-only arena of [`Proof`] nodes — the DAG itself.
#[derive(Clone, Debug, Default)]
pub struct ProofStore {
    nodes: Vec<Proof>,
}

impl ProofStore {
    /// Empty store.
    pub fn new() -> Self {
        Self::default()
    }

    /// Allocate `proof`, returning its assigned [`ProofId`].
    pub fn alloc(&mut self, proof: Proof) -> ProofId {
        let id = ProofId(self.nodes.len() as u32);
        self.nodes.push(proof);
        id
    }

    /// Look up a proof by id.
    pub fn get(&self, id: ProofId) -> Option<&Proof> {
        self.nodes.get(id.0 as usize)
    }

    /// Number of allocated proofs.
    pub fn len(&self) -> usize {
        self.nodes.len()
    }

    /// True if no proofs have been allocated.
    pub fn is_empty(&self) -> bool {
        self.nodes.is_empty()
    }
}

/// Direct dependencies of a justification — the proof ids the justification
/// references.
pub fn dependencies(j: &Justification) -> Vec<ProofId> {
    match j {
        Justification::Fiat => Vec::new(),
        Justification::Rule { premise_proofs, .. } => premise_proofs.clone(),
        Justification::MergeFn {
            old_proof,
            new_proof,
            ..
        } => vec![*old_proof, *new_proof],
        Justification::Trans(a, b) => vec![*a, *b],
        Justification::Sym(a) => vec![*a],
        Justification::Congr {
            proof, child_proof, ..
        } => vec![*proof, *child_proof],
    }
}

/// Dependency-first visit of every proof reachable from `root`.
///
/// Used by the driver: each call to a bridge method needs every premise's
/// `Thm` already resolved. The returned vector ends with `root`.
pub fn topological_order(store: &ProofStore, root: ProofId) -> Vec<ProofId> {
    enum Step {
        Enter(ProofId),
        Exit(ProofId),
    }

    let mut order = Vec::new();
    let mut visited: HashSet<ProofId> = HashSet::new();
    let mut stack = vec![Step::Enter(root)];

    while let Some(step) = stack.pop() {
        match step {
            Step::Enter(id) => {
                if !visited.insert(id) {
                    continue;
                }
                stack.push(Step::Exit(id));
                if let Some(p) = store.get(id) {
                    for dep in dependencies(&p.justification) {
                        stack.push(Step::Enter(dep));
                    }
                }
            }
            Step::Exit(id) => order.push(id),
        }
    }

    order
}
