//! `KernelEgglogBridge` — concrete [`EgglogBridge`] impl against any
//! `covalence_shell::Prover`.
//!
//! This is the **only** file in the crate that mentions specific prover
//! operations. The trait surface ([`EgglogBridge`]) and the driver stay
//! stable while this file (and the underlying `Prover` impl) churn alongside
//! the kernel.
//!
//! Today the bridge:
//!
//!   - Translates egglog sort symbols and user constructors into `Prover`
//!     `Type` / `Term` handles, caching constants so the same egglog
//!     symbol always produces the same `Term` (required for any future
//!     UF-based congruence to fire).
//!   - Materialises [`Term`] DAG nodes into `Prover` terms via repeated
//!     `comb` applications.
//!   - Implements [`Justification::Fiat`](crate::proof::Justification::Fiat)
//!     by either calling `Prover::refl` (when `lhs == rhs` as `TermRef`s)
//!     or by pushing the equality as an assumption and calling
//!     `Prover::assume`.
//!   - Implements [`Justification::Trans`](crate::proof::Justification::Trans)
//!     and [`Justification::Sym`](crate::proof::Justification::Sym) by
//!     calling through to the prover's own primitives — the kernel
//!     validates the shape of the input theorems.
//!   - Implements [`Justification::Congr`](crate::proof::Justification::Congr)
//!     by injecting both premise equalities into the UF and closing the
//!     conclusion via `Prover::cong`. Egglog's `child_index` is implicit:
//!     the kernel walks the term tree and reconciles wherever the UF
//!     says two subterms are equal.
//!   - The remaining justifications (`Rule`, `MergeFn`) fall through to
//!     the trait default, returning [`BridgeError::NotImplemented`]
//!     tagged with the variant.

use std::collections::HashMap;

use covalence_shell::Prover;

use crate::bridge::EgglogBridge;
use crate::error::BridgeError;
use crate::proof::{
    Justification, ProofId, ProofStore, Proposition, Term, TermDag, TermId, topological_order,
};

/// Bridge an egglog proof DAG into any `P: Prover`.
///
/// Owns:
///   - a mutable prover borrow,
///   - the egglog sort symbol → kernel `Type` map,
///   - the egglog constructor symbol → (kernel `Type`, cached const `Term`)
///     map. Caching keeps every reference to the same egglog constructor
///     pointing at one canonical `Term`, so equality at the term level is
///     stable across the proof.
///   - a memo from [`TermId`] to already-materialised `Term`. The proof DAG
///     can reference the same term many times; materialising it once is
///     cheap and avoids re-translation costs.
pub struct KernelEgglogBridge<'a, P: Prover> {
    prover: &'a mut P,
    sorts: HashMap<String, P::Type>,
    /// `name → (declared kernel type, cached const Term)`. The `Type` is the
    /// *full* function type (already curried for n-ary constructors); the
    /// `Term` is the const symbol that gets `comb`-applied to arguments.
    constructors: HashMap<String, (P::Type, P::Term)>,
    /// `name → arity` for declared constructors. Stored separately from
    /// [`Self::constructors`] so the materialiser can check application
    /// arity without unpacking the kernel type.
    arities: HashMap<String, usize>,
    /// Memo for materialised proof-DAG terms.
    term_cache: HashMap<TermId, P::Term>,
    /// `(lhs, rhs) → eq Term` memo. The kernel doesn't hash-cons compound
    /// terms, so without this memo two calls to `prover.eq(a, b)` would
    /// return distinct `P::Term`s — breaking [`Self::fiat_props`]'s
    /// `eq_term` key. See the matching `eq_memo` in `covalence-alethe`.
    eq_memo: HashMap<(P::Term, P::Term), P::Term>,
    /// `eq_term → Prop` cache for [`Justification::Fiat`] equalities. Filled
    /// by [`KernelEgglogBridge::pre_walk`] before any other dispatch runs,
    /// so every `assume` in the topo walk sees the *full* assumption set on
    /// the context — required for `trans` / `sym` over Fiat-derived Thms
    /// not to trip the kernel's `ContextMismatch` check. See
    /// `docs/prop-egraph-design.md` for the underlying context model.
    fiat_props: HashMap<P::Term, P::Prop>,
}

impl<'a, P: Prover> KernelEgglogBridge<'a, P> {
    /// Build a fresh bridge wrapping the given prover.
    pub fn new(prover: &'a mut P) -> Self {
        Self {
            prover,
            sorts: HashMap::new(),
            constructors: HashMap::new(),
            arities: HashMap::new(),
            term_cache: HashMap::new(),
            eq_memo: HashMap::new(),
            fiat_props: HashMap::new(),
        }
    }

    /// Memoised `prover.eq(a, b)` — keeps a single canonical `P::Term` per
    /// `(lhs, rhs)` pair so `fiat_props` lookups round-trip.
    fn mk_eq(&mut self, a: P::Term, b: P::Term) -> Result<P::Term, BridgeError> {
        if let Some(t) = self.eq_memo.get(&(a, b)).copied() {
            return Ok(t);
        }
        let t = self.prover.eq(a, b)?;
        self.eq_memo.insert((a, b), t);
        Ok(t)
    }

    /// Borrow the underlying prover (e.g. for inspecting kernel state in
    /// tests).
    pub fn prover(&self) -> &P {
        self.prover
    }

    /// Look up a declared sort by egglog symbol.
    pub fn lookup_sort(&self, name: &str) -> Option<P::Type> {
        self.sorts.get(name).copied()
    }

    /// Look up a declared constructor's *type* by egglog symbol.
    pub fn lookup_constructor_ty(&self, name: &str) -> Option<P::Type> {
        self.constructors.get(name).map(|(ty, _)| *ty)
    }

    /// Materialise a [`TermId`] from `dag` into a `P::Term`, recursing on
    /// children and memoising results. Constants resolve to their cached
    /// const-term; applications head-resolve and `comb` left-to-right.
    fn materialise(&mut self, id: TermId, dag: &TermDag) -> Result<P::Term, BridgeError> {
        if let Some(cached) = self.term_cache.get(&id).copied() {
            return Ok(cached);
        }

        let term = dag.get(id).ok_or(BridgeError::UndefinedTerm(id.0))?;
        let materialised = match term {
            Term::Const(name) => self.lookup_const_term(name)?,
            Term::App(name, args) => {
                let head = self.lookup_const_term(name)?;
                let expected_arity = self
                    .arity_of(name)
                    .ok_or_else(|| BridgeError::UnknownConstructor(name.clone()))?;
                if expected_arity != args.len() {
                    return Err(BridgeError::ArityMismatch {
                        name: name.clone(),
                        expected: expected_arity,
                        actual: args.len(),
                    });
                }
                let mut acc = head;
                for arg_id in args {
                    let arg = self.materialise(*arg_id, dag)?;
                    acc = self.prover.comb(acc, arg)?;
                }
                acc
            }
        };
        self.term_cache.insert(id, materialised);
        Ok(materialised)
    }

    /// Look up a constructor's cached const-term.
    fn lookup_const_term(&self, name: &str) -> Result<P::Term, BridgeError> {
        self.constructors
            .get(name)
            .map(|(_, term)| *term)
            .ok_or_else(|| BridgeError::UnknownConstructor(name.to_string()))
    }

    /// Number of declared parameters for `name`, or `None` if undeclared.
    fn arity_of(&self, name: &str) -> Option<usize> {
        self.arities.get(name).copied()
    }
}

impl<'a, P: Prover> EgglogBridge for KernelEgglogBridge<'a, P> {
    type Thm = P::Thm;

    fn declare_sort(&mut self, name: &str) -> Result<(), BridgeError> {
        let ty = self.prover.tyapp(name, &[])?;
        self.sorts.insert(name.to_string(), ty);
        Ok(())
    }

    fn declare_constructor(
        &mut self,
        name: &str,
        params: &[&str],
        result_sort: &str,
    ) -> Result<(), BridgeError> {
        let result_ty = self
            .sorts
            .get(result_sort)
            .copied()
            .ok_or_else(|| BridgeError::UnknownSort(result_sort.to_string()))?;

        // Build the curried function type result_ty <- params[n-1] <- … <- params[0].
        let mut ty = result_ty;
        for p in params.iter().rev() {
            let pty = self
                .sorts
                .get(*p)
                .copied()
                .ok_or_else(|| BridgeError::UnknownSort((*p).to_string()))?;
            ty = self.prover.fun_ty(pty, ty)?;
        }

        let const_term = self.prover.const_term(name, ty)?;
        self.constructors
            .insert(name.to_string(), (ty, const_term));
        self.arities.insert(name.to_string(), params.len());
        Ok(())
    }

    fn pre_walk(
        &mut self,
        store: &ProofStore,
        dag: &TermDag,
        root: ProofId,
    ) -> Result<(), BridgeError> {
        // Push every non-reflexive Fiat equality onto the kernel's context
        // *before* any other dispatch runs, so all derived Thms share the
        // same assumption chain. Reflexive Fiats (`t = t`) need no push —
        // they're discharged via `refl` inside `fiat`.
        for id in topological_order(store, root) {
            let proof = store
                .get(id)
                .ok_or(BridgeError::UndefinedProof(id.0))?;
            if !matches!(proof.justification, Justification::Fiat) {
                continue;
            }
            let lhs = self.materialise(proof.proposition.lhs, dag)?;
            let rhs = self.materialise(proof.proposition.rhs, dag)?;
            if lhs == rhs {
                continue;
            }
            let eq_term = self.mk_eq(lhs, rhs)?;
            // Idempotent on the eq term: two Fiat nodes asserting the same
            // equality reuse one Prop, one push.
            if self.fiat_props.contains_key(&eq_term) {
                continue;
            }
            let prop = self.prover.push_assumption(eq_term)?;
            self.fiat_props.insert(eq_term, prop);
        }
        Ok(())
    }

    fn fiat(
        &mut self,
        prop: &Proposition,
        dag: &TermDag,
    ) -> Result<Self::Thm, BridgeError> {
        let lhs = self.materialise(prop.lhs, dag)?;
        let rhs = self.materialise(prop.rhs, dag)?;

        // Primitive reflexive equality — `t = t` for a t already in the
        // arena. Egglog Fiat-justifies these explicitly; we discharge with
        // `refl`, no assumption pushed.
        if lhs == rhs {
            return Ok(self.prover.refl(lhs)?);
        }

        // Top-level union: the equality is already on the context (pushed
        // during `pre_walk`); just `assume` the cached Prop. This is what
        // keeps every Fiat-derived Thm in the same context — the
        // precondition for `trans` / `sym` to compose across them.
        let eq_term = self.mk_eq(lhs, rhs)?;
        let prop_handle = self
            .fiat_props
            .get(&eq_term)
            .cloned()
            .ok_or_else(|| {
                BridgeError::Malformed(
                    "Fiat equality missing from pre_walk cache — was \
                     ingest_proof_store bypassed?"
                        .into(),
                )
            })?;
        Ok(self.prover.assume(prop_handle)?)
    }

    fn trans(
        &mut self,
        _prop: &Proposition,
        ab: Self::Thm,
        bc: Self::Thm,
        _dag: &TermDag,
    ) -> Result<Self::Thm, BridgeError> {
        Ok(self.prover.trans(ab, bc)?)
    }

    fn sym(
        &mut self,
        _prop: &Proposition,
        ab: Self::Thm,
        _dag: &TermDag,
    ) -> Result<Self::Thm, BridgeError> {
        Ok(self.prover.sym(ab)?)
    }

    fn congr(
        &mut self,
        prop: &Proposition,
        proof_thm: Self::Thm,
        _child_index: usize,
        child_thm: Self::Thm,
        dag: &TermDag,
    ) -> Result<Self::Thm, BridgeError> {
        // Inject both premise equalities into the kernel's UF. Egglog's
        // `child_index` is implicit for us — the kernel's `cong` walks the
        // term tree itself and reconciles wherever the UF says two
        // subterms are equal. Same pattern as covalence-alethe's
        // `rule_cong`.
        self.inject_equality(&proof_thm)?;
        self.inject_equality(&child_thm)?;

        let lhs = self.materialise(prop.lhs, dag)?;
        let rhs = self.materialise(prop.rhs, dag)?;

        // Depth 32 is generously larger than anything egglog emits — egglog
        // Congr steps move by a single child position, but our kernel's
        // cong takes the whole tree at once and we don't want a recursion
        // cap to surface as a spurious failure.
        Ok(self.prover.cong(lhs, rhs, 32)?)
    }
}

impl<'a, P: Prover> KernelEgglogBridge<'a, P> {
    /// Destructure `th`'s conclusion as an equality and `union` its two
    /// sides into the kernel's UF. Used by [`EgglogBridge::congr`] to make
    /// premise equalities visible to `Prover::cong`.
    fn inject_equality(&mut self, th: &P::Thm) -> Result<(), BridgeError> {
        let concl = self.prover.conclusion(th)?;
        let (a, b) = self.prover.dest_eq(concl).ok_or_else(|| {
            BridgeError::Malformed("congr premise is not an equality".into())
        })?;
        self.prover.union(a, b)?;
        Ok(())
    }
}
