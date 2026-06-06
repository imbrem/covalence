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
//!   - Every other justification falls through to the trait default,
//!     returning [`BridgeError::NotImplemented`] tagged with the variant.

use std::collections::HashMap;

use covalence_shell::Prover;

use crate::bridge::EgglogBridge;
use crate::error::BridgeError;
use crate::proof::{Proposition, Term, TermDag, TermId};

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
        }
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

        // Top-level union: push the equality as a context assumption, then
        // `assume`. The resulting Thm has the equality both as a hypothesis
        // and as its conclusion — the same shape an Alethe `(assume id φ)`
        // step produces.
        let eq_term = self.prover.eq(lhs, rhs)?;
        let prop_handle = self.prover.push_assumption(eq_term)?;
        Ok(self.prover.assume(prop_handle)?)
    }
}
