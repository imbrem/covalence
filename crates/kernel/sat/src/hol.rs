//! [`HolClauseBackend`] — a [`ClauseBackend`] backed by the `covalence-core`
//! HOL kernel.
//!
//! A SAT variable `Var(i)` becomes the boolean free variable `xi : bool`; a
//! clause becomes the right-associated `∨` of its literal terms (a positive
//! literal is the variable, a negative literal its `¬`); the empty clause is
//! `F`. `assume_clause` mints `⊢ C` as a hypothesis, `resolve` is propositional
//! resolution from [`covalence_init::init::logic`], and a theorem is the empty
//! clause when its conclusion is the boolean `false`.
//!
//! Because every input clause enters as an *assumption*, a derived `⊢ F` whose
//! hypotheses are all input clauses is a genuine refutation of the CNF —
//! nothing is trusted beyond the kernel's own inference. The backend adds
//! **zero TCB**: it only drives the trusted kernel API.

use covalence_core::{Term, Type};
use covalence_hol_eval::EvalThm as Thm;
use covalence_init::HolLightCtx;
use covalence_init::init::logic;
use covalence_sat::{Clause, Lit};

use crate::{ClauseBackend, ReplayError, SatProblem};

/// A [`ClauseBackend`] that reads clauses as HOL boolean disjunctions and
/// resolves through the `covalence-core` kernel. Its [`SatProblem`] lowering
/// maps `Var(i)` to `xi : bool`; the proof seam assumes and resolves.
#[derive(Default)]
pub struct HolClauseBackend {
    ctx: HolLightCtx,
}

impl HolClauseBackend {
    /// A fresh backend.
    pub fn new() -> Self {
        Self {
            ctx: HolLightCtx::new(),
        }
    }

    /// The boolean variable term for a literal's variable: `xi : bool`.
    fn var_term(lit: Lit) -> Term {
        Term::free(format!("x{}", lit.var().index()), Type::bool())
    }
}

impl SatProblem for HolClauseBackend {
    type Term = Term;

    /// A literal's HOL term: the variable positively, `¬`-wrapped negatively.
    fn lit(&self, lit: Lit) -> Term {
        let v = Self::var_term(lit);
        if lit.is_pos() { v } else { self.ctx.mk_not(v) }
    }

    /// The clause term: the right-associated `∨` of its literals, `F` when empty
    /// — the encoding `init::logic` resolves over.
    fn clause(&self, clause: &Clause) -> Term {
        match clause.lits() {
            [] => self.falsity(),
            [only] => self.lit(*only),
            [rest @ .., last] => {
                // Fold from the right so the spine is `l₀ ∨ (l₁ ∨ … ∨ lₙ)`.
                let mut acc = self.lit(*last);
                for lit in rest.iter().rev() {
                    acc = self.ctx.mk_or(self.lit(*lit), acc);
                }
                acc
            }
        }
    }

    fn falsity(&self) -> Term {
        Term::bool_lit(false)
    }
}

impl ClauseBackend for HolClauseBackend {
    type Thm = Thm;

    fn assume_clause(&mut self, clause: &Clause) -> Result<Self::Thm, ReplayError> {
        Thm::assume(self.clause(clause)).map_err(|e| ReplayError::Backend(e.to_string()))
    }

    fn resolve(&mut self, a: &Self::Thm, b: &Self::Thm) -> Result<Self::Thm, ReplayError> {
        logic::resolve(a.clone(), b.clone()).map_err(|e| ReplayError::Backend(e.to_string()))
    }

    fn is_empty_clause(&self, thm: &Self::Thm) -> bool {
        matches!(thm.concl().as_bool(), Some(false))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use covalence_sat::Cnf;

    /// The [`SatProblem`] lowering yields a `Term` with no proof — a clause is a
    /// disjunction, the empty clause is falsity, a literal is (negated) var.
    #[test]
    fn problem_lowering_is_term_only() {
        let mut cnf = Cnf::new();
        let (x, y) = (cnf.fresh(), cnf.fresh());
        let b = HolClauseBackend::new();

        // A clause is a `∨` term; no theorem involved.
        let term = b.clause(&Clause::new([x, !y]));
        let expected = b.ctx.mk_or(b.lit(x), b.lit(!y));
        assert_eq!(term, expected);

        // The empty clause lowers to falsity.
        assert_eq!(b.clause(&Clause::new([])), b.falsity());
        assert_eq!(b.falsity(), Term::bool_lit(false));
    }

    #[test]
    fn empty_clause_is_false() {
        let mut b = HolClauseBackend::new();
        let thm = b.assume_clause(&Clause::new([])).unwrap();
        assert!(b.is_empty_clause(&thm));
    }

    #[test]
    fn unit_clause_is_not_empty() {
        let mut cnf = Cnf::new();
        let x = cnf.fresh();
        let mut b = HolClauseBackend::new();
        let thm = b.assume_clause(&Clause::new([x])).unwrap();
        assert!(!b.is_empty_clause(&thm));
        assert_eq!(thm.concl(), &Term::free("x1", Type::bool()));
    }

    #[test]
    fn resolve_unit_and_negation_is_empty() {
        // {x} and {¬x} resolve to the empty clause ⊢ F.
        let mut cnf = Cnf::new();
        let x = cnf.fresh();
        let mut b = HolClauseBackend::new();
        let px = b.assume_clause(&Clause::new([x])).unwrap();
        let nx = b.assume_clause(&Clause::new([!x])).unwrap();
        let empty = b.resolve(&px, &nx).unwrap();
        assert!(b.is_empty_clause(&empty));
        // Its hypotheses are exactly the two input clauses.
        assert_eq!(empty.hyps().len(), 2);
    }
}
