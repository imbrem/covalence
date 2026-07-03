use crate::{Clause, Cnf, Decision, Lit, Var};

/// A (partial) assignment of truth values to variables, with backtracking.
///
/// Each variable maps to a [`Decision`]: `Sat` (true), `Unsat` (false), or
/// `Unknown` (unassigned). Evaluation uses Kleene three-valued logic via
/// `Decision` combinators. Variables are 1-indexed (DIMACS convention).
///
/// Use [`push`](Model::push) / [`pop`](Model::pop) for checkpoint-based
/// backtracking — all assignments made since the last `push` are undone on
/// `pop`.
///
/// ```
/// use covalence_sat::{Cnf, Model, Decision};
///
/// let mut cnf = Cnf::new();
/// let x = cnf.fresh();
/// let y = cnf.fresh();
/// cnf.clause([x, !y]); // x ∨ ¬y
///
/// let model = Model::from_total([true, false]);
/// assert_eq!(model.eval_cnf(&cnf), Decision::Sat);
/// ```
#[derive(Debug, Clone)]
pub struct Model {
    values: Vec<Decision>,
    trail: Vec<(Var, Decision)>,
    checkpoints: Vec<usize>,
}

impl PartialEq for Model {
    fn eq(&self, other: &Self) -> bool {
        self.values == other.values
    }
}

impl Eq for Model {}

impl Model {
    /// Create a model with all variables unassigned (`Unknown`).
    pub fn new(num_vars: u32) -> Self {
        Model {
            values: vec![Decision::Unknown; num_vars as usize],
            trail: Vec::new(),
            checkpoints: Vec::new(),
        }
    }

    /// Create a model from an iterator of [`Decision`] values.
    ///
    /// The i-th element corresponds to variable i+1.
    pub fn from_values(values: impl IntoIterator<Item = Decision>) -> Self {
        Model {
            values: values.into_iter().collect(),
            trail: Vec::new(),
            checkpoints: Vec::new(),
        }
    }

    /// Create a total model where every variable is assigned.
    ///
    /// The i-th element corresponds to variable i+1.
    pub fn from_total(values: impl IntoIterator<Item = bool>) -> Self {
        Model {
            values: values.into_iter().map(Decision::from).collect(),
            trail: Vec::new(),
            checkpoints: Vec::new(),
        }
    }

    /// Get the [`Decision`] for a variable.
    pub fn get_var(&self, var: Var) -> Decision {
        let idx = (var.index() - 1) as usize;
        self.values.get(idx).copied().unwrap_or(Decision::Unknown)
    }

    /// Get the [`Decision`] for a literal, accounting for polarity.
    ///
    /// For a negative literal, the decision is negated: `Sat ↔ Unsat`,
    /// `Unknown` stays `Unknown`.
    pub fn get(&self, lit: Lit) -> Decision {
        let val = self.get_var(lit.var());
        if lit.is_pos() { val } else { val.not() }
    }

    /// Set a variable's value.
    ///
    /// Accepts any type convertible to [`Decision`] — including `bool`
    /// (`true → Sat`, `false → Unsat`) and `Decision` directly.
    ///
    /// If there is an active checkpoint (from [`push`](Model::push)), the
    /// previous value is recorded for undo on [`pop`](Model::pop).
    pub fn set(&mut self, var: Var, value: impl Into<Decision>) {
        let idx = (var.index() - 1) as usize;
        if let Some(slot) = self.values.get_mut(idx) {
            if !self.checkpoints.is_empty() {
                self.trail.push((var, *slot));
            }
            *slot = value.into();
        }
    }

    /// Unset a variable (set to `Unknown`).
    pub fn unset(&mut self, var: Var) {
        self.set(var, Decision::Unknown);
    }

    /// Save a checkpoint. All subsequent [`set`](Model::set) calls can be
    /// undone by a matching [`pop`](Model::pop).
    pub fn push(&mut self) {
        self.checkpoints.push(self.trail.len());
    }

    /// Undo all assignments since the last [`push`](Model::push).
    ///
    /// # Panics
    ///
    /// Panics if there is no matching `push`.
    pub fn pop(&mut self) {
        let checkpoint = self
            .checkpoints
            .pop()
            .expect("Model::pop without matching push");
        while self.trail.len() > checkpoint {
            let (var, old) = self.trail.pop().unwrap();
            self.values[(var.index() - 1) as usize] = old;
        }
    }

    /// Evaluate a literal under this model.
    ///
    /// Equivalent to [`get`](Model::get) — returns the three-valued
    /// [`Decision`] for the literal under the current assignment.
    pub fn eval_lit(&self, lit: Lit) -> Decision {
        self.get(lit)
    }

    /// Evaluate a clause (disjunction) under this model.
    ///
    /// Folds with `Decision::or` — `Sat` dominates.
    /// Empty clause evaluates to `Unsat` (vacuously false).
    ///
    /// ```
    /// use covalence_sat::{Cnf, Clause, Model, Decision};
    ///
    /// let mut cnf = Cnf::new();
    /// let x = cnf.fresh();
    /// let y = cnf.fresh();
    ///
    /// // Partial model: x=Sat, y=Unknown
    /// let model = Model::from_values([Decision::Sat, Decision::Unknown]);
    /// let clause = Clause::new([x, !y]);
    /// assert_eq!(model.eval_clause(&clause), Decision::Sat);
    /// ```
    pub fn eval_clause(&self, clause: &Clause) -> Decision {
        clause
            .lits()
            .iter()
            .fold(Decision::Unsat, |acc, &lit| acc.or(self.eval_lit(lit)))
    }

    /// Evaluate a CNF formula (conjunction) under this model.
    ///
    /// Folds with `Decision::and` — `Unsat` dominates.
    /// Empty formula evaluates to `Sat` (vacuously true).
    ///
    /// ```
    /// use covalence_sat::{Cnf, Model, Decision};
    ///
    /// let cnf = Cnf::new(); // empty formula
    /// let model = Model::new(0);
    /// assert_eq!(model.eval_cnf(&cnf), Decision::Sat);
    /// ```
    pub fn eval_cnf(&self, cnf: &Cnf) -> Decision {
        cnf.clauses().fold(Decision::Sat, |acc, clause| {
            acc.and(self.eval_clause(clause))
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use Decision::*;

    fn make_simple_cnf() -> (Cnf, Lit, Lit) {
        let mut cnf = Cnf::new();
        let x = cnf.fresh();
        let y = cnf.fresh();
        // (x ∨ ¬y) ∧ (¬x ∨ y) — satisfied iff x = y
        cnf.clause([x, !y]);
        cnf.clause([!x, y]);
        (cnf, x, y)
    }

    #[test]
    fn total_model_sat() {
        let (cnf, _, _) = make_simple_cnf();
        let model = Model::from_total([true, true]);
        assert_eq!(model.eval_cnf(&cnf), Sat);
    }

    #[test]
    fn total_model_unsat() {
        let (cnf, _, _) = make_simple_cnf();
        let model = Model::from_total([true, false]);
        assert_eq!(model.eval_cnf(&cnf), Unsat);
    }

    #[test]
    fn partial_model_unknown() {
        let (cnf, _, _) = make_simple_cnf();
        // x=Sat, y=Unknown: clause1 = Sat, clause2 = (Unsat ∨ Unknown) = Unknown
        let model = Model::from_values([Sat, Unknown]);
        assert_eq!(model.eval_cnf(&cnf), Unknown);
    }

    #[test]
    fn partial_model_sat() {
        let mut cnf = Cnf::new();
        let x = cnf.fresh();
        let _y = cnf.fresh();
        cnf.clause([x]); // just (x)
        let model = Model::from_values([Sat, Unknown]);
        assert_eq!(model.eval_cnf(&cnf), Sat);
    }

    #[test]
    fn empty_clause_is_unsat() {
        let model = Model::new(0);
        let empty_clause = Clause::new([]);
        assert_eq!(model.eval_clause(&empty_clause), Unsat);
    }

    #[test]
    fn empty_formula_is_sat() {
        let cnf = Cnf::new();
        let model = Model::new(0);
        assert_eq!(model.eval_cnf(&cnf), Sat);
    }

    #[test]
    fn formula_with_empty_clause_is_unsat() {
        let mut cnf = Cnf::new();
        let x = cnf.fresh();
        cnf.clause([x]);
        cnf.clause([]);
        let model = Model::from_total([true]);
        assert_eq!(model.eval_cnf(&cnf), Unsat);
    }

    #[test]
    fn eval_lit_polarity() {
        let mut cnf = Cnf::new();
        let x = cnf.fresh();
        let model = Model::from_total([true]);
        assert_eq!(model.eval_lit(x), Sat);
        assert_eq!(model.eval_lit(!x), Unsat);
    }

    #[test]
    fn get_handles_polarity() {
        let mut cnf = Cnf::new();
        let x = cnf.fresh();
        let model = Model::from_total([false]);
        assert_eq!(model.get(x), Unsat);
        assert_eq!(model.get(!x), Sat);
    }

    #[test]
    fn set_and_unset() {
        let mut cnf = Cnf::new();
        let x = cnf.fresh();

        let mut model = Model::new(1);
        assert_eq!(model.get_var(x.var()), Unknown);

        model.set(x.var(), true);
        assert_eq!(model.get_var(x.var()), Sat);

        model.unset(x.var());
        assert_eq!(model.get_var(x.var()), Unknown);
    }

    #[test]
    fn set_with_decision() {
        let mut cnf = Cnf::new();
        let x = cnf.fresh();

        let mut model = Model::new(1);
        model.set(x.var(), Sat);
        assert_eq!(model.get_var(x.var()), Sat);

        model.set(x.var(), Unknown);
        assert_eq!(model.get_var(x.var()), Unknown);
    }

    #[test]
    fn both_satisfying_assignments() {
        let (cnf, _, _) = make_simple_cnf();
        assert_eq!(Model::from_total([true, true]).eval_cnf(&cnf), Sat);
        assert_eq!(Model::from_total([false, false]).eval_cnf(&cnf), Sat);
    }

    #[test]
    fn both_falsifying_assignments() {
        let (cnf, _, _) = make_simple_cnf();
        assert_eq!(Model::from_total([true, false]).eval_cnf(&cnf), Unsat);
        assert_eq!(Model::from_total([false, true]).eval_cnf(&cnf), Unsat);
    }

    // --- push / pop ---

    #[test]
    fn push_pop_restores() {
        let mut cnf = Cnf::new();
        let x = cnf.fresh();
        let y = cnf.fresh();

        let mut model = Model::new(2);
        model.set(x.var(), true);
        assert_eq!(model.get_var(x.var()), Sat);

        model.push();
        model.set(x.var(), false);
        model.set(y.var(), true);
        assert_eq!(model.get_var(x.var()), Unsat);
        assert_eq!(model.get_var(y.var()), Sat);

        model.pop();
        assert_eq!(model.get_var(x.var()), Sat);
        assert_eq!(model.get_var(y.var()), Unknown);
    }

    #[test]
    fn nested_push_pop() {
        let mut cnf = Cnf::new();
        let x = cnf.fresh();

        let mut model = Model::new(1);

        model.push();
        model.set(x.var(), true);
        assert_eq!(model.get_var(x.var()), Sat);

        model.push();
        model.set(x.var(), false);
        assert_eq!(model.get_var(x.var()), Unsat);

        model.pop(); // inner
        assert_eq!(model.get_var(x.var()), Sat);

        model.pop(); // outer
        assert_eq!(model.get_var(x.var()), Unknown);
    }

    #[test]
    fn push_pop_no_changes() {
        let mut cnf = Cnf::new();
        let x = cnf.fresh();
        let y = cnf.fresh();

        let mut model = Model::from_total([true, false]);
        model.push();
        model.pop();
        assert_eq!(model.get_var(x.var()), Sat);
        assert_eq!(model.get_var(y.var()), Unsat);
    }

    #[test]
    #[should_panic(expected = "pop without matching push")]
    fn pop_without_push_panics() {
        let mut model = Model::new(1);
        model.pop();
    }

    #[test]
    fn equality_ignores_trail() {
        let mut cnf = Cnf::new();
        let x = cnf.fresh();
        let y = cnf.fresh();

        let a = Model::from_total([true, false]);

        let mut b = Model::new(2);
        b.push();
        b.set(x.var(), true);
        b.set(y.var(), false);

        assert_eq!(a, b);
    }
}
