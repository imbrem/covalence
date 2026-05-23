use std::fmt;
use std::num::NonZeroI32;

/// A propositional variable, 1-indexed.
///
/// Wraps a positive [`NonZeroI32`], following the DIMACS convention where
/// variables are numbered 1, 2, 3, … Variables are created exclusively
/// through [`Cnf::fresh`]. Use [`Var::pos`] / [`Var::neg`] to obtain literals.
///
/// ```
/// use covalence_sat::Cnf;
///
/// let mut cnf = Cnf::new();
/// let x = cnf.fresh();
/// assert_eq!(x.var().index(), 1);
/// assert_eq!(x.to_string(), "x1");
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Var(NonZeroI32); // invariant: always positive

impl Var {
    /// Create a variable from a positive index. Restricted to crate internals —
    /// users obtain variables via [`Cnf::fresh`].
    ///
    /// # Panics
    ///
    /// Panics if `index` is not positive.
    pub(crate) fn new(index: NonZeroI32) -> Self {
        assert!(index.get() > 0, "Var index must be positive");
        Var(index)
    }

    /// The 1-based index of this variable.
    pub fn index(self) -> i32 {
        self.0.get()
    }

    /// Positive literal for this variable.
    pub fn pos(self) -> Lit {
        Lit(self.0)
    }

    /// Negative literal for this variable.
    pub fn neg(self) -> Lit {
        // Safe: self.0 is positive NonZeroI32, negation is negative NonZeroI32
        Lit(self.0.checked_neg().expect("variable index overflow"))
    }
}

impl fmt::Display for Var {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "x{}", self.0)
    }
}

/// A signed literal, following the DIMACS convention.
///
/// Wraps a [`NonZeroI32`]: positive values represent positive literals,
/// negative values represent negative literals. The absolute value is the
/// variable index.
///
/// ```
/// use covalence_sat::Cnf;
///
/// let mut cnf = Cnf::new();
/// let x = cnf.fresh();
/// assert!(x.is_pos());
/// assert_eq!(x.dimacs(), 1);
/// assert_eq!((!x).dimacs(), -1);
/// assert_eq!((!x).to_string(), "~x1");
/// assert_eq!(!(!x), x);
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Lit(NonZeroI32);

impl Lit {
    /// The underlying variable.
    pub fn var(self) -> Var {
        // Safe: absolute value of a NonZeroI32 is a positive NonZeroI32
        Var(NonZeroI32::new(self.0.get().abs()).expect("literal is zero"))
    }

    /// Is this a positive literal?
    pub fn is_pos(self) -> bool {
        self.0.get() > 0
    }

    /// Is this a negative literal?
    pub fn is_neg(self) -> bool {
        self.0.get() < 0
    }

    /// The polarity: `true` for positive, `false` for negative.
    pub fn polarity(self) -> bool {
        self.0.get() > 0
    }

    /// The raw DIMACS integer representation.
    pub fn dimacs(self) -> i32 {
        self.0.get()
    }
}

impl std::ops::Not for Lit {
    type Output = Lit;

    fn not(self) -> Lit {
        // Safe: negating a NonZeroI32 is still nonzero
        Lit(self.0.checked_neg().expect("literal overflow"))
    }
}

impl fmt::Display for Lit {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_pos() {
            write!(f, "x{}", self.0)
        } else {
            write!(f, "~x{}", self.0.get().abs())
        }
    }
}

/// A clause — a disjunction of literals.
///
/// ```
/// use covalence_sat::{Cnf, Clause};
///
/// let mut cnf = Cnf::new();
/// let x = cnf.fresh();
/// let y = cnf.fresh();
/// let clause = Clause::new([x, !y]);
/// assert_eq!(clause.len(), 2);
/// assert!(!clause.is_empty());
/// assert!(!clause.is_unit());
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Clause(Vec<Lit>);

impl Clause {
    /// Create a clause from an iterator of literals.
    pub fn new(lits: impl IntoIterator<Item = Lit>) -> Self {
        Clause(lits.into_iter().collect())
    }

    /// The literals in this clause.
    pub fn lits(&self) -> &[Lit] {
        &self.0
    }

    /// Number of literals.
    pub fn len(&self) -> usize {
        self.0.len()
    }

    /// Is this the empty clause (always false)?
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    /// Is this a unit clause (exactly one literal)?
    pub fn is_unit(&self) -> bool {
        self.0.len() == 1
    }
}

impl fmt::Display for Clause {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("(")?;
        for (i, lit) in self.0.iter().enumerate() {
            if i > 0 {
                f.write_str(" | ")?;
            }
            write!(f, "{lit}")?;
        }
        f.write_str(")")
    }
}

/// A CNF formula — a conjunction of clauses with a variable counter.
///
/// ```
/// use covalence_sat::Cnf;
///
/// let mut cnf = Cnf::new();
/// let x = cnf.fresh();
/// let y = cnf.fresh();
/// cnf.clause([x, !y]);
/// cnf.clause([!x, y]);
/// assert_eq!(cnf.num_vars(), 2);
/// assert_eq!(cnf.num_clauses(), 2);
/// ```
#[derive(Debug, Clone)]
pub struct Cnf {
    num_vars: u32,
    clauses: Vec<Clause>,
}

impl Cnf {
    /// Create an empty CNF formula.
    pub fn new() -> Self {
        Cnf {
            num_vars: 0,
            clauses: Vec::new(),
        }
    }

    /// Allocate a fresh variable and return its positive literal.
    pub fn fresh(&mut self) -> Lit {
        self.num_vars += 1;
        let v = Var::new(NonZeroI32::new(self.num_vars as i32).expect("too many variables"));
        v.pos()
    }

    /// Add a clause to the formula.
    pub fn clause(&mut self, lits: impl IntoIterator<Item = Lit>) {
        self.clauses.push(Clause::new(lits));
    }

    /// Number of variables allocated so far.
    pub fn num_vars(&self) -> u32 {
        self.num_vars
    }

    /// Number of clauses.
    pub fn num_clauses(&self) -> usize {
        self.clauses.len()
    }

    /// Iterate over the clauses of this formula.
    pub fn clauses(&self) -> impl ExactSizeIterator<Item = &Clause> + '_ {
        self.clauses.iter()
    }
}

impl Default for Cnf {
    fn default() -> Self {
        Self::new()
    }
}

impl fmt::Display for Cnf {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (i, clause) in self.clauses().enumerate() {
            if i > 0 {
                f.write_str(" & ")?;
            }
            write!(f, "{clause}")?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn fresh_variables_are_sequential() {
        let mut cnf = Cnf::new();
        let x = cnf.fresh();
        let y = cnf.fresh();
        let z = cnf.fresh();
        assert_eq!(x.var().index(), 1);
        assert_eq!(y.var().index(), 2);
        assert_eq!(z.var().index(), 3);
        assert_eq!(cnf.num_vars(), 3);
    }

    #[test]
    fn literal_polarity() {
        let mut cnf = Cnf::new();
        let x = cnf.fresh();
        assert!(x.is_pos());
        assert!(!x.is_neg());

        let nx = !x;
        assert!(nx.is_neg());
        assert!(!nx.is_pos());
        assert_eq!(nx.var(), x.var());
    }

    #[test]
    fn double_negation() {
        let mut cnf = Cnf::new();
        let x = cnf.fresh();
        assert_eq!(!(!x), x);
    }

    #[test]
    fn dimacs_encoding() {
        let mut cnf = Cnf::new();
        let x = cnf.fresh(); // var 1
        let y = cnf.fresh(); // var 2
        assert_eq!(x.dimacs(), 1);
        assert_eq!((!x).dimacs(), -1);
        assert_eq!(y.dimacs(), 2);
        assert_eq!((!y).dimacs(), -2);
    }

    #[test]
    fn clause_properties() {
        let empty = Clause::new([]);
        assert!(empty.is_empty());
        assert!(!empty.is_unit());
        assert_eq!(empty.len(), 0);

        let mut cnf = Cnf::new();
        let x = cnf.fresh();
        let unit = Clause::new([x]);
        assert!(!unit.is_empty());
        assert!(unit.is_unit());
        assert_eq!(unit.len(), 1);
    }

    #[test]
    fn cnf_building() {
        let mut cnf = Cnf::new();
        assert_eq!(cnf.num_vars(), 0);
        assert_eq!(cnf.num_clauses(), 0);

        let x = cnf.fresh();
        let y = cnf.fresh();
        cnf.clause([x, !y]);
        cnf.clause([!x, y]);

        assert_eq!(cnf.num_vars(), 2);
        assert_eq!(cnf.num_clauses(), 2);
        assert_eq!(cnf.clauses().next().unwrap().len(), 2);
    }

    #[test]
    fn display_var() {
        let v = Var::new(NonZeroI32::new(42).unwrap());
        assert_eq!(v.to_string(), "x42");
    }

    #[test]
    fn display_lit() {
        let v = Var::new(NonZeroI32::new(3).unwrap());
        assert_eq!(v.pos().to_string(), "x3");
        assert_eq!(v.neg().to_string(), "~x3");
    }

    #[test]
    fn display_clause() {
        let mut cnf = Cnf::new();
        let x = cnf.fresh();
        let y = cnf.fresh();
        let clause = Clause::new([x, !y]);
        assert_eq!(clause.to_string(), "(x1 | ~x2)");

        let empty = Clause::new([]);
        assert_eq!(empty.to_string(), "()");
    }

    #[test]
    fn display_cnf() {
        let mut cnf = Cnf::new();
        let x = cnf.fresh();
        let y = cnf.fresh();
        cnf.clause([x, !y]);
        cnf.clause([!x, y]);
        assert_eq!(cnf.to_string(), "(x1 | ~x2) & (~x1 | x2)");
    }

    #[test]
    fn empty_cnf_display() {
        let cnf = Cnf::new();
        assert_eq!(cnf.to_string(), "");
    }
}
