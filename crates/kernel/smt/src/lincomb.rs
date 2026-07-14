//! Linear combinations of *atoms* over [`Rational`] coefficients — the pure
//! data the Farkas checker manipulates. An atom is anything the arithmetic
//! frontend treats as an opaque variable (a free `int` variable, an
//! uninterpreted term like `f a`, or a non-linear product). Atoms are keyed by
//! a caller-chosen `A: Ord + Clone` (a term, an interned index, a string in
//! tests) so this module is completely backend-independent.

use std::collections::BTreeMap;

use crate::rational::Rational;

/// A linear combination `Σ cᵢ·aᵢ` (no constant term — the constant is tracked
/// separately by the normalised-literal layer). Kept with zero coefficients
/// pruned, so [`LinComb::is_empty`] means "identically zero".
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LinComb<A: Ord + Clone> {
    terms: BTreeMap<A, Rational>,
}

impl<A: Ord + Clone> Default for LinComb<A> {
    fn default() -> Self {
        LinComb {
            terms: BTreeMap::new(),
        }
    }
}

impl<A: Ord + Clone> LinComb<A> {
    pub fn new() -> Self {
        Self::default()
    }

    /// The single-atom combination `1·a`.
    pub fn atom(a: A) -> Self {
        let mut lc = Self::new();
        let _ = lc.add_term(a, Rational::ONE); // fresh map: cannot overflow
        lc
    }

    /// Add `c·a`, pruning to zero. Returns `false` on coefficient overflow.
    #[must_use]
    pub fn add_term(&mut self, a: A, c: Rational) -> bool {
        if c.is_zero() {
            return true;
        }
        match self.terms.get(&a) {
            Some(existing) => match existing.add(&c) {
                Some(sum) if sum.is_zero() => {
                    self.terms.remove(&a);
                    true
                }
                Some(sum) => {
                    self.terms.insert(a, sum);
                    true
                }
                None => false,
            },
            None => {
                self.terms.insert(a, c);
                true
            }
        }
    }

    /// `self += other`. Returns `false` on overflow.
    #[must_use]
    pub fn add_assign(&mut self, other: &LinComb<A>) -> bool {
        other
            .terms
            .iter()
            .all(|(a, c)| self.add_term(a.clone(), *c))
    }

    /// `self *= k` (scale every coefficient). Returns `false` on overflow.
    #[must_use]
    pub fn scale(&mut self, k: Rational) -> bool {
        if k.is_zero() {
            self.terms.clear();
            return true;
        }
        for c in self.terms.values_mut() {
            match c.mul(&k) {
                Some(p) => *c = p,
                None => return false,
            }
        }
        true
    }

    /// Identically zero (all coefficients cancelled)?
    pub fn is_empty(&self) -> bool {
        self.terms.is_empty()
    }

    /// The greatest common divisor of every (integer) coefficient's numerator,
    /// or `None` if any coefficient is non-integral. Used by the GCD
    /// strengthening variant. `0` (empty combination) yields `None`.
    pub fn integer_coeff_gcd(&self) -> Option<i128> {
        let mut g = 0i128;
        for c in self.terms.values() {
            if !c.is_integer() {
                return None;
            }
            let n = c.num().unsigned_abs() as i128;
            g = gcd(g, n);
        }
        (g != 0).then_some(g)
    }

    pub fn iter(&self) -> impl Iterator<Item = (&A, &Rational)> {
        self.terms.iter()
    }
}

fn gcd(a: i128, b: i128) -> i128 {
    let (mut a, mut b) = (a.unsigned_abs(), b.unsigned_abs());
    while b != 0 {
        (a, b) = (b, a % b);
    }
    a as i128
}
