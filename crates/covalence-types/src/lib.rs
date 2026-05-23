pub use bytes;

use std::fmt;
use std::str::FromStr;

/// Error returned when parsing an invalid [`Decision`] string.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[error("invalid decision: {0:?}")]
pub struct ParseDecisionError(String);

/// Three-valued decision result, shared across the kernel, SAT, and SMT layers.
///
/// Combinators (`and`, `or`, `not`, `implies`) follow Kleene's strong
/// three-valued logic. Integer encoding: `1 = Sat`, `0 = Unknown`, `-1 = Unsat`.
///
/// ```
/// use covalence_types::Decision::{self, *};
///
/// // Kleene AND: Unsat dominates
/// assert_eq!(Sat.and(Unknown), Unknown);
/// assert_eq!(Sat.and(Unsat), Unsat);
///
/// // Kleene OR: Sat dominates
/// assert_eq!(Unsat.or(Unknown), Unknown);
/// assert_eq!(Unsat.or(Sat), Sat);
///
/// // Integer encoding
/// assert_eq!(i8::from(Sat), 1);
/// assert_eq!(i8::from(Unsat), -1);
/// assert_eq!(Decision::try_from(0i8), Ok(Unknown));
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Decision {
    /// Satisfiable / proved — the proposition called `attest()`, or the formula has a model.
    Sat,
    /// Undecided — neither proved nor refuted (e.g. solver timeout, resource limit).
    Unknown,
    /// Unsatisfiable / refuted — the proposition was refuted, or the formula has no model.
    Unsat,
}

// ---------------------------------------------------------------------------
// Display / FromStr
// ---------------------------------------------------------------------------

impl fmt::Display for Decision {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

/// Parses `"sat"`, `"unknown"`, or `"unsat"`. Does **not** accept `"true"`/`"false"` —
/// `covalence-kernel` still uses those strings internally but will migrate later.
impl FromStr for Decision {
    type Err = ParseDecisionError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "sat" => Ok(Decision::Sat),
            "unknown" => Ok(Decision::Unknown),
            "unsat" => Ok(Decision::Unsat),
            _ => Err(ParseDecisionError(s.to_owned())),
        }
    }
}

// ---------------------------------------------------------------------------
// Integer conversions: 1 = Sat, 0 = Unknown, -1 = Unsat
// ---------------------------------------------------------------------------

impl From<Decision> for i8 {
    fn from(d: Decision) -> i8 {
        match d {
            Decision::Sat => 1,
            Decision::Unknown => 0,
            Decision::Unsat => -1,
        }
    }
}

impl From<Decision> for i32 {
    fn from(d: Decision) -> i32 {
        i8::from(d) as i32
    }
}

impl TryFrom<i8> for Decision {
    type Error = ();

    fn try_from(v: i8) -> Result<Self, ()> {
        match v {
            1 => Ok(Decision::Sat),
            0 => Ok(Decision::Unknown),
            -1 => Ok(Decision::Unsat),
            _ => Err(()),
        }
    }
}

impl TryFrom<i32> for Decision {
    type Error = ();

    fn try_from(v: i32) -> Result<Self, ()> {
        match v {
            1 => Ok(Decision::Sat),
            0 => Ok(Decision::Unknown),
            -1 => Ok(Decision::Unsat),
            _ => Err(()),
        }
    }
}

// ---------------------------------------------------------------------------
// Boolean conversions
// ---------------------------------------------------------------------------

impl From<bool> for Decision {
    /// `true → Sat`, `false → Unsat`.
    fn from(b: bool) -> Self {
        if b { Decision::Sat } else { Decision::Unsat }
    }
}

// ---------------------------------------------------------------------------
// Predicates and combinators
// ---------------------------------------------------------------------------

impl Decision {
    /// String representation: `"sat"`, `"unknown"`, or `"unsat"`.
    pub const fn as_str(self) -> &'static str {
        match self {
            Decision::Sat => "sat",
            Decision::Unknown => "unknown",
            Decision::Unsat => "unsat",
        }
    }

    /// Is this `Sat`?
    pub const fn is_sat(self) -> bool {
        matches!(self, Decision::Sat)
    }

    /// Is this `Unsat`?
    pub const fn is_unsat(self) -> bool {
        matches!(self, Decision::Unsat)
    }

    /// Is this `Unknown`?
    pub const fn is_unknown(self) -> bool {
        matches!(self, Decision::Unknown)
    }

    /// Is this known (either `Sat` or `Unsat`)?
    pub const fn is_known(self) -> bool {
        !self.is_unknown()
    }

    /// Could be true? (`Sat` or `Unknown`).
    pub const fn maybe_sat(self) -> bool {
        !self.is_unsat()
    }

    /// Could be false? (`Unsat` or `Unknown`).
    pub const fn maybe_unsat(self) -> bool {
        !self.is_sat()
    }

    /// Negation: `Sat ↔ Unsat`, `Unknown` stays `Unknown`.
    pub const fn not(self) -> Decision {
        match self {
            Decision::Sat => Decision::Unsat,
            Decision::Unknown => Decision::Unknown,
            Decision::Unsat => Decision::Sat,
        }
    }

    /// Kleene AND — `Unsat` dominates.
    pub const fn and(self, other: Decision) -> Decision {
        match (self, other) {
            (Decision::Unsat, _) | (_, Decision::Unsat) => Decision::Unsat,
            (Decision::Unknown, _) | (_, Decision::Unknown) => Decision::Unknown,
            (Decision::Sat, Decision::Sat) => Decision::Sat,
        }
    }

    /// Kleene OR — `Sat` dominates.
    pub const fn or(self, other: Decision) -> Decision {
        match (self, other) {
            (Decision::Sat, _) | (_, Decision::Sat) => Decision::Sat,
            (Decision::Unknown, _) | (_, Decision::Unknown) => Decision::Unknown,
            (Decision::Unsat, Decision::Unsat) => Decision::Unsat,
        }
    }

    /// Material implication: `self → other` ≡ `¬self ∨ other`.
    pub const fn implies(self, other: Decision) -> Decision {
        self.not().or(other)
    }
}

// ---------------------------------------------------------------------------
// Operator overloads
// ---------------------------------------------------------------------------

impl std::ops::Not for Decision {
    type Output = Decision;

    fn not(self) -> Decision {
        Decision::not(self)
    }
}

impl std::ops::BitAnd for Decision {
    type Output = Decision;

    fn bitand(self, rhs: Decision) -> Decision {
        self.and(rhs)
    }
}

impl std::ops::BitOr for Decision {
    type Output = Decision;

    fn bitor(self, rhs: Decision) -> Decision {
        self.or(rhs)
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use Decision::*;

    #[test]
    fn display() {
        assert_eq!(Sat.to_string(), "sat");
        assert_eq!(Unknown.to_string(), "unknown");
        assert_eq!(Unsat.to_string(), "unsat");
    }

    #[test]
    fn parse() {
        assert_eq!("sat".parse::<Decision>(), Ok(Sat));
        assert_eq!("unknown".parse::<Decision>(), Ok(Unknown));
        assert_eq!("unsat".parse::<Decision>(), Ok(Unsat));
        assert!("true".parse::<Decision>().is_err());
        assert!("false".parse::<Decision>().is_err());
        assert!("garbage".parse::<Decision>().is_err());
    }

    #[test]
    fn int_roundtrip() {
        for d in [Sat, Unknown, Unsat] {
            assert_eq!(Decision::try_from(i8::from(d)), Ok(d));
            assert_eq!(Decision::try_from(i32::from(d)), Ok(d));
        }
    }

    #[test]
    fn int_values() {
        assert_eq!(i8::from(Sat), 1);
        assert_eq!(i8::from(Unknown), 0);
        assert_eq!(i8::from(Unsat), -1);
    }

    #[test]
    fn int_reject_invalid() {
        assert_eq!(Decision::try_from(2i8), Err(()));
        assert_eq!(Decision::try_from(-2i8), Err(()));
        assert_eq!(Decision::try_from(42i32), Err(()));
    }

    #[test]
    fn from_bool() {
        assert_eq!(Decision::from(true), Sat);
        assert_eq!(Decision::from(false), Unsat);
    }

    #[test]
    fn predicates() {
        assert!(Sat.is_sat());
        assert!(Sat.is_known());
        assert!(!Sat.is_unsat());
        assert!(!Sat.is_unknown());

        assert!(Unsat.is_unsat());
        assert!(Unsat.is_known());
        assert!(!Unsat.is_sat());
        assert!(!Unsat.is_unknown());

        assert!(Unknown.is_unknown());
        assert!(!Unknown.is_known());
        assert!(!Unknown.is_sat());
        assert!(!Unknown.is_unsat());

        // maybe_sat / maybe_unsat
        assert!(Sat.maybe_sat());
        assert!(!Sat.maybe_unsat());
        assert!(Unknown.maybe_sat());
        assert!(Unknown.maybe_unsat());
        assert!(!Unsat.maybe_sat());
        assert!(Unsat.maybe_unsat());
    }

    #[test]
    fn not_involution() {
        for d in [Sat, Unknown, Unsat] {
            assert_eq!(d.not().not(), d);
        }
    }

    #[test]
    fn and_commutativity() {
        let vals = [Sat, Unknown, Unsat];
        for &a in &vals {
            for &b in &vals {
                assert_eq!(a.and(b), b.and(a));
            }
        }
    }

    #[test]
    fn or_commutativity() {
        let vals = [Sat, Unknown, Unsat];
        for &a in &vals {
            for &b in &vals {
                assert_eq!(a.or(b), b.or(a));
            }
        }
    }

    #[test]
    fn and_identity_and_annihilator() {
        for d in [Sat, Unknown, Unsat] {
            assert_eq!(d.and(Sat), d); // Sat is identity
            assert_eq!(d.and(Unsat), Unsat); // Unsat annihilates
        }
    }

    #[test]
    fn or_identity_and_annihilator() {
        for d in [Sat, Unknown, Unsat] {
            assert_eq!(d.or(Unsat), d); // Unsat is identity
            assert_eq!(d.or(Sat), Sat); // Sat annihilates
        }
    }

    #[test]
    fn de_morgan() {
        let vals = [Sat, Unknown, Unsat];
        for &a in &vals {
            for &b in &vals {
                assert_eq!(a.and(b).not(), a.not().or(b.not()));
                assert_eq!(a.or(b).not(), a.not().and(b.not()));
            }
        }
    }

    #[test]
    fn implies_truth_table() {
        assert_eq!(Sat.implies(Sat), Sat);
        assert_eq!(Sat.implies(Unknown), Unknown);
        assert_eq!(Sat.implies(Unsat), Unsat);
        assert_eq!(Unsat.implies(Sat), Sat);
        assert_eq!(Unsat.implies(Unknown), Sat);
        assert_eq!(Unsat.implies(Unsat), Sat);
    }

    #[test]
    fn operator_overloads() {
        assert_eq!(!Sat, Unsat);
        assert_eq!(Sat & Unsat, Unsat);
        assert_eq!(Unsat | Sat, Sat);
        assert_eq!(!Unknown, Unknown);
    }

    #[test]
    fn associativity() {
        let vals = [Sat, Unknown, Unsat];
        for &a in &vals {
            for &b in &vals {
                for &c in &vals {
                    assert_eq!(a.and(b.and(c)), a.and(b).and(c));
                    assert_eq!(a.or(b.or(c)), a.or(b).or(c));
                }
            }
        }
    }

    #[test]
    fn distributivity() {
        let vals = [Sat, Unknown, Unsat];
        for &a in &vals {
            for &b in &vals {
                for &c in &vals {
                    assert_eq!(a.and(b.or(c)), a.and(b).or(a.and(c)));
                    assert_eq!(a.or(b.and(c)), a.or(b).and(a.or(c)));
                }
            }
        }
    }
}
