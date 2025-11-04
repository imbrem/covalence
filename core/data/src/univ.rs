use std::fmt::{self, Debug};

/// A universe level
#[derive(Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct ULvl {
    pub(crate) level: i32,
}

impl ULvl {
    /// The universe of propositions
    pub const PROP: Self = ULvl { level: 0 };
    // The universe of sets
    pub const SET: Self = ULvl { level: 1 };

    /// Construct a constant universe level
    pub fn of_nat(level: u32) -> ULvl {
        assert!(level <= i32::MAX as u32, "universe level out of bounds");
        ULvl {
            level: level as i32,
        }
    }

    /// Get this universe level as a constant
    pub fn as_const(self) -> Option<u32> {
        if self.level >= 0 {
            Some(self.level as u32)
        } else {
            None
        }
    }
}

impl Debug for ULvl {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.level >= 0 {
            write!(f, "#u{}", self.level)
        } else {
            write!(f, "#uv{}", -self.level)
        }
    }
}

/// A datastore that can read universe levels
pub trait ReadUniv {
    /// Check whether one universe is less than or equal to another
    fn u_le(&self, lo: ULvl, hi: ULvl) -> bool;

    /// Check whether one universe is strictly less than another
    fn u_lt(&self, lo: ULvl, hi: ULvl) -> bool;

    /// Check whether the impredicative maximum of two universes is less than or equal to another
    fn imax_le(&self, lo_lhs: ULvl, lo_rhs: ULvl, hi: ULvl) -> bool;
}

///  A trait implemented by a datastore that can create hash-consed universe levels
pub trait WriteUniv {
    /// Get the successor of a given universe level
    fn succ(&mut self, level: ULvl) -> ULvl;

    /// Get the maximum of two universe levels
    fn umax(&mut self, lhs: ULvl, rhs: ULvl) -> ULvl;

    /// Get the impredicatibe maximum of two universe levels
    fn imax(&mut self, lhs: ULvl, rhs: ULvl) -> ULvl;
}
