use crate::data::term::ULvl;

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
