use std::{
    fmt::{self, Debug},
    ops::{Add, Sub},
};

/// A bound variable, represented by a de-Bruijn index
#[derive(Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd, Default)]
pub struct Bv(pub u32);

impl Bv {
    /// An invalid bound variable
    ///
    /// Compares greater-than all other bound variables
    pub const INVALID: Bv = Bv(u32::MAX);

    /// Construct a bound variable from a `u32`
    pub const fn new(ix: u32) -> Bv {
        assert!(
            ix != u32::MAX,
            "cannot use new to construct an invalid de-Bruijn index"
        );
        Bv(ix)
    }

    /// Get the successor of this bound variable
    ///
    /// Panics if this would overflow
    ///
    /// # Examples
    /// ```rust
    /// # use covalence::kernel::data::term::Bv;
    /// for x in 0..100 {
    ///     assert_eq!(Bv(x).succ(), Bv(x + 1));
    /// }
    /// assert_eq!(Bv::INVALID.succ(), Bv::INVALID);
    /// ```
    pub fn succ(self) -> Bv {
        if self.0 == u32::MAX - 1 {
            panic!("de-Bruijn index overflow");
        }
        Bv(self.0.saturating_add(1))
    }

    /// Get the predecessor of this bound variable
    ///
    /// The predecessor of `#0` is `#0`.
    ///
    /// Panics if:
    /// - The bound variable is invalid
    ///     ```rust,should_panic
    ///     # use covalence::kernel::data::term::Bv;
    ///     Bv::INVALID.pred();
    ///     ``````
    /// # Examples
    /// ```rust
    /// # use covalence::kernel::data::term::Bv;
    /// assert_eq!(Bv(0).pred(), Bv(0));
    /// for x in 0..100 {
    ///     assert_eq!(Bv(x).succ().pred(), Bv(x));
    /// }
    /// ```
    pub fn pred(self) -> Bv {
        if !self.is_valid() {
            panic!("attempted to take predecessor of invalid de-Bruijn index")
        }
        Bv(self.0.saturating_sub(1))
    }

    /// Get whether this bound variable is valid
    ///
    /// # Examples
    /// ```rust
    /// # use covalence::kernel::data::term::Bv;
    /// for x in 0..100 {
    ///    assert!(Bv(x).is_valid());
    /// }
    /// assert!(!Bv::INVALID.is_valid());
    /// ```
    pub fn is_valid(self) -> bool {
        self.0 != u32::MAX
    }

    /// Get the `bvi` of this bound variable after inserting a bound variable under `k` binders
    pub fn bvi_under(self, k: Bv) -> Bv {
        if self < k { self } else { self.succ() }
    }

    /// Get the `bvi` of this bound variable after inserting `n` bound variables under `k` binders
    pub fn bvi_add_under(self, shift: Bv, under: Bv) -> Bv {
        if self < under { self } else { self + shift }
    }
}

impl Add for Bv {
    type Output = Bv;

    fn add(self, rhs: Bv) -> Bv {
        let add = self.0.saturating_add(rhs.0);
        if add != u32::MAX {
            Bv(add)
        } else if self.is_valid() && rhs.is_valid() {
            panic!("bound variable overflow");
        } else {
            Bv::INVALID
        }
    }
}

impl Sub for Bv {
    type Output = Bv;

    fn sub(self, rhs: Bv) -> Bv {
        Bv(self.0.saturating_sub(rhs.0))
    }
}

impl Debug for Bv {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if *self == Bv::INVALID {
            return write!(f, "#invalid");
        }
        write!(f, "#{}", self.0)
    }
}

/// A substitution which shifts up `shift` binders under `under` binders
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd, Default)]
pub struct Shift {
    /// The level at which to shift
    pub under: Bv,
    /// The number of binders to shift by
    shift: Bv,
}

impl Shift {
    /// Construct a new shift from a level and shift
    ///
    /// Panics if either is invalid
    pub fn new(level: Bv, shift: Bv) -> Shift {
        debug_assert!(
            level.is_valid(),
            "cannot construct a shift at an invalid level"
        );
        debug_assert!(
            shift.is_valid(),
            "cannot construct a shift by an invalid amount"
        );
        Shift {
            under: if shift == Bv(0) { Bv(0) } else { level },
            shift,
        }
    }

    /// Construct a new shift from the number of binders to shift by
    ///
    /// Panics if the shift is invalid
    pub fn from_shift(shift: Bv) -> Shift {
        Self::new(Bv(0), shift)
    }

    /// Shift upwards by one at the given level
    ///
    /// Panics if the level is invalid
    pub fn up(level: Bv) -> Shift {
        Self::new(level, Bv(1))
    }

    /// Lift this shift under a binder
    pub fn lift(self) -> Shift {
        if self.shift == Bv(0) {
            debug_assert_eq!(self.under, Bv(0), "the identity shift must have zero level");
            return self;
        }
        Shift {
            under: self.under.succ(),
            shift: self.shift,
        }
    }

    /// Lift this shift under `n` binders
    pub fn lift_under(self, n: Bv) -> Shift {
        if self.shift == Bv(0) {
            debug_assert_eq!(self.under, Bv(0), "the identity shift must have zero level");
            return self;
        }
        Shift {
            under: self.under + n,
            shift: self.shift,
        }
    }

    /// Get the successor of this shift
    pub fn succ(self) -> Shift {
        Shift {
            under: self.under,
            shift: self.shift.succ(),
        }
    }

    /// Apply this shift
    pub fn apply(self, bv: Bv) -> Bv {
        if bv < self.under { bv } else { bv + self.shift }
    }

    /// Get an upper bound on the bound variable index after applying this shift
    ///
    /// # Examples
    /// ```rust
    /// # use covalence::kernel::data::term::*;
    /// # for level in (0..10).map(Bv) { for shift in (0..10).map(Bv) {
    /// let shift = Shift::new(level, shift);
    /// assert_eq!(shift.bvi(Bv(0)), Bv(0));
    /// # for bv in (0..10).map(Bv) {
    /// assert_eq!(shift.bvi(bv.succ()), shift.apply(bv).succ());
    /// # } } }
    /// ```
    pub fn bvi(self, bvi: Bv) -> Bv {
        if bvi <= self.under {
            bvi
        } else {
            bvi + self.shift
        }
    }

    /// Get this shift's level
    pub fn under(self) -> Bv {
        self.under
    }

    /// Get this shift's shift
    pub fn shift(self) -> Bv {
        self.shift
    }

    /// Check whether this shift is the identity
    pub fn is_id(self) -> bool {
        if self.shift == Bv(0) {
            debug_assert_eq!(self.under, Bv(0), "the identity shift must have zero level");
            true
        } else {
            false
        }
    }
}
