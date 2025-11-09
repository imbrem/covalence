mod implies_sealed {
    pub trait ImpliesSealed<F> {}

    pub trait FromIffSealed<F> {}

    pub trait TryFromIffSealed<F> {}
}

pub(crate) use implies_sealed::{FromIffSealed, ImpliesSealed, TryFromIffSealed};

pub trait Implies<F>: ImpliesSealed<F> {
    fn implies(self) -> F;
}

pub trait FromIff<F>: FromIffSealed<F> {
    fn from_iff(fact: F) -> Self;
}

pub trait TryFromIff<F>: TryFromIffSealed<F> {
    fn try_from_iff(fact: F) -> Result<Self, F>
    where
        Self: Sized;
}
