mod implies_sealed {
    pub trait ImpliesSealed<F> {}

    pub trait FromIffSealed<F> {}
}

pub(crate) use implies_sealed::{FromIffSealed, ImpliesSealed};

pub trait Implies<F>: ImpliesSealed<F> {
    fn implies(self) -> F;
}

pub trait FromIff<F>: FromIffSealed<F> {
    fn from_iff(fact: F) -> Self;
}