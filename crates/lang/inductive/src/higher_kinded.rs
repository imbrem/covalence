//! Host-language higher-kinded operations.
//!
//! Rust cannot quantify directly over a type constructor `F<_>`.  [`TypeCtor`]
//! therefore uses a zero-sized witness with a generic associated type.  For
//! example, [`OptionK`] witnesses `Option<_>`, while [`ResultK`] fixes the
//! error parameter and witnesses `Result<_, E>`.
//!
//! This is the computational, host-language companion to
//! [`StructuralFunctorAction`](crate::StructuralFunctorAction).  The latter
//! maps abstract backend arrows (including HOL terms); this module maps Rust
//! functions over Rust values.  Keeping the two surfaces separate avoids
//! pretending that a host closure is a logic-level arrow.
//!
//! Operation traits make no law claim.  The corresponding `*Laws` marker
//! traits are opt-in assertions whose equations are exercised by reusable
//! conformance helpers.  They are not theorem authority.

use std::marker::PhantomData;

/// A witness for a unary type constructor.
pub trait TypeCtor {
    /// Application of this constructor to an element type.
    type Of<T>;
}

/// Computational `map`.
pub trait Functor: TypeCtor {
    /// Apply a function to every element, preserving the outer structure.
    fn map<A, B>(value: Self::Of<A>, f: impl FnMut(A) -> B) -> Self::Of<B>;
}

/// Computational application inside a context.
pub trait Apply: Functor {
    /// Apply contextual functions to contextual arguments.
    fn ap<A: Clone, B, F: FnMut(A) -> B>(
        functions: Self::Of<F>,
        arguments: Self::Of<A>,
    ) -> Self::Of<B>;
}

/// Computational injection into a context.
pub trait Applicative: Apply {
    /// Embed a pure value.
    fn pure<A>(value: A) -> Self::Of<A>;
}

/// Computational monadic sequencing without a law claim.
pub trait Bind: TypeCtor {
    /// Sequence a computation selected by each contained value.
    fn flat_map<A, B>(value: Self::Of<A>, f: impl FnMut(A) -> Self::Of<B>) -> Self::Of<B>;
}

/// An operational convenience bound.
pub trait Monad: Applicative + Bind {}

impl<T: Applicative + Bind> Monad for T {}

/// Left folds, separated from traversal because folds need no effect algebra.
pub trait Foldable: TypeCtor {
    /// Fold elements from left to right.
    fn fold_left<A, B>(value: Self::Of<A>, initial: B, f: impl FnMut(B, A) -> B) -> B;
}

/// Minimal applicative interface needed by [`Traversable`].
///
/// `map2` avoids placing a global `Clone` bound on contextual arguments. This
/// matters for traversing into proof objects and linear host values. An
/// applicative with Cartesian/list application may expose traversal through a
/// different, explicitly cloning adapter.
pub trait TraverseEffect: Functor {
    /// Embed a pure value in the effect.
    fn effect_pure<A>(value: A) -> Self::Of<A>;

    /// Combine two independent effects.
    fn map2<A, B, C>(
        left: Self::Of<A>,
        right: Self::Of<B>,
        f: impl FnMut(A, B) -> C,
    ) -> Self::Of<C>;
}

/// Effectful traversal preserving the outer shape.
pub trait Traversable: Functor + Foldable {
    /// Map each element to an effect and collect those effects in order.
    fn traverse<E: TraverseEffect, A, B>(
        value: Self::Of<A>,
        f: impl FnMut(A) -> E::Of<B>,
    ) -> E::Of<Self::Of<B>>;
}

/// Opt-in assertion that [`Functor`] obeys identity and composition.
pub trait FunctorLaws: Functor {}

/// Opt-in assertion that [`Applicative`] obeys identity, homomorphism,
/// interchange, and composition.
pub trait ApplicativeLaws: Applicative + FunctorLaws {}

/// Opt-in assertion that [`Monad`] obeys left/right identity and associativity.
pub trait MonadLaws: Monad + ApplicativeLaws {}

/// `Option<_>` constructor witness.
#[derive(Clone, Copy, Debug, Default)]
pub struct OptionK;

impl TypeCtor for OptionK {
    type Of<T> = Option<T>;
}

impl Functor for OptionK {
    fn map<A, B>(value: Option<A>, f: impl FnMut(A) -> B) -> Option<B> {
        value.map(f)
    }
}

impl Apply for OptionK {
    fn ap<A: Clone, B, F: FnMut(A) -> B>(functions: Option<F>, arguments: Option<A>) -> Option<B> {
        functions
            .zip(arguments)
            .map(|(mut f, argument)| f(argument))
    }
}

impl Applicative for OptionK {
    fn pure<A>(value: A) -> Option<A> {
        Some(value)
    }
}

impl Bind for OptionK {
    fn flat_map<A, B>(value: Option<A>, f: impl FnMut(A) -> Option<B>) -> Option<B> {
        value.and_then(f)
    }
}

impl Foldable for OptionK {
    fn fold_left<A, B>(value: Option<A>, initial: B, mut f: impl FnMut(B, A) -> B) -> B {
        match value {
            Some(value) => f(initial, value),
            None => initial,
        }
    }
}

impl TraverseEffect for OptionK {
    fn effect_pure<A>(value: A) -> Option<A> {
        Some(value)
    }

    fn map2<A, B, C>(left: Option<A>, right: Option<B>, mut f: impl FnMut(A, B) -> C) -> Option<C> {
        left.zip(right).map(|(left, right)| f(left, right))
    }
}

impl Traversable for OptionK {
    fn traverse<E: TraverseEffect, A, B>(
        value: Option<A>,
        mut f: impl FnMut(A) -> E::Of<B>,
    ) -> E::Of<Option<B>> {
        match value {
            None => E::effect_pure(None),
            Some(value) => E::map(f(value), Some),
        }
    }
}

impl FunctorLaws for OptionK {}
impl ApplicativeLaws for OptionK {}
impl MonadLaws for OptionK {}

/// `Vec<_>` constructor witness, with list applicative application.
#[derive(Clone, Copy, Debug, Default)]
pub struct VecK;

impl TypeCtor for VecK {
    type Of<T> = Vec<T>;
}

impl Functor for VecK {
    fn map<A, B>(value: Vec<A>, f: impl FnMut(A) -> B) -> Vec<B> {
        value.into_iter().map(f).collect()
    }
}

impl Apply for VecK {
    fn ap<A: Clone, B, F: FnMut(A) -> B>(functions: Vec<F>, arguments: Vec<A>) -> Vec<B> {
        functions
            .into_iter()
            .flat_map(|mut function| {
                arguments
                    .iter()
                    .cloned()
                    .map(&mut function)
                    .collect::<Vec<_>>()
            })
            .collect()
    }
}

impl Applicative for VecK {
    fn pure<A>(value: A) -> Vec<A> {
        vec![value]
    }
}

impl Bind for VecK {
    fn flat_map<A, B>(value: Vec<A>, f: impl FnMut(A) -> Vec<B>) -> Vec<B> {
        value.into_iter().flat_map(f).collect()
    }
}

impl Foldable for VecK {
    fn fold_left<A, B>(value: Vec<A>, initial: B, f: impl FnMut(B, A) -> B) -> B {
        value.into_iter().fold(initial, f)
    }
}

impl Traversable for VecK {
    fn traverse<E: TraverseEffect, A, B>(
        value: Vec<A>,
        mut f: impl FnMut(A) -> E::Of<B>,
    ) -> E::Of<Vec<B>> {
        value
            .into_iter()
            .fold(E::effect_pure(Vec::new()), |collected, value| {
                E::map2(collected, f(value), |mut collected, value| {
                    collected.push(value);
                    collected
                })
            })
    }
}

impl FunctorLaws for VecK {}
impl ApplicativeLaws for VecK {}
impl MonadLaws for VecK {}

/// `Result<_, E>` constructor witness.
#[derive(Clone, Copy, Debug, Default)]
pub struct ResultK<E>(PhantomData<fn() -> E>);

impl<E> TypeCtor for ResultK<E> {
    type Of<T> = Result<T, E>;
}

impl<E> Functor for ResultK<E> {
    fn map<A, B>(value: Result<A, E>, f: impl FnMut(A) -> B) -> Result<B, E> {
        value.map(f)
    }
}

impl<E> Apply for ResultK<E> {
    fn ap<A: Clone, B, F: FnMut(A) -> B>(
        functions: Result<F, E>,
        arguments: Result<A, E>,
    ) -> Result<B, E> {
        functions.and_then(|mut function| arguments.map(&mut function))
    }
}

impl<E> Applicative for ResultK<E> {
    fn pure<A>(value: A) -> Result<A, E> {
        Ok(value)
    }
}

impl<E> Bind for ResultK<E> {
    fn flat_map<A, B>(value: Result<A, E>, f: impl FnMut(A) -> Result<B, E>) -> Result<B, E> {
        value.and_then(f)
    }
}

impl<E> Foldable for ResultK<E> {
    fn fold_left<A, B>(value: Result<A, E>, initial: B, mut f: impl FnMut(B, A) -> B) -> B {
        match value {
            Ok(value) => f(initial, value),
            Err(_) => initial,
        }
    }
}

impl<E> TraverseEffect for ResultK<E> {
    fn effect_pure<A>(value: A) -> Result<A, E> {
        Ok(value)
    }

    fn map2<A, B, C>(
        left: Result<A, E>,
        right: Result<B, E>,
        mut f: impl FnMut(A, B) -> C,
    ) -> Result<C, E> {
        left.and_then(|left| right.map(|right| f(left, right)))
    }
}

impl<E> Traversable for ResultK<E> {
    fn traverse<F: TraverseEffect, A, B>(
        value: Result<A, E>,
        mut f: impl FnMut(A) -> F::Of<B>,
    ) -> F::Of<Result<B, E>> {
        match value {
            Ok(value) => F::map(f(value), Ok),
            Err(error) => F::effect_pure(Err(error)),
        }
    }
}

impl<E> FunctorLaws for ResultK<E> {}
impl<E> ApplicativeLaws for ResultK<E> {}
impl<E> MonadLaws for ResultK<E> {}

#[cfg(test)]
mod tests {
    use super::*;

    fn functor_laws<F>()
    where
        F: FunctorLaws + TestSample,
        F::Of<i32>: Clone + PartialEq + std::fmt::Debug,
    {
        let sample = F::pure_for_test();
        assert_eq!(F::map(sample.clone(), |x| x), sample);
        assert_eq!(
            F::map(F::map(sample.clone(), |x| x + 2), |x| x * 3),
            F::map(sample, |x| (x + 2) * 3)
        );
    }

    trait TestSample: Functor {
        fn pure_for_test() -> Self::Of<i32>;
    }

    impl TestSample for OptionK {
        fn pure_for_test() -> Option<i32> {
            Some(4)
        }
    }
    impl TestSample for VecK {
        fn pure_for_test() -> Vec<i32> {
            vec![1, 2, 3]
        }
    }
    impl TestSample for ResultK<&'static str> {
        fn pure_for_test() -> Result<i32, &'static str> {
            Ok(4)
        }
    }

    #[test]
    fn reference_functors_obey_identity_and_composition() {
        functor_laws::<OptionK>();
        functor_laws::<VecK>();
        functor_laws::<ResultK<&'static str>>();
    }

    #[test]
    fn option_applicative_and_monad_laws() {
        assert_eq!(OptionK::ap(Some(|x| x + 1), Some(2)), Some(3));
        assert_eq!(
            OptionK::flat_map(OptionK::pure(3), |x| Some(x + 4)),
            Some(7)
        );
        let value = Some(3);
        assert_eq!(OptionK::flat_map(value, OptionK::pure), value);
        let f = |x| Some(x + 1);
        let g = |x| Some(x * 2);
        assert_eq!(
            OptionK::flat_map(OptionK::flat_map(value, f), g),
            OptionK::flat_map(value, |x| OptionK::flat_map(f(x), g))
        );
    }

    #[test]
    fn list_application_is_cartesian_and_fold_is_ordered() {
        let functions: Vec<fn(i32) -> i32> = vec![|x| x + 1, |x| x * 10];
        assert_eq!(VecK::ap(functions, vec![1, 2]), vec![2, 3, 10, 20]);
        assert_eq!(
            VecK::fold_left(vec!["a", "b", "c"], String::new(), |mut acc, x| {
                acc.push_str(x);
                acc
            }),
            "abc"
        );
    }

    #[test]
    fn result_short_circuits_the_fixed_error_parameter() {
        type R = ResultK<&'static str>;
        assert_eq!(R::flat_map(Ok(2), |x| Ok(x + 1)), Ok(3));
        assert_eq!(R::flat_map(Err::<i32, _>("bad"), |x| Ok(x + 1)), Err("bad"));
    }

    #[test]
    fn traversal_preserves_order_and_short_circuits_effects() {
        let success = VecK::traverse::<OptionK, _, _>(vec![1, 2, 3], |x| Some(x * 2));
        assert_eq!(success, Some(vec![2, 4, 6]));
        let failure = VecK::traverse::<ResultK<&'static str>, _, _>(vec![1, 2, 3], |x| {
            if x == 2 { Err("two") } else { Ok(x) }
        });
        assert_eq!(failure, Err("two"));
        assert_eq!(
            OptionK::traverse::<OptionK, _, _>(None::<i32>, Some),
            Some(None)
        );
    }
}
