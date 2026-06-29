//! Testing utilities for `covalence-pure` and downstream crates.
//!
//! **Not for production.** [`TestCtx`] admits any proposition as an axiom, so
//! `MThm<TestCtx, _>` is an untrusted nucleus (it has no bridge to any real
//! kernel — the type makes that visible). It exists so tests mint theorems
//! through the real [`Derive::derive`] gate instead of constructing a `MThm`
//! directly, which is impossible outside this crate anyway.

use std::convert::Infallible;

use crate::{Derive, MThm, Rule, Union};

/// A context that admits any proposition as an axiom (unsound by design).
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct TestCtx;

/// `TestCtx` merges with itself trivially — enough for `zip` / `push` in tests.
impl Union<TestCtx, TestCtx> for TestCtx {
    fn union(_: TestCtx, _: TestCtx) -> TestCtx {
        TestCtx
    }
}

/// The rule behind [`TestCtx::axiom`]: admit `p` as an axiom of [`TestCtx`].
pub struct Axiom<P>(pub P);

impl<P> Rule<Axiom<P>, P, Infallible> for TestCtx {
    fn derive(Axiom(p): Axiom<P>) -> Result<(TestCtx, P), Infallible> {
        Ok((TestCtx, p))
    }
}

impl TestCtx {
    /// Mint `MThm<TestCtx, P>` for any `p`, through the real `derive` gate.
    pub fn axiom<P>(p: P) -> MThm<TestCtx, P> {
        match <MThm<TestCtx, P> as Derive<Axiom<P>, TestCtx, P, Infallible>>::derive(Axiom(p)) {
            Ok(thm) => thm,
            Err(never) => match never {},
        }
    }
}
