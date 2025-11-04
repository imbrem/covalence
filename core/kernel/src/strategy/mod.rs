use crate::data::term::*;
use crate::fact::*;

/// A strategy tells a kernel how to derive facts about terms in a context
pub trait Strategy<C, T, K: ?Sized> {
    /// The type returned by the strategy on failure
    type Fail;

    // == Derivations ==

    /// Begin a derivation
    fn start_rule(&mut self, _rule: &'static str, _ker: &mut K) -> Result<(), Self::Fail> {
        Ok(())
    }

    /// Commit the results of a successful derivation
    fn commit_rule(&mut self, _ker: &mut K) {}

    /// End a successful derivation
    fn finish_rule(&mut self, _ker: &mut K) {}

    /// An irrecoverable failure
    fn fail(&mut self, msg: &'static str, ker: &mut K) -> Self::Fail;

    // == Goals ==

    /// Begin a goal
    fn start_goal(
        &mut self,
        _goal: QAtomSeq<C, TmIn<C, T>>,
        _ker: &mut K,
    ) -> Result<(), Self::Fail> {
        Ok(())
    }

    /// Attempt to prove a goal
    fn prove_goal(
        &mut self,
        goal: QAtomSeq<C, TmIn<C, T>>,
        msg: &'static str,
        attempt_no: usize,
        ker: &mut K,
    ) -> Result<(), Self::Fail>;

    /// Called when a goal is proved
    fn finish_goal(&mut self, _goal: QAtomSeq<C, TmIn<C, T>>, _ker: &mut K) {}

    // == Imports ==

    /// Attempt to import a value into the given context
    fn import(&mut self, _ctx: C, _val: TmIn<C, T>, _ker: &mut K) -> Result<Option<T>, Self::Fail> {
        Ok(None)
    }

    /// Called when an import has succeeded
    fn finish_import(&mut self, _ctx: C, _val: TmIn<C, T>, _ker: &mut K) {}

    // == Resolutions ==

    /// Attempt to resolve a node into a value
    fn resolve(
        &mut self,
        _ctx: C,
        _val: NodeVT<C, T>,
        _ker: &mut K,
    ) -> Result<Option<TmIn<C, T>>, Self::Fail> {
        Ok(None)
    }

    /// Called when an insertion has succeeded
    fn finish_resolve(&mut self, _ctx: C, _val: NodeVT<C, T>, _ker: &mut K) {}
}

impl<C, T, K: ?Sized> Strategy<C, T, K> for () {
    type Fail = &'static str;

    fn prove_goal(
        &mut self,
        _goal: QAtomSeq<C, TmIn<C, T>>,
        msg: &'static str,
        _attempt_no: usize,
        _ker: &mut K,
    ) -> Result<(), Self::Fail> {
        Err(msg)
    }

    fn fail(&mut self, msg: &'static str, _ker: &mut K) -> Self::Fail {
        msg
    }
}
