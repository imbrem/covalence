/*!
Generalized algebraic theories
*/

use covalence_kernel::{
    CtxId, TermId, ULvl,
    api::derive::Strategy,
    data::term::{GNode, Gv},
    rules::KernelAPI,
};
use smallvec::{SmallVec, smallvec};

/**
A system of generalized algebraic theories
*/
pub struct GatSystem<C = CtxId, T = TermId> {
    /// The base context of this system
    base: C,
    /// The generalized algebraic theories in this system, each tagged with their parent system
    theories: Vec<Gat<C, T>>,
}

impl<C: Copy, T: Copy + PartialEq> GatSystem<C, T> {
    const MAX_GATS: usize = u32::MAX as usize;

    /// Initialize a new, empty GAT system over the given base context
    pub fn new(base: C) -> GatSystem<C, T> {
        GatSystem {
            base,
            theories: vec![],
        }
    }

    fn new_ix(&self) -> GatId {
        assert!(self.theories.len() < Self::MAX_GATS);
        GatId(self.theories.len() as u32)
    }

    /// Allocate a new GAT over the base context
    ///
    /// # Examples
    /// ```rust
    /// # use covalence::gat::*;
    /// # use covalence::kernel::*;
    /// # let mut ker = Kernel::new();
    /// let base = ker.new_ctx();
    /// let mut sys = GatSystem::new(base);
    /// let pointed = sys.new_gat(&mut ker);
    /// let carrier = sys.add_set(pointed, &mut ker);
    /// ```
    pub fn new_gat(&mut self, ker: &mut impl KernelAPI<C, T>) -> GatId {
        let ix = self.new_ix();
        let base = ker.with_parent(self.base);
        self.theories.push(Gat::new(base, ker));
        ix
    }

    /// Create a new GAT with the given parent
    pub fn with_parent(&mut self, parent: GatId, ker: &mut impl KernelAPI<C, T>) -> GatId {
        let ix = self.new_ix();
        let base = ker.with_parent(self.theories[parent.ix()].eqn_ctx);
        self.theories.push(Gat::new(base, ker));
        ix
    }

    /// Get the number of levels of the given GAT
    pub fn levels(&self, gat: GatId) -> u32 {
        self.theories[gat.ix()].def_stack.len() as u32
    }

    /// Push a new level onto a GAT
    ///
    /// Returns the index of the level
    pub fn push_level(&mut self, gat: GatId, ker: &mut impl KernelAPI<C, T>) -> u32 {
        self.theories[gat.ix()].push_level(ker)
    }

    /// Get the context for a GAT level
    pub fn level_ctx(&self, gat: GatId, level: u32) -> C {
        self.theories[gat.ix()].level_ctx(level)
    }

    /// Add a GAT level, returning it's context
    pub fn add_level(&mut self, gat: GatId, level: u32, ker: &mut impl KernelAPI<C, T>) -> C {
        self.theories[gat.ix()].add_level(level, ker)
    }

    /// Get the `n`th definition at the given level
    pub fn level_def(&self, gat: GatId, level: u32, def: u32) -> Gv<C> {
        Gv {
            ctx: self.level_ctx(gat, level),
            ix: def,
        }
    }

    /// Push a new definition of the given type to the given level
    pub fn add_def<K, S>(
        &mut self,
        gat: GatId,
        level: u32,
        ty: T,
        ker: &mut K,
        strategy: &mut S,
    ) -> Result<Gv<C>, S::Fail>
    where
        K: KernelAPI<C, T>,
        S: Strategy<C, T, K>,
    {
        self.theories[gat.ix()].add_def(level, ty, ker, strategy)
    }

    /// Add a set to the kernel
    ///
    /// This always goes on level zero
    pub fn add_set(&mut self, gat: GatId, ker: &mut impl KernelAPI<C, T>) -> Gv<C> {
        let l0_ctx = self.add_level(gat, 0, ker);
        let set = ker.add(l0_ctx, GNode::U(ULvl::SET));
        self.add_def(gat, 0, set, ker, &mut ())
            .expect("the level 0 context should not be sealed")
    }

    /// Assert a proposition in the given GAT
    pub fn add_assert<K, S>(
        &mut self,
        gat: GatId,
        prop: T,
        ker: &mut K,
        strategy: &mut S,
    ) -> Result<u32, S::Fail>
    where
        K: KernelAPI<C, T>,
        S: Strategy<C, T, K>,
    {
        self.theories[gat.ix()].add_assert(prop, ker, strategy)
    }
}

/// A generalized algebraic theory in a system
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash, PartialOrd, Ord)]
pub struct GatId(pub u32);

impl GatId {
    pub fn ix(self) -> usize {
        self.0 as usize
    }
}

/**
A generalized algebraic theory

Note that this struct carries _very little_ metadata; most of it is implicit in the contexts!
*/
pub struct Gat<C, T> {
    /// This theory's equation context
    eqn_ctx: C,
    /// This theory's definition stack
    def_stack: SmallVec<[C; 3]>,
    /// This theory's assertions
    assertions: Vec<T>,
}

/// A non-parametrized sort in a generalized algebraic theory
pub struct SortId<C>(pub Gv<C>);

impl<C: Copy, T: Copy + PartialEq> Gat<C, T> {
    const MAX_DEPTH_STACK: usize = u32::MAX as usize;

    const MAX_ASSERTIONS: usize = u32::MAX as usize;

    /// Construct a new, trivial GAT
    pub fn new(base: C, ker: &mut impl KernelAPI<C, T>) -> Gat<C, T> {
        let eqn_ctx = ker.with_parent(base);
        Gat {
            eqn_ctx,
            def_stack: smallvec![base],
            assertions: vec![],
        }
    }

    /// Get whether this GAT is trivial (w.r.t. the base context)
    pub fn is_trivial(&self, ker: &impl KernelAPI<C, T>) -> bool {
        !self.has_assertions() && !self.has_defs(ker)
    }

    /// Get whether this GAT has any assertions
    pub fn has_assertions(&self) -> bool {
        self.assertions.len() != 0
    }

    /// Get whether this GAT has any definitions
    pub fn has_defs(&self, ker: &impl KernelAPI<C, T>) -> bool {
        self.trivial_past(ker) != 0
    }

    /// Get the first level at which this GAT is trivial
    ///
    /// # Examples
    /// ```rust
    /// # use covalence::gat::*;
    /// # use covalence::kernel::*;
    /// # let mut ker = Kernel::new();
    /// let base = ker.new_ctx();
    /// let mut pointed = Gat::new(base, &mut ker);
    /// assert_eq!(pointed.trivial_past(&ker), 0);
    /// let carrier = pointed.add_set(&mut ker);
    /// assert_eq!(pointed.trivial_past(&ker), 1);
    /// ```
    pub fn trivial_past(&self, ker: &impl KernelAPI<C, T>) -> u32 {
        self.def_stack
            .iter()
            .enumerate()
            .filter(|(_, c)| ker.num_vars(**c) != 0)
            .map(|(i, _)| (i + 1) as u32)
            .next()
            .unwrap_or(0)
    }

    pub fn top(&self) -> C {
        self.def_stack.last().copied().unwrap()
    }

    pub fn levels(&self) -> u32 {
        debug_assert!(self.def_stack.len() <= Self::MAX_DEPTH_STACK);
        self.def_stack.len() as u32
    }

    pub fn level_ctx(&self, level: u32) -> C {
        self.def_stack[level as usize]
    }

    pub fn add_level(&mut self, level: u32, ker: &mut impl KernelAPI<C, T>) -> C {
        while self.levels() <= level {
            self.push_level(ker);
        }
        self.level_ctx(level)
    }

    pub fn push_level(&mut self, ker: &mut impl KernelAPI<C, T>) -> u32 {
        assert!(self.def_stack.len() < Self::MAX_DEPTH_STACK);
        let ix = self.def_stack.len() as u32;
        let new = ker.with_parent(self.top());
        ker.set_parent(self.eqn_ctx, new, &mut ())
            .expect("invalid GAT");
        self.def_stack.push(new);
        ix
    }

    pub fn add_def<K, S>(
        &mut self,
        level: u32,
        ty: T,
        ker: &mut K,
        strategy: &mut S,
    ) -> Result<Gv<C>, S::Fail>
    where
        K: KernelAPI<C, T>,
        S: Strategy<C, T, K>,
    {
        while self.levels() <= level {
            self.push_level(ker);
        }
        let ctx = self.level_ctx(level);
        ker.add_var(ctx, ty, strategy)
    }

    /// Add a set to this GAT
    ///
    /// This always goes on level zero
    pub fn add_set(&mut self, ker: &mut impl KernelAPI<C, T>) -> SortId<C> {
        let l0_ctx = self.add_level(0, ker);
        let set = ker.add(l0_ctx, GNode::U(ULvl::SET));
        SortId(
            self.add_def(0, set, ker, &mut ())
                .expect("the level 0 context should not be sealed"),
        )
    }

    /// Add an n-ary operation to this GAT
    ///
    /// This always goes on level one
    pub fn add_nary(
        &mut self,
        carrier: SortId<C>,
        arity: u32,
        ker: &mut impl KernelAPI<C, T>,
    ) -> T {
        todo!()
    }

    pub fn add_assert<K, S>(
        &mut self,
        prop: T,
        ker: &mut K,
        strategy: &mut S,
    ) -> Result<u32, S::Fail>
    where
        K: KernelAPI<C, T>,
        S: Strategy<C, T, K>,
    {
        let top = self.top();
        ker.assume(self.eqn_ctx, prop, top, strategy)?;
        Ok(self.push_assert(prop))
    }

    pub fn push_assert(&mut self, prop: T) -> u32 {
        assert!(self.assertions.len() < Self::MAX_ASSERTIONS);
        let ix = self.assertions.len() as u32;
        self.assertions.push(prop);
        ix
    }
}
