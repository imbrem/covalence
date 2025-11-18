use crate::{
    Theorem,
    data::term::{Kind, Node, Tm1, Tm2, Tm3},
    error::KernelError,
    fact::RwIn,
    id::KernelId,
    store::{Ctx, LocalTerm},
    theorem::{Env, RwTheorem},
};

mod transform_sealed {
    use super::*;

    pub trait TmRewriterSealed<C, I, O, St, D, S = KernelId> {}

    // pub trait ReadTransformState<C, D> {
    //     fn db(&mut self) -> &Kernel<D>;
    // }

    // impl<C, D> ReadTransformState<C, D> for Kernel<D>
    // where
    //     C: Ctx<D>,
    // {
    //     fn db(&mut self) -> &Kernel<D> {
    //         self
    //     }
    // }

    // impl<C, D> ReadTransformState<C, D> for &Kernel<D>
    // where
    //     C: Ctx<D>,
    // {
    //     fn db(&mut self) -> &Kernel<D> {
    //         self
    //     }
    // }

    // pub trait WriteTransformState<C, D> {
    //     fn db_mut(&mut self) -> &mut Kernel<D>;
    // }

    // impl<C, D> WriteTransformState<C, D> for Kernel<D>
    // where
    //     C: Ctx<D>,
    // {
    //     fn db_mut(&mut self) -> &mut Kernel<D> {
    //         self
    //     }
    // }
}

use transform_sealed::{
    TmRewriterSealed,
    // MapToEqSealed,
};

/// Rewrite a term into an equivalent term given a kernel ID and context
pub trait TmRewriter<C, I, O, St, D, S = KernelId>: TmRewriterSealed<C, I, O, St, D, S> {
    fn rewrite_tm(self, ctx: Env<C, S>, lhs: I, state: &mut St) -> Result<O, KernelError>;

    fn assert_rewrite_defeq(&self) -> Result<(), KernelError> {
        Err(KernelError::RequireDefEq)
    }
}

/// Generate a rewrite given a kernel ID and context
pub trait IntoRw<C, L, R, St, D, S = KernelId>: TmRewriterSealed<C, L, R, St, D, S> {
    fn into_rw(
        self,
        ctx: Env<C, S>,
        state: &mut St,
    ) -> Result<RwTheorem<C, L, R, D, S>, KernelError>;

    fn assert_into_rw_defeq(&self) -> Result<(), KernelError> {
        Err(KernelError::RequireDefEq)
    }
}

impl<C, I, O, St, D, S> TmRewriterSealed<C, I, O, St, D, S> for ()
where
    C: Ctx<D, S>,
    I: LocalTerm<C, D, S>,
    O: LocalTerm<C, D, S>,
    I: TryInto<O>,
{
}

impl<C, I, O, St, D, S> TmRewriter<C, I, O, St, D, S> for ()
where
    C: Ctx<D, S>,
    I: LocalTerm<C, D, S> + TryInto<O>,
    O: LocalTerm<C, D, S>,
{
    fn rewrite_tm(self, _ctx: Env<C, S>, lhs: I, _state: &mut St) -> Result<O, KernelError> {
        lhs.try_into().map_err(|_| KernelError::TryIntoFailure)
    }

    fn assert_rewrite_defeq(&self) -> Result<(), KernelError> {
        Ok(())
    }
}

/// Reflexivity at a given term
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd, Default)]
pub struct Refl<T>(pub T);

impl<C, L, R, T, St, D, S> TmRewriterSealed<C, L, R, St, D, S> for Refl<T>
where
    C: Ctx<D, S>,
    L: LocalTerm<C, D, S>,
    R: LocalTerm<C, D, S>,
    T: LocalTerm<C, D, S>,
{
}

impl<C, L, R, T, St, D, S> TmRewriter<C, L, R, St, D, S> for Refl<T>
where
    C: Ctx<D, S>,
    L: LocalTerm<C, D, S> + PartialEq<T>,
    R: LocalTerm<C, D, S>,
    T: LocalTerm<C, D, S> + TryInto<R>,
{
    fn rewrite_tm(self, _ctx: Env<C, S>, lhs: L, _state: &mut St) -> Result<R, KernelError> {
        if lhs != self.0 {
            return Err(KernelError::EqMismatch);
        }
        self.0.try_into().map_err(|_| KernelError::TryIntoFailure)
    }

    fn assert_rewrite_defeq(&self) -> Result<(), KernelError> {
        Ok(())
    }
}

impl<C, L, R, T, St, D, S> IntoRw<C, L, R, St, D, S> for Refl<T>
where
    C: Ctx<D, S>,
    L: LocalTerm<C, D, S>,
    R: LocalTerm<C, D, S>,
    T: LocalTerm<C, D, S> + Clone + TryInto<L> + TryInto<R>,
{
    fn into_rw(
        self,
        ctx: Env<C, S>,
        _state: &mut St,
    ) -> Result<RwTheorem<C, L, R, D, S>, KernelError> {
        let lhs = self
            .0
            .clone()
            .try_into()
            .map_err(|_| KernelError::TryIntoFailure)?;
        let rhs = self.0.try_into().map_err(|_| KernelError::TryIntoFailure)?;
        Ok(Theorem::rw_unchecked(ctx, lhs, rhs))
    }

    fn assert_into_rw_defeq(&self) -> Result<(), KernelError> {
        Ok(())
    }
}

/// Wrap the output of a rewriter in an identity node with the given ID
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd, Default)]
pub struct WrapId<M>(u64, M);

impl<M, C, I, CO, O, IO, XO, St, D, S> TmRewriterSealed<C, I, Node<CO, O, IO, XO>, St, D, S>
    for WrapId<M>
where
    M: TmRewriterSealed<C, I, O, St, D, S>,
    C: Ctx<D, S>,
    I: LocalTerm<C, D, S>,
    O: LocalTerm<C, D, S>,
    CO: Ctx<D, S>,
    IO: LocalTerm<C, D, S>,
    XO: LocalTerm<C, D, S>,
{
}

impl<M, C, I, CO, O, IO, XO, St, D, S> TmRewriter<C, I, Node<CO, O, IO, XO>, St, D, S> for WrapId<M>
where
    M: TmRewriter<C, I, O, St, D, S>,
    C: Ctx<D, S> + Copy,
    I: LocalTerm<C, D, S>,
    O: LocalTerm<C, D, S>,
    CO: Ctx<D, S>,
    IO: LocalTerm<C, D, S>,
    XO: LocalTerm<C, D, S>,
{
    fn rewrite_tm(
        self,
        ctx: Env<C, S>,
        lhs: I,
        state: &mut St,
    ) -> Result<Node<CO, O, IO, XO>, KernelError> {
        self.1
            .rewrite_tm(ctx, lhs, state)
            .map(|tm| Node::Id(self.0, [tm]))
    }

    fn assert_rewrite_defeq(&self) -> Result<(), KernelError> {
        self.1.assert_rewrite_defeq()
    }
}

impl<M, C, I, CO, O, IO, XO, St, D, S> IntoRw<C, I, Node<CO, O, IO, XO>, St, D, S> for WrapId<M>
where
    M: IntoRw<C, I, O, St, D, S>,
    C: Ctx<D, S> + Copy,
    I: LocalTerm<C, D, S>,
    O: LocalTerm<C, D, S>,
    CO: Ctx<D, S>,
    IO: LocalTerm<C, D, S>,
    XO: LocalTerm<C, D, S>,
{
    fn into_rw(
        self,
        ctx: Env<C, S>,
        state: &mut St,
    ) -> Result<RwTheorem<C, I, Node<CO, O, IO, XO>, D, S>, KernelError> {
        self.1
            .into_rw(ctx, state)?
            .try_map_rhs(|rhs| Ok(Node::Id(self.0, [rhs])))
    }

    fn assert_into_rw_defeq(&self) -> Result<(), KernelError> {
        self.1.assert_into_rw_defeq()
    }
}

impl<C, I, O, L, R, St, D> TmRewriterSealed<C, I, O, St, D> for Theorem<RwIn<C, L, R>, D>
where
    C: Ctx<D> + PartialEq,
    I: LocalTerm<C, D>,
    O: LocalTerm<C, D>,
    L: LocalTerm<C, D>,
    R: LocalTerm<C, D>,
{
}

impl<C, I, O, L, R, St, D> TmRewriter<C, I, O, St, D> for Theorem<RwIn<C, L, R>, D>
where
    C: Ctx<D> + PartialEq,
    I: LocalTerm<C, D> + PartialEq<L>,
    O: LocalTerm<C, D>,
    L: LocalTerm<C, D>,
    R: LocalTerm<C, D> + TryInto<O>,
{
    fn rewrite_tm(self, ctx: Env<C>, lhs: I, _state: &mut St) -> Result<O, KernelError> {
        self.env_compat(&ctx)?;
        if lhs != self.0 {
            return Err(KernelError::EqMismatch);
        }
        self.fact
            .form
            .1
            .try_into()
            .map_err(|_| KernelError::TryIntoFailure)
    }
}

impl<C, I, O, L, R, St, D> IntoRw<C, I, O, St, D> for Theorem<RwIn<C, L, R>, D>
where
    C: Ctx<D> + PartialEq,
    I: LocalTerm<C, D>,
    O: LocalTerm<C, D>,
    L: LocalTerm<C, D> + TryInto<I>,
    R: LocalTerm<C, D> + TryInto<O>,
{
    fn into_rw(self, ctx: Env<C>, _state: &mut St) -> Result<RwTheorem<C, I, O, D>, KernelError> {
        self.env_compat(&ctx)?;
        let lhs = self
            .fact
            .form
            .0
            .try_into()
            .map_err(|_| KernelError::TryIntoFailure)?;
        let rhs = self
            .fact
            .form
            .1
            .try_into()
            .map_err(|_| KernelError::TryIntoFailure)?;
        Ok(Theorem::rw_unchecked(ctx, lhs, rhs))
    }
}

impl<MT, MI, MS, C, CN, T, I, S, TO, IO, SO, St, D>
    TmRewriterSealed<C, Node<CN, T, I, S>, Node<CN, TO, IO, SO>, St, D> for Node<CN, MT, MI, MS>
where
    MT: TmRewriter<C, T, TO, St, D>,
    MI: TmRewriter<C, I, IO, St, D>,
    MS: TmRewriter<C, S, SO, St, D>,
    C: Ctx<D>,
    CN: Ctx<D>,
    T: LocalTerm<C, D>,
    I: LocalTerm<C, D>,
    S: LocalTerm<C, D>,
    TO: LocalTerm<C, D>,
    IO: LocalTerm<C, D>,
    SO: LocalTerm<C, D>,
{
}

impl<MT, MI, MS, C, CN, T, I, S, TO, IO, SO, St, D>
    TmRewriter<C, Node<CN, T, I, S>, Node<CN, TO, IO, SO>, St, D> for Node<CN, MT, MI, MS>
where
    MT: TmRewriter<C, T, TO, St, D>,
    MI: TmRewriter<C, I, IO, St, D>,
    MS: TmRewriter<C, S, SO, St, D>,
    C: Ctx<D> + Copy,
    CN: Ctx<D> + PartialEq,
    T: LocalTerm<C, D>,
    I: LocalTerm<C, D>,
    S: LocalTerm<C, D>,
    TO: LocalTerm<C, D>,
    IO: LocalTerm<C, D>,
    SO: LocalTerm<C, D>,
{
    fn rewrite_tm(
        self,
        ctx: Env<C>,
        lhs: Node<CN, T, I, S>,
        state: &mut St,
    ) -> Result<Node<CN, TO, IO, SO>, KernelError> {
        let res = self.zip(lhs).map_err(|_| KernelError::ShapeMismatch)?;
        res.try_map_ix(|(map, tm)| map.rewrite_tm(ctx, tm, state))?
            .try_map_quote(|(map, tm)| map.rewrite_tm(ctx, tm, state))?
            .try_map_syn(|(map, tm)| {
                map.assert_rewrite_defeq()?;
                map.rewrite_tm(ctx, tm, state)
            })
    }
}

impl<K, M, C, I, O, St, D> TmRewriterSealed<C, Tm1<K, I>, Tm1<K, O>, St, D> for Tm1<K, M>
where
    M: TmRewriter<C, I, O, St, D>,
    K: Kind<1>,
{
}

impl<K, M, C, I, O, St, D> TmRewriter<C, Tm1<K, I>, Tm1<K, O>, St, D> for Tm1<K, M>
where
    C: Ctx<D>,
    M: TmRewriter<C, I, O, St, D>,
    K: Kind<1>,
{
    fn rewrite_tm(
        self,
        ctx: Env<C>,
        lhs: Tm1<K, I>,
        state: &mut St,
    ) -> Result<Tm1<K, O>, KernelError> {
        Ok(Tm1(lhs.0, self.1.rewrite_tm(ctx, lhs.1, state)?))
    }
}

impl<K, M, C, CN, T, I, S, O, St, D> TmRewriterSealed<C, Node<CN, T, I, S>, Tm1<K, O>, St, D>
    for Tm1<K, M>
where
    M: TmRewriter<C, T, O, St, D>,
    CN: Ctx<D>,
    T: LocalTerm<C, D>,
    I: LocalTerm<C, D>,
    S: LocalTerm<C, D>,
    O: LocalTerm<C, D>,
    K: Kind<1>,
{
}

impl<K, M, C, CN, T, I, S, O, St, D> TmRewriter<C, Node<CN, T, I, S>, Tm1<K, O>, St, D>
    for Tm1<K, M>
where
    C: Ctx<D>,
    M: TmRewriter<C, T, O, St, D>,
    CN: Ctx<D>,
    T: LocalTerm<C, D>,
    I: LocalTerm<C, D>,
    S: LocalTerm<C, D>,
    O: LocalTerm<C, D>,
    K: Kind<1>,
    Node<CN, T, I, S>: TryInto<Tm1<K, T>>,
{
    fn rewrite_tm(
        self,
        ctx: Env<C>,
        lhs: Node<CN, T, I, S>,
        state: &mut St,
    ) -> Result<Tm1<K, O>, KernelError> {
        self.rewrite_tm(
            ctx,
            lhs.try_into().map_err(|_| KernelError::ShapeMismatch)?,
            state,
        )
    }
}

impl<K, ML, MR, C, IL, IR, LO, RO, St, D> TmRewriterSealed<C, Tm2<K, IL, IR>, Tm2<K, LO, RO>, St, D>
    for Tm2<K, ML, MR>
where
    ML: TmRewriter<C, IL, LO, St, D>,
    MR: TmRewriter<C, IR, RO, St, D>,
    K: Kind<2>,
{
}

impl<K, ML, MR, C, IL, IR, LO, RO, St, D> TmRewriter<C, Tm2<K, IL, IR>, Tm2<K, LO, RO>, St, D>
    for Tm2<K, ML, MR>
where
    C: Ctx<D> + Copy,
    ML: TmRewriter<C, IL, LO, St, D>,
    MR: TmRewriter<C, IR, RO, St, D>,
    K: Kind<2>,
{
    fn rewrite_tm(
        self,
        ctx: Env<C>,
        lhs: Tm2<K, IL, IR>,
        state: &mut St,
    ) -> Result<Tm2<K, LO, RO>, KernelError> {
        Ok(Tm2(
            lhs.0,
            self.1.rewrite_tm(ctx, lhs.1, state)?,
            self.2.rewrite_tm(ctx, lhs.2, state)?,
        ))
    }
}

impl<K, ML, MR, C, CN, T, I, S, LO, RO, St, D>
    TmRewriterSealed<C, Node<CN, T, I, S>, Tm2<K, LO, RO>, St, D> for Tm2<K, ML, MR>
where
    ML: TmRewriter<C, T, LO, St, D>,
    MR: TmRewriter<C, T, RO, St, D>,
    CN: Ctx<D>,
    T: LocalTerm<C, D>,
    I: LocalTerm<C, D>,
    S: LocalTerm<C, D>,
    K: Kind<2>,
{
}

impl<K, ML, MR, C, CN, T, I, S, LO, RO, St, D>
    TmRewriter<C, Node<CN, T, I, S>, Tm2<K, LO, RO>, St, D> for Tm2<K, ML, MR>
where
    C: Ctx<D> + Copy,
    ML: TmRewriter<C, T, LO, St, D>,
    MR: TmRewriter<C, T, RO, St, D>,
    CN: Ctx<D> + PartialEq,
    T: LocalTerm<C, D>,
    I: LocalTerm<C, D>,
    S: LocalTerm<C, D>,
    K: Kind<2>,
    Node<CN, T, I, S>: TryInto<Tm2<K, T, T>>,
{
    fn rewrite_tm(
        self,
        ctx: Env<C>,
        lhs: Node<CN, T, I, S>,
        state: &mut St,
    ) -> Result<Tm2<K, LO, RO>, KernelError> {
        self.rewrite_tm(
            ctx,
            lhs.try_into().map_err(|_| KernelError::ShapeMismatch)?,
            state,
        )
    }
}

impl<K, ML, MM, MR, C, IL, IM, IR, LO, MO, RO, St, D>
    TmRewriterSealed<C, Tm3<K, IL, IM, IR>, Tm3<K, LO, MO, RO>, St, D> for Tm3<K, ML, MM, MR>
where
    C: Ctx<D> + Copy,
    ML: TmRewriter<C, IL, LO, St, D>,
    MM: TmRewriter<C, IM, MO, St, D>,
    MR: TmRewriter<C, IR, RO, St, D>,
    K: Kind<3>,
{
}

impl<K, ML, MM, MR, C, IL, IM, IR, LO, MO, RO, St, D>
    TmRewriter<C, Tm3<K, IL, IM, IR>, Tm3<K, LO, MO, RO>, St, D> for Tm3<K, ML, MM, MR>
where
    C: Ctx<D> + Copy,
    ML: TmRewriter<C, IL, LO, St, D>,
    MM: TmRewriter<C, IM, MO, St, D>,
    MR: TmRewriter<C, IR, RO, St, D>,
    K: Kind<3>,
{
    fn rewrite_tm(
        self,
        ctx: Env<C>,
        lhs: Tm3<K, IL, IM, IR>,
        state: &mut St,
    ) -> Result<Tm3<K, LO, MO, RO>, KernelError> {
        Ok(Tm3(
            lhs.0,
            self.1.rewrite_tm(ctx, lhs.1, state)?,
            self.2.rewrite_tm(ctx, lhs.2, state)?,
            self.3.rewrite_tm(ctx, lhs.3, state)?,
        ))
    }
}

impl<K, ML, MM, MR, C, CN, T, I, S, LO, MO, RO, St, D>
    TmRewriterSealed<C, Node<CN, T, I, S>, Tm3<K, LO, MO, RO>, St, D> for Tm3<K, ML, MM, MR>
where
    ML: TmRewriter<C, T, LO, St, D>,
    MM: TmRewriter<C, T, MO, St, D>,
    MR: TmRewriter<C, T, RO, St, D>,
    CN: Ctx<D>,
    T: LocalTerm<C, D>,
    I: LocalTerm<C, D>,
    S: LocalTerm<C, D>,
    K: Kind<3>,
{
}

impl<K, ML, MM, MR, C, CN, T, I, S, LO, MO, RO, St, D>
    TmRewriter<C, Node<CN, T, I, S>, Tm3<K, LO, MO, RO>, St, D> for Tm3<K, ML, MM, MR>
where
    C: Ctx<D> + Copy,
    ML: TmRewriter<C, T, LO, St, D>,
    MM: TmRewriter<C, T, MO, St, D>,
    MR: TmRewriter<C, T, RO, St, D>,
    CN: Ctx<D> + PartialEq,
    T: LocalTerm<C, D>,
    I: LocalTerm<C, D>,
    S: LocalTerm<C, D>,
    K: Kind<3>,
    Node<CN, T, I, S>: TryInto<Tm3<K, T, T, T>>,
{
    fn rewrite_tm(
        self,
        ctx: Env<C>,
        lhs: Node<CN, T, I, S>,
        state: &mut St,
    ) -> Result<Tm3<K, LO, MO, RO>, KernelError> {
        self.rewrite_tm(
            ctx,
            lhs.try_into().map_err(|_| KernelError::ShapeMismatch)?,
            state,
        )
    }
}
