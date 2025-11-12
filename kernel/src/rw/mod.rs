use crate::{
    Theorem,
    data::term::{Kind, Node, Tm1, Tm2, Tm3},
    error::KernelError,
    fact::RwIn,
    store::{Ctx, LocalTerm},
    theorem::CtxIn,
};

mod transform_sealed {
    // use crate::{Kernel, store::Ctx};

    pub trait TmRewriterSealed<C, I, O, St, D> {}

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
pub trait TmRewriter<C, I, O, St, D>: TmRewriterSealed<C, I, O, St, D> {
    fn rewrite_tm(self, ctx: CtxIn<C>, lhs: I, state: &mut St) -> Result<O, KernelError>;

    fn assert_defeq(&self) -> Result<(), KernelError> {
        Err(KernelError::RequireDefEq)
    }
}

/// Generate a rewrite given a kernel ID and context
pub trait IntoRw<C, I, O, St, D>: TmRewriterSealed<C, I, O, St, D> {
    fn into_rw(
        self,
        ctx: CtxIn<C>,
        state: &mut St,
    ) -> Result<Theorem<RwIn<C, I, O>, D>, KernelError>;

    fn assert_defeq(&self) -> Result<(), KernelError> {
        Err(KernelError::RequireDefEq)
    }
}

impl<C, I, O, St, D> TmRewriterSealed<C, I, O, St, D> for ()
where
    I: LocalTerm<C, D>,
    O: LocalTerm<C, D>,
    I: TryInto<O>,
{
}

impl<C, I, O, St, D> TmRewriter<C, I, O, St, D> for ()
where
    I: LocalTerm<C, D>,
    O: LocalTerm<C, D>,
    I: TryInto<O>,
{
    fn rewrite_tm(self, _ctx: CtxIn<C>, lhs: I, _state: &mut St) -> Result<O, KernelError> {
        lhs.try_into().map_err(|_| KernelError::TryIntoFailure)
    }

    fn assert_defeq(&self) -> Result<(), KernelError> {
        Ok(())
    }
}

/// Remove an identity node
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd, Default)]
pub struct RemoveId;

/// Wrap a term in an identity `Node`
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd, Default)]
pub struct IdNode;

/// Wrap a term in a quote
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd, Default)]
pub struct QuoteNode;

/// Cons a `Node` in the ambient context
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd, Default)]
pub struct ConsAmb;

/// Get a `Node` in the ambient context
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd, Default)]
pub struct GetAmb;

/// Lookup a `Node` in the ambient context
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd, Default)]
pub struct LookupAmb;

/// Import a `TmId` into an `Ix` in the ambient context
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd, Default)]
pub struct ImportAmb;

/// Get the import of a `TmId` into an `Ix` in the ambient context
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd, Default)]
pub struct GetImportAmb;

/// Lookup the import of a `TmId` into an `Ix` in the ambient context
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd, Default)]
pub struct LookupImportAmb;

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
    fn rewrite_tm(self, ctx: CtxIn<C>, lhs: I, _state: &mut St) -> Result<O, KernelError> {
        if self.id != ctx.0 {
            return Err(KernelError::IdMismatch);
        }
        if self.ctx != ctx.1 {
            return Err(KernelError::CtxMismatch);
        }
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
    fn into_rw(
        self,
        ctx: CtxIn<C>,
        _state: &mut St,
    ) -> Result<Theorem<RwIn<C, I, O>, D>, KernelError> {
        if self.id != ctx.0 {
            return Err(KernelError::IdMismatch);
        }
        if self.ctx != ctx.1 {
            return Err(KernelError::CtxMismatch);
        }
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
        Ok(Theorem::new_unchecked(ctx.0, RwIn::new(ctx.1, lhs, rhs)))
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
        ctx: CtxIn<C>,
        lhs: Node<CN, T, I, S>,
        state: &mut St,
    ) -> Result<Node<CN, TO, IO, SO>, KernelError> {
        let res = self.zip(lhs).map_err(|_| KernelError::ShapeMismatch)?;
        res.try_map_children(|(map, tm)| map.rewrite_tm(ctx, tm, state))?
            .try_map_import(|(map, tm)| map.rewrite_tm(ctx, tm, state))?
            .try_map_closures(|(map, tm)| {
                map.assert_defeq()?;
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
        ctx: CtxIn<C>,
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
        ctx: CtxIn<C>,
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
        ctx: CtxIn<C>,
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
        ctx: CtxIn<C>,
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
        ctx: CtxIn<C>,
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
        ctx: CtxIn<C>,
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

// impl<T, U, C, I, E, St, D> TmRewriterSealed<C, I, E, St, D> for (T, U)
// where
//     T: TmRewriter<C, I, E, St, D>,
//     U: TmRewriter<C, T::IntoRw, E, St, D>,
// {
// }

// impl<T, U, C, I, E, St, D> TmRewriter<C, I, E, St, D> for (T, U)
// where
//     C: Ctx<D> + Copy,
//     T: TmRewriter<C, I, E, St, D>,
//     U: TmRewriter<C, T::IntoRw, E, St, D>,
// {
//     type IntoRw = U::IntoRw;

//     fn rewrite_tm(self, id: KernelId, ctx: C, lhs: I, state: &mut St) -> Result<Self::IntoRw, E> {
//         let mid = self.0.rewrite_tm(id, ctx, lhs, state)?;
//         self.1.rewrite_tm(id, ctx, mid, state)
//     }
// }

// pub trait MapToEq<C, I, E, St, D>: MapToEqSealed<C, I, E, St, D> {
//     type ToEq: LocalTerm<C, D>;

//     fn to_eq(self, lhs: &I, state: &mut St) -> Result<Self::ToEq, E>;

//     fn assert_to_defeq(&self) -> Result<(), KernelError> {
//         Err(KernelError::RequireDefEq)
//     }
// }

// impl<C, I, E, St, D> MapToEqSealed<C, I, E, St, D> for () {}

// impl<C, I, E, St, D> MapToEq<C, I, E, St, D> for ()
// where
//     I: Clone + LocalTerm<C, D>,
// {
//     type ToEq = I;

//     fn to_eq(self, lhs: &I, _state: &mut St) -> Result<I, E> {
//         Ok(lhs.clone())
//     }

//     fn assert_to_defeq(&self) -> Result<(), KernelError> {
//         Ok(())
//     }
// }

// impl<C, I, L, R, St, D> MapToEqSealed<C, I, KernelError, St, D> for Theorem<RwIn<C, L, R>, D>
// where
//     C: Ctx<D>,
//     I: LocalTerm<C, D>,
//     L: LocalTerm<C, D>,
//     R: LocalTerm<C, D>,
// {
// }

// impl<C, I, L, R, St, D> MapToEq<C, I, KernelError, St, D> for Theorem<RwIn<C, L, R>, D>
// where
//     C: Ctx<D>,
//     I: LocalTerm<C, D> + PartialEq<L>,
//     L: LocalTerm<C, D>,
//     R: LocalTerm<C, D>,
//     St: TransformState<C, D>,
// {
//     type ToEq = R;

//     fn to_eq(self, lhs: &I, state: &mut St) -> Result<R, KernelError> {
//         state.check(
//             &self.fact.ctx,
//             self.id,
//             self.0.relocatable() && self.1.relocatable(),
//         )?;
//         if *lhs != self.0 {
//             return Err(KernelError::EqMismatch);
//         }
//         Ok(self.fact.form.1)
//     }
// }

// impl<K, M, C, I, E, St, D> MapToEqSealed<C, Tm1<K, I>, E, St, D> for Tm1<K, M>
// where
//     M: MapToEq<C, I, E, St, D>,
//     K: Kind<1>,
// {
// }

// impl<K, M, C, I, E, St, D> MapToEq<C, Tm1<K, I>, E, St, D> for Tm1<K, M>
// where
//     C: Ctx<D>,
//     M: MapToEq<C, I, E, St, D>,
//     K: Kind<1> + Copy,
// {
//     type ToEq = Tm1<K, M::ToEq>;

//     fn to_eq(self, lhs: &Tm1<K, I>, state: &mut St) -> Result<Self::ToEq, E> {
//         Ok(Tm1(lhs.0, self.1.to_eq(&lhs.1, state)?))
//     }
// }

// impl<K, ML, MR, C, IL, IR, E, St, D> MapToEqSealed<C, Tm2<K, IL, IR>, E, St, D> for Tm2<K, ML, MR>
// where
//     ML: MapToEq<C, IL, E, St, D>,
//     MR: MapToEq<C, IR, E, St, D>,
//     K: Kind<2>,
// {
// }

// impl<K, ML, MR, C, IL, IR, E, St, D> MapToEq<C, Tm2<K, IL, IR>, E, St, D> for Tm2<K, ML, MR>
// where
//     C: Ctx<D>,
//     ML: MapToEq<C, IL, E, St, D>,
//     MR: MapToEq<C, IR, E, St, D>,
//     K: Kind<2> + Copy,
// {
//     type ToEq = Tm2<K, ML::ToEq, MR::ToEq>;

//     fn to_eq(self, lhs: &Tm2<K, IL, IR>, state: &mut St) -> Result<Self::ToEq, E> {
//         Ok(Tm2(
//             lhs.0,
//             self.1.to_eq(&lhs.1, state)?,
//             self.2.to_eq(&lhs.2, state)?,
//         ))
//     }
// }

// impl<MT, MI, MS, C, CN, T, I, S, E, St, D> MapToEqSealed<C, Node<CN, T, I, S>, E, St, D>
//     for Node<CN, MT, MI, MS>
// where
//     MT: MapToEq<C, T, E, St, D>,
//     MI: MapToEq<C, I, E, St, D>,
//     MS: MapToEq<C, S, KernelError, St, D>,
//     C: Ctx<D>,
//     CN: Ctx<D>,
//     T: LocalTerm<C, D>,
//     I: LocalTerm<C, D>,
// {
// }

// impl<MT, MI, MS, C, CN, T, I, S, St, D> MapToEq<C, Node<CN, T, I, S>, KernelError, St, D>
//     for Node<CN, MT, MI, MS>
// where
//     MT: MapToEq<C, T, KernelError, St, D>,
//     MI: MapToEq<C, I, KernelError, St, D>,
//     MS: MapToEq<C, S, KernelError, St, D>,
//     C: Ctx<D>,
//     CN: Ctx<D> + PartialEq + Clone,
//     T: LocalTerm<C, D>,
//     I: LocalTerm<C, D>,
// {
//     type ToEq = Node<CN, MT::ToEq, MI::ToEq, MS::ToEq>;

//     fn to_eq(self, lhs: &Node<CN, T, I, S>, state: &mut St) -> Result<Self::ToEq, KernelError> {
//         let res = self
//             .zip(lhs.subterms_as_ref())
//             .map_err(|_| KernelError::ShapeMismatch)?;
//         res.try_map_children(|(map, tm)| map.to_eq(tm, state))?
//             .try_map_import(|(map, tm)| map.to_eq(tm, state))?
//             .try_map_closures(|(map, tm)| {
//                 map.assert_to_defeq()?;
//                 map.to_eq(tm, state)
//             })
//     }
// }

// impl<T, U, C, I, E, St, D> MapToEqSealed<C, I, E, St, D> for (T, U)
// where
//     T: MapToEq<C, I, E, St, D>,
//     U: MapIntoEq<C, T::ToEq, E, St, D>,
// {
// }

// impl<T, U, C, I, E, St, D> MapToEq<C, I, E, St, D> for (T, U)
// where
//     T: MapToEq<C, I, E, St, D>,
//     U: MapIntoEq<C, T::ToEq, E, St, D>,
// {
//     type ToEq = U::IntoEq;

//     fn to_eq(self, lhs: &I, state: &mut St) -> Result<Self::ToEq, E> {
//         let mid = self.0.to_eq(lhs, state)?;
//         self.1.into_eq(mid, state)
//     }
// }

// impl<C, I, L, R, St, D> MapIntoEqSealed<C, I, KernelError, St, D> for &Theorem<RwIn<C, L, R>, D>
// where
//     C: Ctx<D>,
//     I: LocalTerm<C, D>,
//     L: LocalTerm<C, D>,
//     R: LocalTerm<C, D>,
// {
// }

// impl<'a, C, I, L, R, St, D> MapIntoEq<C, I, KernelError, St, D> for &'a Theorem<RwIn<C, L, R>, D>
// where
//     C: Ctx<D>,
//     I: LocalTerm<C, D> + PartialEq<L>,
//     L: LocalTerm<C, D>,
//     R: LocalTerm<C, D>,
//     St: TransformState<C, D>,
// {
//     type IntoEq = &'a R;

//     fn into_eq(self, lhs: I, state: &mut St) -> Result<&'a R, KernelError> {
//         self.to_eq(&lhs, state)
//     }
// }

// impl<C, I, L, R, St, D> MapToEqSealed<C, I, KernelError, St, D> for &Theorem<RwIn<C, L, R>, D>
// where
//     C: Ctx<D>,
//     I: LocalTerm<C, D>,
//     L: LocalTerm<C, D>,
//     R: LocalTerm<C, D>,
// {
// }

// impl<'a, C, I, L, R, St, D> MapToEq<C, I, KernelError, St, D> for &'a Theorem<RwIn<C, L, R>, D>
// where
//     C: Ctx<D>,
//     I: LocalTerm<C, D> + PartialEq<L>,
//     L: LocalTerm<C, D>,
//     R: LocalTerm<C, D>,
//     St: TransformState<C, D>,
// {
//     type ToEq = &'a R;

//     fn to_eq(self, lhs: &I, state: &mut St) -> Result<&'a R, KernelError> {
//         state.check(
//             &self.fact.ctx,
//             self.id,
//             self.0.relocatable() && self.1.relocatable(),
//         )?;
//         if *lhs != self.0 {
//             return Err(KernelError::EqMismatch);
//         }
//         Ok(&self.1)
//     }
// }

// impl<'a, K, M, C, I, E, St, D> MapIntoEqSealed<C, Tm1<K, I>, E, St, D> for &'a Tm1<K, M>
// where
//     &'a M: MapIntoEq<C, I, E, St, D>,
//     K: Kind<1>,
// {
// }

// impl<'a, K, M, C, I, E, St, D> MapIntoEq<C, Tm1<K, I>, E, St, D> for &'a Tm1<K, M>
// where
//     C: Ctx<D>,
//     &'a M: MapIntoEq<C, I, E, St, D>,
//     K: Kind<1>,
// {
//     type IntoEq = Tm1<K, <&'a M as MapIntoEq<C, I, E, St, D>>::IntoEq>;

//     fn into_eq(self, lhs: Tm1<K, I>, state: &mut St) -> Result<Self::IntoEq, E> {
//         Ok(Tm1(lhs.0, (&self.1).into_eq(lhs.1, state)?))
//     }
// }

// impl<'a, K, M, C, I, E, St, D> MapToEqSealed<C, Tm1<K, I>, E, St, D> for &'a Tm1<K, M>
// where
//     &'a M: MapToEq<C, I, E, St, D>,
//     K: Kind<1>,
// {
// }

// impl<'a, K, M, C, I, E, St, D> MapToEq<C, Tm1<K, I>, E, St, D> for &'a Tm1<K, M>
// where
//     C: Ctx<D>,
//     &'a M: MapToEq<C, I, E, St, D>,
//     K: Kind<1> + Copy,
// {
//     type ToEq = Tm1<K, <&'a M as MapToEq<C, I, E, St, D>>::ToEq>;

//     fn to_eq(self, lhs: &Tm1<K, I>, state: &mut St) -> Result<Self::ToEq, E> {
//         Ok(Tm1(lhs.0, (&self.1).to_eq(&lhs.1, state)?))
//     }
// }

// impl<'a, K, ML, MR, C, IL, IR, E, St, D> MapIntoEqSealed<C, Tm2<K, IL, IR>, E, St, D>
//     for &'a Tm2<K, ML, MR>
// where
//     &'a ML: MapIntoEq<C, IL, E, St, D>,
//     &'a MR: MapIntoEq<C, IR, E, St, D>,
//     K: Kind<2>,
// {
// }

// impl<'a, K, ML, MR, C, IL, IR, E, St, D> MapIntoEq<C, Tm2<K, IL, IR>, E, St, D>
//     for &'a Tm2<K, ML, MR>
// where
//     C: Ctx<D>,
//     &'a ML: MapIntoEq<C, IL, E, St, D>,
//     &'a MR: MapIntoEq<C, IR, E, St, D>,
//     K: Kind<2>,
// {
//     type IntoEq = Tm2<
//         K,
//         <&'a ML as MapIntoEq<C, IL, E, St, D>>::IntoEq,
//         <&'a MR as MapIntoEq<C, IR, E, St, D>>::IntoEq,
//     >;

//     fn into_eq(self, lhs: Tm2<K, IL, IR>, state: &mut St) -> Result<Self::IntoEq, E> {
//         Ok(Tm2(
//             lhs.0,
//             (&self.1).into_eq(lhs.1, state)?,
//             (&self.2).into_eq(lhs.2, state)?,
//         ))
//     }
// }

// impl<'a, K, ML, MR, C, IL, IR, E, St, D> MapToEqSealed<C, Tm2<K, IL, IR>, E, St, D>
//     for &'a Tm2<K, ML, MR>
// where
//     &'a ML: MapToEq<C, IL, E, St, D>,
//     &'a MR: MapToEq<C, IR, E, St, D>,
//     K: Kind<2>,
// {
// }

// impl<'a, K, ML, MR, C, IL, IR, E, St, D> MapToEq<C, Tm2<K, IL, IR>, E, St, D> for &'a Tm2<K, ML, MR>
// where
//     C: Ctx<D>,
//     &'a ML: MapToEq<C, IL, E, St, D>,
//     &'a MR: MapToEq<C, IR, E, St, D>,
//     K: Kind<2> + Copy,
// {
//     type ToEq = Tm2<
//         K,
//         <&'a ML as MapToEq<C, IL, E, St, D>>::ToEq,
//         <&'a MR as MapToEq<C, IR, E, St, D>>::ToEq,
//     >;

//     fn to_eq(self, lhs: &Tm2<K, IL, IR>, state: &mut St) -> Result<Self::ToEq, E> {
//         Ok(Tm2(
//             lhs.0,
//             (&self.1).to_eq(&lhs.1, state)?,
//             (&self.2).to_eq(&lhs.2, state)?,
//         ))
//     }
// }

// impl<'a, MT, MI, MS, C, CN, T, I, S, E, St, D> MapIntoEqSealed<C, Node<CN, T, I, S>, E, St, D>
//     for &'a Node<CN, MT, MI, MS>
// where
//     &'a MT: MapIntoEq<C, T, E, St, D>,
//     &'a MI: MapIntoEq<C, I, E, St, D>,
//     &'a MS: MapIntoEq<C, S, KernelError, St, D>,
//     C: Ctx<D>,
//     CN: Ctx<D>,
//     T: LocalTerm<C, D>,
//     I: LocalTerm<C, D>,
// {
// }

// impl<'a, MT, MI, MS, C, CN, T, I, S, St, D> MapIntoEq<C, Node<CN, T, I, S>, KernelError, St, D>
//     for &'a Node<CN, MT, MI, MS>
// where
//     &'a MT: MapIntoEq<C, T, KernelError, St, D>,
//     &'a MI: MapIntoEq<C, I, KernelError, St, D>,
//     &'a MS: MapIntoEq<C, S, KernelError, St, D>,
//     C: Ctx<D>,
//     CN: Ctx<D> + PartialEq + Clone,
//     T: LocalTerm<C, D>,
//     I: LocalTerm<C, D>,
// {
//     type IntoEq = Node<
//         CN,
//         <&'a MT as MapIntoEq<C, T, KernelError, St, D>>::IntoEq,
//         <&'a MI as MapIntoEq<C, I, KernelError, St, D>>::IntoEq,
//         <&'a MS as MapIntoEq<C, S, KernelError, St, D>>::IntoEq,
//     >;

//     fn into_eq(self, lhs: Node<CN, T, I, S>, state: &mut St) -> Result<Self::IntoEq, KernelError> {
//         self.subterms_as_ref().into_eq(lhs, state)
//     }
// }

// impl<'a, MT, MI, MS, C, CN, T, I, S, E, St, D> MapToEqSealed<C, Node<CN, T, I, S>, E, St, D>
//     for &'a Node<CN, MT, MI, MS>
// where
//     &'a MT: MapToEq<C, T, E, St, D>,
//     &'a MI: MapToEq<C, I, E, St, D>,
//     &'a MS: MapToEq<C, S, KernelError, St, D>,
//     C: Ctx<D>,
//     CN: Ctx<D>,
//     T: LocalTerm<C, D>,
//     I: LocalTerm<C, D>,
// {
// }

// impl<'a, MT, MI, MS, C, CN, T, I, S, St, D> MapToEq<C, Node<CN, T, I, S>, KernelError, St, D>
//     for &'a Node<CN, MT, MI, MS>
// where
//     &'a MT: MapToEq<C, T, KernelError, St, D>,
//     &'a MI: MapToEq<C, I, KernelError, St, D>,
//     &'a MS: MapToEq<C, S, KernelError, St, D>,
//     C: Ctx<D>,
//     CN: Ctx<D> + PartialEq + Clone,
//     T: LocalTerm<C, D>,
//     I: LocalTerm<C, D>,
// {
//     type ToEq = Node<
//         CN,
//         <&'a MT as MapToEq<C, T, KernelError, St, D>>::ToEq,
//         <&'a MI as MapToEq<C, I, KernelError, St, D>>::ToEq,
//         <&'a MS as MapToEq<C, S, KernelError, St, D>>::ToEq,
//     >;

//     fn to_eq(self, lhs: &Node<CN, T, I, S>, state: &mut St) -> Result<Self::ToEq, KernelError> {
//         self.subterms_as_ref().to_eq(lhs, state)
//     }
// }
