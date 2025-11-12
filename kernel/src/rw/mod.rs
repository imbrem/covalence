use crate::{
    Theorem,
    data::term::{Kind, Node, Tm1, Tm2, Tm3},
    error::KernelError,
    fact::RwIn,
    store::{Ctx, LocalTerm},
};

mod transform_sealed {
    use crate::{error::KernelError, id::KernelId};

    pub trait MapIntoEqSealed<C, I, E, St, D> {}

    // pub trait MapToEqSealed<C, I, E, St, D> {}

    pub trait TransformState<C, D> {
        fn check(&mut self, ctx: &C, id: KernelId, relocatable: bool) -> Result<(), KernelError>;
    }
}

use transform_sealed::{
    MapIntoEqSealed,
    // MapToEqSealed,
    TransformState,
};

pub trait MapIntoEq<C, I, E, St, D>: MapIntoEqSealed<C, I, E, St, D> {
    type IntoEq: LocalTerm<C, D>;

    fn into_eq(self, lhs: I, state: &mut St) -> Result<Self::IntoEq, E>;

    fn assert_into_defeq(&self) -> Result<(), KernelError> {
        Err(KernelError::RequireDefEq)
    }
}

impl<C, I, E, St, D> MapIntoEqSealed<C, I, E, St, D> for () {}

impl<C, I, E, St, D> MapIntoEq<C, I, E, St, D> for ()
where
    I: LocalTerm<C, D>,
{
    type IntoEq = I;

    fn into_eq(self, lhs: I, _state: &mut St) -> Result<I, E> {
        Ok(lhs)
    }

    fn assert_into_defeq(&self) -> Result<(), KernelError> {
        Ok(())
    }
}

impl<C, I, L, R, St, D> MapIntoEqSealed<C, I, KernelError, St, D> for Theorem<RwIn<C, L, R>, D>
where
    C: Ctx<D>,
    I: LocalTerm<C, D>,
    L: LocalTerm<C, D>,
    R: LocalTerm<C, D>,
{
}

impl<C, I, L, R, St, D> MapIntoEq<C, I, KernelError, St, D> for Theorem<RwIn<C, L, R>, D>
where
    C: Ctx<D>,
    I: LocalTerm<C, D> + PartialEq<L>,
    L: LocalTerm<C, D>,
    R: LocalTerm<C, D>,
    St: TransformState<C, D>,
{
    type IntoEq = R;

    fn into_eq(self, lhs: I, state: &mut St) -> Result<R, KernelError> {
        state.check(
            &self.fact.ctx,
            self.id,
            self.0.relocatable() && self.1.relocatable(),
        )?;
        if lhs != self.0 {
            return Err(KernelError::EqMismatch);
        }
        Ok(self.fact.form.1)
    }
}

impl<MT, MI, MS, C, CN, T, I, S, E, St, D> MapIntoEqSealed<C, Node<CN, T, I, S>, E, St, D>
    for Node<CN, MT, MI, MS>
where
    MT: MapIntoEq<C, T, E, St, D>,
    MI: MapIntoEq<C, I, E, St, D>,
    MS: MapIntoEq<C, S, KernelError, St, D>,
    C: Ctx<D>,
    CN: Ctx<D>,
    T: LocalTerm<C, D>,
    I: LocalTerm<C, D>,
{
}

impl<MT, MI, MS, C, CN, T, I, S, St, D> MapIntoEq<C, Node<CN, T, I, S>, KernelError, St, D>
    for Node<CN, MT, MI, MS>
where
    MT: MapIntoEq<C, T, KernelError, St, D>,
    MI: MapIntoEq<C, I, KernelError, St, D>,
    MS: MapIntoEq<C, S, KernelError, St, D>,
    C: Ctx<D>,
    CN: Ctx<D> + PartialEq,
    T: LocalTerm<C, D>,
    I: LocalTerm<C, D>,
{
    type IntoEq = Node<CN, MT::IntoEq, MI::IntoEq, MS::IntoEq>;

    fn into_eq(self, lhs: Node<CN, T, I, S>, state: &mut St) -> Result<Self::IntoEq, KernelError> {
        let res = self.zip(lhs).map_err(|_| KernelError::ShapeMismatch)?;
        res.try_map_children(|(map, tm)| map.into_eq(tm, state))?
            .try_map_import(|(map, tm)| map.into_eq(tm, state))?
            .try_map_closures(|(map, tm)| {
                map.assert_into_defeq()?;
                map.into_eq(tm, state)
            })
    }
}

impl<K, M, C, I, E, St, D> MapIntoEqSealed<C, Tm1<K, I>, E, St, D> for Tm1<K, M>
where
    M: MapIntoEq<C, I, E, St, D>,
    K: Kind<1>,
{
}

impl<K, M, C, I, E, St, D> MapIntoEq<C, Tm1<K, I>, E, St, D> for Tm1<K, M>
where
    C: Ctx<D>,
    M: MapIntoEq<C, I, E, St, D>,
    K: Kind<1>,
{
    type IntoEq = Tm1<K, M::IntoEq>;

    fn into_eq(self, lhs: Tm1<K, I>, state: &mut St) -> Result<Self::IntoEq, E> {
        Ok(Tm1(lhs.0, self.1.into_eq(lhs.1, state)?))
    }
}

impl<K, M, C, CN, T, I, S, E, St, D> MapIntoEqSealed<C, Node<CN, T, I, S>, E, St, D> for Tm1<K, M>
where
    M: MapIntoEq<C, T, E, St, D>,
    CN: Ctx<D>,
    T: LocalTerm<C, D>,
    I: LocalTerm<C, D>,
    S: LocalTerm<C, D>,
    K: Kind<1>,
{
}

impl<K, M, C, CN, T, I, S, St, D> MapIntoEq<C, Node<CN, T, I, S>, KernelError, St, D> for Tm1<K, M>
where
    C: Ctx<D>,
    M: MapIntoEq<C, T, KernelError, St, D>,
    CN: Ctx<D>,
    T: LocalTerm<C, D>,
    I: LocalTerm<C, D>,
    S: LocalTerm<C, D>,
    K: Kind<1>,
    Node<CN, T, I, S>: TryInto<Tm1<K, T>>,
{
    type IntoEq = Tm1<K, M::IntoEq>;

    fn into_eq(self, lhs: Node<CN, T, I, S>, state: &mut St) -> Result<Self::IntoEq, KernelError> {
        self.into_eq(
            lhs.try_into().map_err(|_| KernelError::ShapeMismatch)?,
            state,
        )
    }
}

impl<K, ML, MR, C, IL, IR, E, St, D> MapIntoEqSealed<C, Tm2<K, IL, IR>, E, St, D> for Tm2<K, ML, MR>
where
    ML: MapIntoEq<C, IL, E, St, D>,
    MR: MapIntoEq<C, IR, E, St, D>,
    K: Kind<2>,
{
}

impl<K, ML, MR, C, IL, IR, E, St, D> MapIntoEq<C, Tm2<K, IL, IR>, E, St, D> for Tm2<K, ML, MR>
where
    C: Ctx<D>,
    ML: MapIntoEq<C, IL, E, St, D>,
    MR: MapIntoEq<C, IR, E, St, D>,
    K: Kind<2>,
{
    type IntoEq = Tm2<K, ML::IntoEq, MR::IntoEq>;

    fn into_eq(self, lhs: Tm2<K, IL, IR>, state: &mut St) -> Result<Self::IntoEq, E> {
        Ok(Tm2(
            lhs.0,
            self.1.into_eq(lhs.1, state)?,
            self.2.into_eq(lhs.2, state)?,
        ))
    }
}

impl<K, ML, MR, C, CN, T, I, S, E, St, D> MapIntoEqSealed<C, Node<CN, T, I, S>, E, St, D>
    for Tm2<K, ML, MR>
where
    ML: MapIntoEq<C, T, E, St, D>,
    MR: MapIntoEq<C, T, E, St, D>,
    CN: Ctx<D>,
    T: LocalTerm<C, D>,
    I: LocalTerm<C, D>,
    S: LocalTerm<C, D>,
    K: Kind<2>,
{
}

impl<K, ML, MR, C, CN, T, I, S, St, D> MapIntoEq<C, Node<CN, T, I, S>, KernelError, St, D>
    for Tm2<K, ML, MR>
where
    C: Ctx<D>,
    ML: MapIntoEq<C, T, KernelError, St, D>,
    MR: MapIntoEq<C, T, KernelError, St, D>,
    CN: Ctx<D> + PartialEq,
    T: LocalTerm<C, D>,
    I: LocalTerm<C, D>,
    S: LocalTerm<C, D>,
    K: Kind<2>,
    Node<CN, T, I, S>: TryInto<Tm2<K, T, T>>,
{
    type IntoEq = Tm2<K, ML::IntoEq, MR::IntoEq>;

    fn into_eq(self, lhs: Node<CN, T, I, S>, state: &mut St) -> Result<Self::IntoEq, KernelError> {
        self.into_eq(
            lhs.try_into().map_err(|_| KernelError::ShapeMismatch)?,
            state,
        )
    }
}

impl<K, ML, MM, MR, C, IL, IM, IR, E, St, D> MapIntoEqSealed<C, Tm3<K, IL, IM, IR>, E, St, D>
    for Tm3<K, ML, MM, MR>
where
    ML: MapIntoEq<C, IL, E, St, D>,
    MM: MapIntoEq<C, IM, E, St, D>,
    MR: MapIntoEq<C, IR, E, St, D>,
    K: Kind<3>,
{
}

impl<K, ML, MM, MR, C, IL, IM, IR, E, St, D> MapIntoEq<C, Tm3<K, IL, IM, IR>, E, St, D>
    for Tm3<K, ML, MM, MR>
where
    C: Ctx<D>,
    ML: MapIntoEq<C, IL, E, St, D>,
    MM: MapIntoEq<C, IM, E, St, D>,
    MR: MapIntoEq<C, IR, E, St, D>,
    K: Kind<3>,
{
    type IntoEq = Tm3<K, ML::IntoEq, MM::IntoEq, MR::IntoEq>;

    fn into_eq(self, lhs: Tm3<K, IL, IM, IR>, state: &mut St) -> Result<Self::IntoEq, E> {
        Ok(Tm3(
            lhs.0,
            self.1.into_eq(lhs.1, state)?,
            self.2.into_eq(lhs.2, state)?,
            self.3.into_eq(lhs.3, state)?,
        ))
    }
}

impl<K, ML, MM, MR, C, CN, T, I, S, E, St, D> MapIntoEqSealed<C, Node<CN, T, I, S>, E, St, D>
    for Tm3<K, ML, MM, MR>
where
    ML: MapIntoEq<C, T, E, St, D>,
    MM: MapIntoEq<C, T, E, St, D>,
    MR: MapIntoEq<C, T, E, St, D>,
    CN: Ctx<D>,
    T: LocalTerm<C, D>,
    I: LocalTerm<C, D>,
    S: LocalTerm<C, D>,
    K: Kind<3>,
{
}

impl<K, ML, MM, MR, C, CN, T, I, S, St, D> MapIntoEq<C, Node<CN, T, I, S>, KernelError, St, D>
    for Tm3<K, ML, MM, MR>
where
    C: Ctx<D>,
    ML: MapIntoEq<C, T, KernelError, St, D>,
    MM: MapIntoEq<C, T, KernelError, St, D>,
    MR: MapIntoEq<C, T, KernelError, St, D>,
    CN: Ctx<D> + PartialEq,
    T: LocalTerm<C, D>,
    I: LocalTerm<C, D>,
    S: LocalTerm<C, D>,
    K: Kind<3>,
    Node<CN, T, I, S>: TryInto<Tm3<K, T, T, T>>,
{
    type IntoEq = Tm3<K, ML::IntoEq, MM::IntoEq, MR::IntoEq>;

    fn into_eq(self, lhs: Node<CN, T, I, S>, state: &mut St) -> Result<Self::IntoEq, KernelError> {
        self.into_eq(
            lhs.try_into().map_err(|_| KernelError::ShapeMismatch)?,
            state,
        )
    }
}

impl<T, U, C, I, E, St, D> MapIntoEqSealed<C, I, E, St, D> for (T, U)
where
    T: MapIntoEq<C, I, E, St, D>,
    U: MapIntoEq<C, T::IntoEq, E, St, D>,
{
}

impl<T, U, C, I, E, St, D> MapIntoEq<C, I, E, St, D> for (T, U)
where
    T: MapIntoEq<C, I, E, St, D>,
    U: MapIntoEq<C, T::IntoEq, E, St, D>,
{
    type IntoEq = U::IntoEq;

    fn into_eq(self, lhs: I, state: &mut St) -> Result<Self::IntoEq, E> {
        let mid = self.0.into_eq(lhs, state)?;
        self.1.into_eq(mid, state)
    }
}

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
