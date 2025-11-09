use crate::{
    Theorem,
    data::term::{Node, Node2},
    fact::{
        HasTy, Is, IsTy, IsWf, Seq, Ty, Wf,
        quant::{Forall, Quantified},
    },
};

impl<C, T> Seq<C, Quantified<Forall<T>, IsWf<T>>> {
    pub fn abs_wf(self) -> Seq<C, IsWf<Node<C, T>>> {
        Seq {
            ctx: self.ctx,
            stmt: Is(Wf, Node::Abs([self.stmt.binder.0, self.stmt.body.1])),
        }
    }
}

impl<C, T> Theorem<Seq<C, Quantified<Forall<T>, IsWf<T>>>> {
    pub fn abs_wf(self) -> Theorem<Seq<C, IsWf<Node<C, T>>>> {
        Theorem {
            stmt: self.stmt.abs_wf(),
            id: self.id,
        }
    }
}

impl<C, T> Seq<C, Quantified<Forall<T>, IsTy<T>>> {
    pub fn pi_ty(self) -> Seq<C, IsTy<Node<C, T>>> {
        Seq {
            ctx: self.ctx,
            stmt: Is(Ty, Node::Pi([self.stmt.binder.0, self.stmt.body.1])),
        }
    }

    pub fn sigma_ty(self) -> Seq<C, IsTy<Node<C, T>>> {
        Seq {
            ctx: self.ctx,
            stmt: Is(Ty, Node::Sigma([self.stmt.binder.0, self.stmt.body.1])),
        }
    }
}

impl<C, T> Theorem<Seq<C, Quantified<Forall<T>, IsTy<T>>>> {
    pub fn pi_ty(self) -> Theorem<Seq<C, IsTy<Node<C, T>>>> {
        Theorem {
            stmt: self.stmt.pi_ty(),
            id: self.id,
        }
    }

    pub fn sigma_ty(self) -> Theorem<Seq<C, IsTy<Node<C, T>>>> {
        Theorem {
            stmt: self.stmt.sigma_ty(),
            id: self.id,
        }
    }
}

impl<C, T> Seq<C, Quantified<Forall<T>, HasTy<T>>> {
    pub fn abs_has_ty(self) -> Seq<C, HasTy<Node<C, T>>>
    where
        T: Clone,
    {
        Seq {
            ctx: self.ctx,
            stmt: HasTy {
                tm: Node::Abs([self.stmt.binder.0.clone(), self.stmt.body.tm]),
                ty: Node::Pi([self.stmt.binder.0, self.stmt.body.ty]),
            },
        }
    }

    pub fn abs_has_ty_wf<I>(self) -> Seq<C, IsWf<Node2<C, T, I>>> {
        Seq {
            ctx: self.ctx,
            stmt: Is(
                Wf,
                Node2::Abs([
                    Node::Id([self.stmt.binder.0]),
                    Node::HasTy([self.stmt.body.tm, self.stmt.body.ty]),
                ]),
            ),
        }
    }
}

impl<C, T> Theorem<Seq<C, Quantified<Forall<T>, HasTy<T>>>> {
    pub fn abs_has_ty(self) -> Theorem<Seq<C, HasTy<Node<C, T>>>>
    where
        T: Clone,
    {
        Theorem {
            stmt: self.stmt.abs_has_ty(),
            id: self.id,
        }
    }

    pub fn abs_has_ty_wf<I>(self) -> Theorem<Seq<C, IsWf<Node2<C, T, I>>>> {
        Theorem {
            stmt: self.stmt.abs_has_ty_wf(),
            id: self.id,
        }
    }
}
