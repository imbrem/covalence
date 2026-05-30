//! OpenTheory stack objects, generic over the kernel type.

use std::fmt;

use covalence_hol::traits::HolLightKernel;
use covalence_hol::types::NameId;

use crate::name::OtName;

/// Objects on the OpenTheory stack.
pub enum OtObject<K: HolLightKernel> {
    Num(i64),
    Name(OtName),
    List(Vec<OtObject<K>>),
    TypeOp(NameId),
    Type(K::Type),
    Const(NameId),
    Var(NameId, K::Type),
    Term(K::Term),
    Thm(K::Thm),
}

// With Copy types, Clone is trivially derived.
impl<K: HolLightKernel> Clone for OtObject<K> {
    fn clone(&self) -> Self {
        match self {
            OtObject::Num(n) => OtObject::Num(*n),
            OtObject::Name(n) => OtObject::Name(n.clone()),
            OtObject::List(l) => OtObject::List(l.clone()),
            OtObject::TypeOp(n) => OtObject::TypeOp(*n),
            OtObject::Type(t) => OtObject::Type(*t),
            OtObject::Const(n) => OtObject::Const(*n),
            OtObject::Var(n, ty) => OtObject::Var(*n, *ty),
            OtObject::Term(t) => OtObject::Term(*t),
            OtObject::Thm(t) => OtObject::Thm(*t),
        }
    }
}

impl<K: HolLightKernel> fmt::Debug for OtObject<K> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            OtObject::Num(n) => write!(f, "Num({n})"),
            OtObject::Name(n) => write!(f, "Name({n:?})"),
            OtObject::List(l) => write!(f, "List({l:?})"),
            OtObject::TypeOp(n) => write!(f, "TypeOp({n})"),
            OtObject::Type(t) => write!(f, "Type({t:?})"),
            OtObject::Const(n) => write!(f, "Const({n})"),
            OtObject::Var(n, ty) => write!(f, "Var({n}, {ty:?})"),
            OtObject::Term(t) => write!(f, "Term({t:?})"),
            OtObject::Thm(t) => write!(f, "Thm({t:?})"),
        }
    }
}

/// Get the type name of an object (for error messages).
pub fn obj_type_name<K: HolLightKernel>(obj: &OtObject<K>) -> String {
    match obj {
        OtObject::Num(_) => "Num".into(),
        OtObject::Name(_) => "Name".into(),
        OtObject::List(_) => "List".into(),
        OtObject::TypeOp(_) => "TypeOp".into(),
        OtObject::Type(_) => "Type".into(),
        OtObject::Const(_) => "Const".into(),
        OtObject::Var(_, _) => "Var".into(),
        OtObject::Term(_) => "Term".into(),
        OtObject::Thm(_) => "Thm".into(),
    }
}
