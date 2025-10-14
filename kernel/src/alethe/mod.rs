use crate::sexpr::*;
use smol_str::SmolStr;

pub struct Ident {
    pub symbol: SmolStr,
    pub indices: Vec<u64>,
}

pub struct Sort {
    pub name: Ident,
    pub params: Vec<Sort>,
}

pub struct Attribute {
    pub key: SmolStr,
    pub value: Option<SExpr>,
}

pub struct QualId {
    pub id: Ident,
    pub sort: Option<Sort>,
}

pub struct VarBinding {
    pub name: SmolStr,
    pub val: Term,
}

pub struct SortedVar {
    pub name: SmolStr,
    pub sort: Sort,
}

pub enum Term {
    App(QualId, Vec<Term>),
    Let(Vec<VarBinding>, Box<Term>),
    Forall(Vec<SortedVar>, Box<Term>),
    Exists(Vec<SortedVar>, Box<Term>),
    Choice(SortedVar, Box<Term>),
    Annot(Box<Term>, Vec<Attribute>),
}

pub enum ProofCommand {}

pub struct Assume {
    pub symbol: SmolStr,
    pub pred: SExpr,
}

pub struct Step {
    pub symbol: SmolStr,
    pub clause: Clause,
    pub rule: SmolStr,
    pub premises: Option<PremisesAnnot>,
    pub context: Option<ContextAnnot>,
    pub attributes: Vec<Attribute>,
}

pub struct Anchor {
    pub step: SmolStr,
    pub args: Option<ArgsAnnot>,
    pub attributes: Vec<Attribute>,
}

pub struct DefineFun {}

pub struct Clause(pub Vec<SExpr>);

pub struct PremisesAnnot(pub Vec<SmolStr>);

pub struct ArgsAnnot(pub Vec<StepArg>);

pub enum StepArg {
    Symbol(SmolStr),
    SymbolProof(SmolStr, SExpr),
}

pub struct ContextAnnot(pub Vec<ContextAssignment>);

pub enum ContextAssignment {
    SortedVar(SmolStr),
    Assign(SmolStr, SExpr),
}
