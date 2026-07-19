//! Capabilities connecting partial Lisp execution to total logical functions.
//!
//! A finite execution trace proves only `MayEval`. Languages such as ACL2 add
//! a separate admission layer establishing termination and uniqueness for all
//! inputs in a logical world. These types make that boundary explicit without
//! granting theorem authority to a syntactic checker.
//!
//! @covalence-api {"id":"A0024","title":"Lisp admission and totalization","status":"experimental","dependsOn":["A0022"]}

/// A frontend-neutral named definition.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Definition<S, E> {
    pub name: S,
    pub parameters: Vec<S>,
    pub body: E,
}

/// One recursive call discovered in a candidate definition.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RecursiveCall<S, E> {
    pub callee: S,
    pub arguments: Vec<E>,
}

/// Plain termination-certificate data.
///
/// `M` describes the measure/order and `W` is the witness format accepted by
/// a replay backend. Possessing this value does not itself prove termination.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TerminationCertificate<M, W> {
    pub measure: M,
    pub witness: W,
}

/// A definition paired with checked candidate certificate data.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AdmittedDefinition<D, C> {
    pub definition: D,
    pub certificate: C,
}

/// Host-side inspection/checking policy.
///
/// This may reject malformed witnesses early, but its result remains plain
/// data until replayed by [`AdmissionReplay`].
pub trait AdmissionPolicy<D> {
    type Certificate;
    type Error;

    fn inspect(&self, definition: &D) -> Result<Self::Certificate, Self::Error>;
}

/// Proof-producing replay of admission evidence.
pub trait AdmissionReplay<D, C> {
    type Evidence;
    type Error;

    fn replay_termination(
        &self,
        definition: &D,
        certificate: &C,
    ) -> Result<Self::Evidence, Self::Error>;
}

/// Evidence that the relational evaluation result exists and is unique.
#[derive(Clone, Debug)]
pub struct ExistenceUniqueness<T> {
    pub existence: T,
    pub uniqueness: T,
}

/// Capability for conservatively introducing a total interpretation only
/// after existence and uniqueness have been established.
pub trait Totalization<D, T> {
    type Constant;
    type Theorem;
    type Error;

    fn define_total(
        &self,
        definition: &D,
        evidence: ExistenceUniqueness<T>,
    ) -> Result<(Self::Constant, Self::Theorem), Self::Error>;
}
