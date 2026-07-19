//! Explicit effect requests and resumptions for Lisp-family machines.
//!
//! Pure reduction may suspend with a request, but it never performs host I/O
//! or mutates host state. Handlers are separate capabilities, and their
//! request/response transcripts remain plain data until a proof backend
//! supplies an appropriate replay theorem.
//!
//! @covalence-api {"id":"A0025","title":"Lisp effect suspension and handling","status":"experimental","dependsOn":["A0022","A0023"]}

/// A representation-independent effect request.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EffectRequest<O, I> {
    pub operation: O,
    pub input: I,
}

/// A machine continuation waiting for an effect response.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EffectSuspension<C, Q> {
    pub continuation: C,
    pub request: Q,
}

/// Observable state of an effectful machine.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EffectState<C, Q> {
    Running(C),
    Suspended(EffectSuspension<C, Q>),
    Returned(C),
}

/// One handled request retained as auditable, serializable data.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HandledEffect<Q, R> {
    pub request: Q,
    pub response: R,
}

/// WIT-shaped request construction.
pub trait EffectSyntax {
    type Operation: Clone;
    type Input: Clone;
    type Request: Clone;
    type Error;

    fn request(
        &self,
        operation: Self::Operation,
        input: Self::Input,
    ) -> Result<Self::Request, Self::Error>;
}

/// Language semantics for validating a response and resuming a continuation.
pub trait EffectResume {
    type Configuration: Clone;
    type Request: Clone;
    type Response: Clone;
    type Error;

    fn resume(
        &self,
        suspension: EffectSuspension<Self::Configuration, Self::Request>,
        response: Self::Response,
    ) -> Result<Self::Configuration, Self::Error>;
}

/// Proof-free external effect handler.
///
/// Implementations may perform I/O or mutate host state. Consequently this
/// capability carries no theorem authority.
pub trait EffectHandler<Q, R> {
    type Error;

    fn handle(&mut self, request: &Q) -> Result<R, Self::Error>;
}

/// Optional proof-producing validation of a handled effect.
pub trait EffectReplay<Q, R> {
    type Evidence;
    type Error;

    fn replay(&self, handled: &HandledEffect<Q, R>) -> Result<Self::Evidence, Self::Error>;
}
