//! Shared, proof-free Lisp I/O request vocabulary.
//!
//! Concrete languages choose how these requests enter their reduction
//! semantics. This module only fixes the WIT-shaped boundary between a
//! suspended evaluator and an external host.

use crate::EffectHandler;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LispIoRequest<V> {
    Read,
    Write(V),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LispIoResponse<V> {
    Value(V),
    Unit,
}

/// Host capability used by the generic proof-free adapter.
pub trait LispIo<V> {
    type Error;

    fn read(&mut self) -> Result<V, Self::Error>;
    fn write(&mut self, value: &V) -> Result<(), Self::Error>;
}

/// Adapt a host I/O capability to the generic effect-handler boundary.
pub struct LispIoHandler<H> {
    pub host: H,
}

impl<H, V> EffectHandler<LispIoRequest<V>, LispIoResponse<V>> for LispIoHandler<H>
where
    H: LispIo<V>,
{
    type Error = H::Error;

    fn handle(&mut self, request: &LispIoRequest<V>) -> Result<LispIoResponse<V>, Self::Error> {
        match request {
            LispIoRequest::Read => self.host.read().map(LispIoResponse::Value),
            LispIoRequest::Write(value) => {
                self.host.write(value)?;
                Ok(LispIoResponse::Unit)
            }
        }
    }
}
