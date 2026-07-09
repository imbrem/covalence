//! # `covalence-pure` — facade over the closed-world equality kernel
//!
//! Re-exports [`covalence_pure_trusted`] (the kernel TCB — the audit target).
//! This facade is where **non-minting** ergonomics live (extension traits,
//! testing helpers, and later the `language!` macro / `covalence-pure-derive`);
//! none of it can reach the private `Eqn::new` constructor, so the trusted
//! surface stays exactly `covalence-pure-trusted`.
//!
//! See [`covalence_pure_trusted`] for the kernel design: [`Expr`] (sealed, with
//! associated sort [`Expr::Ty`]), the certificate [`Eqn`], the [`Language`] /
//! [`Manifest`] trust enumeration, and the base language `()`.

pub use covalence_pure_trusted::*;

pub mod api;
