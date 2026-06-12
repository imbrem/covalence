pub mod build;
mod validate;
pub use validate::{compile_wat, wasm_to_wat};

/// Length of the WASM preamble (magic word + version), shared between
/// modules and components.
pub const PREAMBLE_LEN: usize = 8;

/// Returns `true` if `bytes` start with the `\0asm` magic word and are
/// long enough to carry a full preamble. Says nothing about whether the
/// remainder is well-formed.
#[inline]
pub fn looks_like_wasm(bytes: &[u8]) -> bool {
    bytes.len() >= PREAMBLE_LEN && bytes[..4] == [0x00, 0x61, 0x73, 0x6d]
}

/// Returns `true` if `bytes` look like a WASM core module — i.e. the
/// preamble version word starts with `0x01`. Distinguishing modules
/// from components by the version byte is the same trick the JS host
/// uses; cheaper than a full parse.
#[inline]
pub fn is_module(bytes: &[u8]) -> bool {
    looks_like_wasm(bytes) && bytes[4] == 0x01
}

/// Returns `true` if `bytes` look like a WASM component — i.e. the
/// preamble version word starts with `0x0d`. The complementary check
/// to [`is_module`].
#[inline]
pub fn is_component(bytes: &[u8]) -> bool {
    looks_like_wasm(bytes) && bytes[4] == 0x0d
}

pub mod parse;
pub use parse::{ComponentInfo, ModuleInfo, parse_component, parse_module};

pub mod component;
pub use component::{encode_core_as_component, encode_core_as_component_for};

pub mod custom;
pub use custom::{append_custom_section, find_custom_section};

pub mod val;
pub use val::{ResourceType, Val, ValType};

/// Errors from WAT compilation, WASM decompilation, and binary parsing.
#[derive(Debug, thiserror::Error)]
pub enum WasmError {
    #[error("WAT compile error: {0}")]
    Wat(String),
    #[error("WASM decompile error: {0}")]
    Decompile(String),
    #[error("invalid module: {0}")]
    InvalidModule(String),
    #[error("invalid component: {0}")]
    InvalidComponent(String),
    #[error("WIT error: {0}")]
    Wit(String),
    #[error("component encode error: {0}")]
    Encode(String),
}

#[cfg(feature = "runtime")]
pub mod engine;

// `pure` exposed Thm Pure-meta rules (imp_intro / imp_elim / all_intro /
// all_elim / sym / cong_app / cong_abs / eta_conv) through the WIT
// component-model API. Those rules are deleted in the Pure→HOL
// collapse migration; the module needs to be re-derived against the
// HOL-Light rule set (refl/trans/mk_comb/abs/beta_conv/assume/eq_mp/
// deduct_antisym/inst). Gated for now.
// #[cfg(feature = "runtime")]
// pub mod pure;

#[cfg(feature = "runtime")]
pub mod runtime;
