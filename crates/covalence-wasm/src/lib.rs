pub mod build;
mod validate;
pub use validate::{compile_wat, wasm_to_wat};

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

#[cfg(feature = "runtime")]
pub mod runtime;
