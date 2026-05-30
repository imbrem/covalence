pub mod build;
mod validate;
pub use validate::{compile_wat, wasm_to_wat};

pub mod parse;
pub use parse::{ComponentInfo, ModuleInfo, parse_component, parse_module};

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
}

#[cfg(feature = "runtime")]
pub mod engine;
