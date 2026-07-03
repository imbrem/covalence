//! Concrete LLM backends.
//!
//! End users should usually construct [`Llm`](crate::Llm) / [`AsyncLlm`](crate::AsyncLlm)
//! via their provider-specific constructors (`Llm::ollama`, `Llm::groq`, …)
//! rather than instantiating a backend directly. Backends are exposed for
//! advanced use (custom transport, testing, plugging in providers we don't
//! yet wrap).

#[cfg(feature = "openai")]
pub mod openai;
