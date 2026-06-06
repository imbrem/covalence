//! High-level chat-completion API for the covalence ecosystem.
//!
//! Most callers want [`Llm`] (blocking) or [`AsyncLlm`] (async): both wrap a
//! [`ChatBackend`] / [`AsyncChatBackend`] plus a default model and option set,
//! and expose ergonomic [`chat`](Llm::chat) / [`complete`](Llm::complete)
//! methods. Provider-specific constructors (`::ollama`, `::openai`, `::groq`,
//! `::cerebras`, `::deepseek`, `::openai_compat`) hide the base-URL + auth
//! quirks of each endpoint.
//!
//! Backends live in [`backend`]. Adding a new provider means implementing
//! [`ChatBackend`] / [`AsyncChatBackend`] there; the [`Llm`] / [`AsyncLlm`]
//! surface stays the same.
//!
//! The WASM-facing surface lives at `wit/llm.wit`; host bindings are not
//! wired up yet.

use std::fmt;

use serde::{Deserialize, Serialize};

pub mod backend;

/// Errors a backend can return.
#[derive(Debug, thiserror::Error)]
pub enum LlmError {
    #[error("transport error: {0}")]
    Transport(String),
    #[error("decode error: {0}")]
    Decode(String),
    #[error("backend error ({status}): {message}")]
    Backend { status: u16, message: String },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum Role {
    System,
    User,
    Assistant,
    Tool,
}

impl fmt::Display for Role {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Role::System => "system",
            Role::User => "user",
            Role::Assistant => "assistant",
            Role::Tool => "tool",
        })
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ChatMessage {
    pub role: Role,
    pub content: String,
}

impl ChatMessage {
    pub fn system(content: impl Into<String>) -> Self {
        Self { role: Role::System, content: content.into() }
    }
    pub fn user(content: impl Into<String>) -> Self {
        Self { role: Role::User, content: content.into() }
    }
    pub fn assistant(content: impl Into<String>) -> Self {
        Self { role: Role::Assistant, content: content.into() }
    }
}

/// Per-request knobs. Backends that don't support a field should ignore it.
#[derive(Debug, Clone, Default)]
pub struct ChatOptions {
    pub temperature: Option<f32>,
    pub top_p: Option<f32>,
    pub max_tokens: Option<u32>,
    pub stop: Vec<String>,
    pub seed: Option<u64>,
}

#[derive(Debug, Clone)]
pub struct ChatRequest {
    pub model: String,
    pub messages: Vec<ChatMessage>,
    pub options: ChatOptions,
}

impl ChatRequest {
    pub fn new(model: impl Into<String>, messages: Vec<ChatMessage>) -> Self {
        Self { model: model.into(), messages, options: ChatOptions::default() }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FinishReason {
    Stop,
    Length,
    Other,
}

#[derive(Debug, Clone, Default)]
pub struct TokenUsage {
    pub prompt_tokens: Option<u32>,
    pub completion_tokens: Option<u32>,
}

#[derive(Debug, Clone)]
pub struct ChatResponse {
    pub message: ChatMessage,
    pub finish_reason: FinishReason,
    pub usage: TokenUsage,
}

/// Blocking chat-completion backend.
#[cfg(feature = "sync")]
pub trait ChatBackend: Send + Sync {
    fn chat(&self, req: &ChatRequest) -> Result<ChatResponse, LlmError>;
}

/// Async chat-completion backend. Object-safe via `async_trait`.
#[cfg(feature = "async")]
#[async_trait::async_trait]
pub trait AsyncChatBackend: Send + Sync {
    async fn chat(&self, req: &ChatRequest) -> Result<ChatResponse, LlmError>;
}

// ── High-level handle ────────────────────────────────────────────────────────

#[cfg(feature = "openai")]
use crate::backend::openai::{
    CEREBRAS_BASE_URL, DEEPSEEK_BASE_URL, GROQ_BASE_URL, OLLAMA_BASE_URL, OPENAI_BASE_URL,
};

/// Blocking high-level chat client.
///
/// Owns a backend plus the defaults applied to each call. Construct via
/// [`Llm::new`] or one of the provider sugar constructors.
#[cfg(feature = "sync")]
pub struct Llm {
    backend: Box<dyn ChatBackend>,
    model: String,
    options: ChatOptions,
}

#[cfg(feature = "sync")]
impl Llm {
    pub fn new(backend: impl ChatBackend + 'static, model: impl Into<String>) -> Self {
        Self {
            backend: Box::new(backend),
            model: model.into(),
            options: ChatOptions::default(),
        }
    }

    /// Replace the default options applied to every call.
    pub fn with_options(mut self, options: ChatOptions) -> Self {
        self.options = options;
        self
    }

    pub fn model(&self) -> &str {
        &self.model
    }
    pub fn options(&self) -> &ChatOptions {
        &self.options
    }

    /// Issue a chat completion using the configured model + default options.
    pub fn chat(&self, messages: Vec<ChatMessage>) -> Result<ChatResponse, LlmError> {
        let req = ChatRequest {
            model: self.model.clone(),
            messages,
            options: self.options.clone(),
        };
        self.backend.chat(&req)
    }

    /// Issue a chat completion with a fully-specified request (bypasses
    /// the configured model / options).
    pub fn chat_request(&self, req: &ChatRequest) -> Result<ChatResponse, LlmError> {
        self.backend.chat(req)
    }

    /// Single-turn convenience: send `prompt` as a user message, return content.
    pub fn complete(&self, prompt: impl Into<String>) -> Result<String, LlmError> {
        let resp = self.chat(vec![ChatMessage::user(prompt)])?;
        Ok(resp.message.content)
    }
}

// Provider sugar constructors (sync).
#[cfg(all(feature = "sync", feature = "openai"))]
impl Llm {
    /// Generic OpenAI-compatible endpoint.
    pub fn openai_compat(
        base_url: impl Into<String>,
        api_key: Option<String>,
        model: impl Into<String>,
    ) -> Self {
        Self::new(backend::openai::OpenAI::new(base_url, api_key), model)
    }

    /// OpenAI (api.openai.com). `api_key` is required.
    pub fn openai(api_key: impl Into<String>, model: impl Into<String>) -> Self {
        Self::openai_compat(OPENAI_BASE_URL, Some(api_key.into()), model)
    }

    /// Groq via OpenAI-compatible endpoint. `api_key` is required.
    pub fn groq(api_key: impl Into<String>, model: impl Into<String>) -> Self {
        Self::openai_compat(GROQ_BASE_URL, Some(api_key.into()), model)
    }

    /// Cerebras via OpenAI-compatible endpoint. `api_key` is required.
    pub fn cerebras(api_key: impl Into<String>, model: impl Into<String>) -> Self {
        Self::openai_compat(CEREBRAS_BASE_URL, Some(api_key.into()), model)
    }

    /// DeepSeek via OpenAI-compatible endpoint. `api_key` is required.
    pub fn deepseek(api_key: impl Into<String>, model: impl Into<String>) -> Self {
        Self::openai_compat(DEEPSEEK_BASE_URL, Some(api_key.into()), model)
    }

    /// Local Ollama via its OpenAI-compatible `/v1` endpoint. No auth.
    pub fn ollama(model: impl Into<String>) -> Self {
        Self::ollama_at(OLLAMA_BASE_URL, model)
    }

    /// Ollama at a non-default base URL.
    pub fn ollama_at(base_url: impl Into<String>, model: impl Into<String>) -> Self {
        Self::openai_compat(base_url, None, model)
    }
}

/// Async high-level chat client. Mirror of [`Llm`].
#[cfg(feature = "async")]
pub struct AsyncLlm {
    backend: std::sync::Arc<dyn AsyncChatBackend>,
    model: String,
    options: ChatOptions,
}

#[cfg(feature = "async")]
impl AsyncLlm {
    pub fn new(backend: impl AsyncChatBackend + 'static, model: impl Into<String>) -> Self {
        Self {
            backend: std::sync::Arc::new(backend),
            model: model.into(),
            options: ChatOptions::default(),
        }
    }

    pub fn with_options(mut self, options: ChatOptions) -> Self {
        self.options = options;
        self
    }

    pub fn model(&self) -> &str {
        &self.model
    }
    pub fn options(&self) -> &ChatOptions {
        &self.options
    }

    pub async fn chat(&self, messages: Vec<ChatMessage>) -> Result<ChatResponse, LlmError> {
        let req = ChatRequest {
            model: self.model.clone(),
            messages,
            options: self.options.clone(),
        };
        self.backend.chat(&req).await
    }

    pub async fn chat_request(&self, req: &ChatRequest) -> Result<ChatResponse, LlmError> {
        self.backend.chat(req).await
    }

    pub async fn complete(&self, prompt: impl Into<String>) -> Result<String, LlmError> {
        let resp = self.chat(vec![ChatMessage::user(prompt)]).await?;
        Ok(resp.message.content)
    }
}

#[cfg(all(feature = "async", feature = "openai"))]
impl AsyncLlm {
    pub fn openai_compat(
        base_url: impl Into<String>,
        api_key: Option<String>,
        model: impl Into<String>,
    ) -> Self {
        Self::new(backend::openai::AsyncOpenAI::new(base_url, api_key), model)
    }
    pub fn openai(api_key: impl Into<String>, model: impl Into<String>) -> Self {
        Self::openai_compat(OPENAI_BASE_URL, Some(api_key.into()), model)
    }
    pub fn groq(api_key: impl Into<String>, model: impl Into<String>) -> Self {
        Self::openai_compat(GROQ_BASE_URL, Some(api_key.into()), model)
    }
    pub fn cerebras(api_key: impl Into<String>, model: impl Into<String>) -> Self {
        Self::openai_compat(CEREBRAS_BASE_URL, Some(api_key.into()), model)
    }
    pub fn deepseek(api_key: impl Into<String>, model: impl Into<String>) -> Self {
        Self::openai_compat(DEEPSEEK_BASE_URL, Some(api_key.into()), model)
    }
    pub fn ollama(model: impl Into<String>) -> Self {
        Self::ollama_at(OLLAMA_BASE_URL, model)
    }
    pub fn ollama_at(base_url: impl Into<String>, model: impl Into<String>) -> Self {
        Self::openai_compat(base_url, None, model)
    }
}
