//! Python bindings for `covalence-llm` (feature `llm`).
//!
//! `Llm` is the user-facing base class; provider-specific subclasses
//! (`Ollama`, `OpenAI`, `Groq`, `Cerebras`, `DeepSeek`) are thin
//! constructor-only wrappers that build an `Llm` with the right backend +
//! base URL + auth.
//!
//! The blocking `chat` / `complete` calls release the GIL so callers can
//! wrap them with `asyncio.to_thread` until a native asyncio integration
//! lands.

use pyo3::prelude::*;

use covalence_llm::{
    ChatMessage, ChatOptions, ChatRequest, ChatResponse, FinishReason, Llm, LlmError, Role,
    TokenUsage,
    backend::openai::{
        CEREBRAS_BASE_URL, DEEPSEEK_BASE_URL, GROQ_BASE_URL, OLLAMA_BASE_URL, OPENAI_BASE_URL,
    },
};

fn role_to_str(role: Role) -> &'static str {
    match role {
        Role::System => "system",
        Role::User => "user",
        Role::Assistant => "assistant",
        Role::Tool => "tool",
    }
}

fn parse_role(s: &str) -> PyResult<Role> {
    match s {
        "system" => Ok(Role::System),
        "user" => Ok(Role::User),
        "assistant" => Ok(Role::Assistant),
        "tool" => Ok(Role::Tool),
        other => Err(pyo3::exceptions::PyValueError::new_err(format!(
            "unknown role: {other}"
        ))),
    }
}

fn finish_to_str(f: FinishReason) -> &'static str {
    match f {
        FinishReason::Stop => "stop",
        FinishReason::Length => "length",
        FinishReason::Other => "other",
    }
}

fn map_err(e: LlmError) -> PyErr {
    match e {
        LlmError::Transport(s) => pyo3::exceptions::PyConnectionError::new_err(s),
        LlmError::Decode(s) => pyo3::exceptions::PyValueError::new_err(s),
        LlmError::Backend { status, message } => pyo3::exceptions::PyRuntimeError::new_err(
            format!("backend error ({status}): {message}"),
        ),
    }
}

// ── Types ────────────────────────────────────────────────────────────────────

#[pyclass(name = "ChatMessage", from_py_object)]
#[derive(Clone)]
pub struct PyChatMessage(ChatMessage);

#[pymethods]
impl PyChatMessage {
    #[new]
    fn new(role: &str, content: String) -> PyResult<Self> {
        Ok(Self(ChatMessage { role: parse_role(role)?, content }))
    }

    #[staticmethod]
    fn system(content: String) -> Self {
        Self(ChatMessage::system(content))
    }
    #[staticmethod]
    fn user(content: String) -> Self {
        Self(ChatMessage::user(content))
    }
    #[staticmethod]
    fn assistant(content: String) -> Self {
        Self(ChatMessage::assistant(content))
    }

    #[getter]
    fn role(&self) -> &'static str {
        role_to_str(self.0.role)
    }
    #[getter]
    fn content(&self) -> &str {
        &self.0.content
    }

    fn __repr__(&self) -> String {
        format!("ChatMessage(role={:?}, content={:?})", role_to_str(self.0.role), self.0.content)
    }
}

#[pyclass(name = "ChatOptions", from_py_object)]
#[derive(Clone, Default)]
pub struct PyChatOptions(ChatOptions);

#[pymethods]
impl PyChatOptions {
    #[new]
    #[pyo3(signature = (
        temperature=None, top_p=None, max_tokens=None, seed=None, stop=None,
    ))]
    fn new(
        temperature: Option<f32>,
        top_p: Option<f32>,
        max_tokens: Option<u32>,
        seed: Option<u64>,
        stop: Option<Vec<String>>,
    ) -> Self {
        Self(ChatOptions {
            temperature,
            top_p,
            max_tokens,
            seed,
            stop: stop.unwrap_or_default(),
        })
    }

    #[getter]
    fn temperature(&self) -> Option<f32> {
        self.0.temperature
    }
    #[getter]
    fn top_p(&self) -> Option<f32> {
        self.0.top_p
    }
    #[getter]
    fn max_tokens(&self) -> Option<u32> {
        self.0.max_tokens
    }
    #[getter]
    fn seed(&self) -> Option<u64> {
        self.0.seed
    }
    #[getter]
    fn stop(&self) -> Vec<String> {
        self.0.stop.clone()
    }
}

#[pyclass(name = "ChatRequest", skip_from_py_object)]
#[derive(Clone)]
pub struct PyChatRequest(ChatRequest);

#[pymethods]
impl PyChatRequest {
    #[new]
    #[pyo3(signature = (model, messages, options=None))]
    fn new(
        model: String,
        messages: Vec<PyChatMessage>,
        options: Option<PyChatOptions>,
    ) -> Self {
        Self(ChatRequest {
            model,
            messages: messages.into_iter().map(|m| m.0).collect(),
            options: options.map(|o| o.0).unwrap_or_default(),
        })
    }

    #[getter]
    fn model(&self) -> &str {
        &self.0.model
    }
    #[getter]
    fn messages(&self) -> Vec<PyChatMessage> {
        self.0.messages.iter().cloned().map(PyChatMessage).collect()
    }
    #[getter]
    fn options(&self) -> PyChatOptions {
        PyChatOptions(self.0.options.clone())
    }
}

#[pyclass(name = "TokenUsage", skip_from_py_object)]
#[derive(Clone)]
pub struct PyTokenUsage(TokenUsage);

#[pymethods]
impl PyTokenUsage {
    #[getter]
    fn prompt_tokens(&self) -> Option<u32> {
        self.0.prompt_tokens
    }
    #[getter]
    fn completion_tokens(&self) -> Option<u32> {
        self.0.completion_tokens
    }
}

#[pyclass(name = "ChatResponse", skip_from_py_object)]
#[derive(Clone)]
pub struct PyChatResponse(ChatResponse);

#[pymethods]
impl PyChatResponse {
    #[getter]
    fn message(&self) -> PyChatMessage {
        PyChatMessage(self.0.message.clone())
    }
    #[getter]
    fn content(&self) -> &str {
        &self.0.message.content
    }
    #[getter]
    fn role(&self) -> &'static str {
        role_to_str(self.0.message.role)
    }
    #[getter]
    fn finish_reason(&self) -> &'static str {
        finish_to_str(self.0.finish_reason)
    }
    #[getter]
    fn usage(&self) -> PyTokenUsage {
        PyTokenUsage(self.0.usage.clone())
    }

    fn __repr__(&self) -> String {
        format!(
            "ChatResponse(role={:?}, content={:?}, finish_reason={:?})",
            role_to_str(self.0.message.role),
            self.0.message.content,
            finish_to_str(self.0.finish_reason),
        )
    }
}

// ── Llm base + provider subclasses ──────────────────────────────────────────

/// High-level chat client. Subclasses (`Ollama`, `OpenAI`, `Groq`, …) are
/// constructor-only wrappers; the methods live here on the base class.
#[pyclass(name = "Llm", subclass)]
pub struct PyLlm {
    inner: Llm,
}

#[pymethods]
impl PyLlm {
    /// Configured default model name.
    #[getter]
    fn model(&self) -> &str {
        self.inner.model()
    }
    /// Configured default options.
    #[getter]
    fn options(&self) -> PyChatOptions {
        PyChatOptions(self.inner.options().clone())
    }

    /// Multi-message chat. `messages` may be a list of `ChatMessage` or
    /// `(role, content)` tuples.
    fn chat(&self, py: Python<'_>, messages: Vec<PyChatMessage>) -> PyResult<PyChatResponse> {
        let msgs: Vec<ChatMessage> = messages.into_iter().map(|m| m.0).collect();
        let resp = py.detach(|| self.inner.chat(msgs)).map_err(map_err)?;
        Ok(PyChatResponse(resp))
    }

    /// Single-turn convenience: send `prompt` as a user message, return the
    /// assistant's text content.
    fn complete(&self, py: Python<'_>, prompt: String) -> PyResult<String> {
        py.detach(|| self.inner.complete(prompt)).map_err(map_err)
    }

    /// Issue a fully-specified request (bypasses default model + options).
    fn chat_request(&self, py: Python<'_>, req: &PyChatRequest) -> PyResult<PyChatResponse> {
        let resp = py.detach(|| self.inner.chat_request(&req.0)).map_err(map_err)?;
        Ok(PyChatResponse(resp))
    }
}

/// Local Ollama via its OpenAI-compatible `/v1` endpoint.
#[pyclass(name = "Ollama", extends = PyLlm)]
pub struct PyOllama;

#[pymethods]
impl PyOllama {
    #[new]
    #[pyo3(signature = (model, base_url=None))]
    fn new(model: String, base_url: Option<String>) -> (Self, PyLlm) {
        let llm = Llm::ollama_at(base_url.unwrap_or_else(|| OLLAMA_BASE_URL.to_string()), model);
        (Self, PyLlm { inner: llm })
    }
}

/// OpenAI (api.openai.com).
#[pyclass(name = "OpenAI", extends = PyLlm)]
pub struct PyOpenAI;

#[pymethods]
impl PyOpenAI {
    #[new]
    fn new(api_key: String, model: String) -> (Self, PyLlm) {
        let llm = Llm::openai(api_key, model);
        (Self, PyLlm { inner: llm })
    }
}

/// Groq via OpenAI-compatible endpoint.
#[pyclass(name = "Groq", extends = PyLlm)]
pub struct PyGroq;

#[pymethods]
impl PyGroq {
    #[new]
    fn new(api_key: String, model: String) -> (Self, PyLlm) {
        let llm = Llm::groq(api_key, model);
        (Self, PyLlm { inner: llm })
    }
}

/// Cerebras via OpenAI-compatible endpoint.
#[pyclass(name = "Cerebras", extends = PyLlm)]
pub struct PyCerebras;

#[pymethods]
impl PyCerebras {
    #[new]
    fn new(api_key: String, model: String) -> (Self, PyLlm) {
        let llm = Llm::cerebras(api_key, model);
        (Self, PyLlm { inner: llm })
    }
}

/// DeepSeek via OpenAI-compatible endpoint.
#[pyclass(name = "DeepSeek", extends = PyLlm)]
pub struct PyDeepSeek;

#[pymethods]
impl PyDeepSeek {
    #[new]
    fn new(api_key: String, model: String) -> (Self, PyLlm) {
        let llm = Llm::deepseek(api_key, model);
        (Self, PyLlm { inner: llm })
    }
}

/// Generic OpenAI-compatible endpoint at a custom base URL.
#[pyclass(name = "OpenAICompat", extends = PyLlm)]
pub struct PyOpenAICompat;

#[pymethods]
impl PyOpenAICompat {
    #[new]
    #[pyo3(signature = (base_url, model, api_key=None))]
    fn new(base_url: String, model: String, api_key: Option<String>) -> (Self, PyLlm) {
        let llm = Llm::openai_compat(base_url, api_key, model);
        (Self, PyLlm { inner: llm })
    }
}

pub fn register(m: &Bound<'_, PyModule>) -> PyResult<()> {
    m.add_class::<PyChatMessage>()?;
    m.add_class::<PyChatOptions>()?;
    m.add_class::<PyChatRequest>()?;
    m.add_class::<PyChatResponse>()?;
    m.add_class::<PyTokenUsage>()?;
    m.add_class::<PyLlm>()?;
    m.add_class::<PyOllama>()?;
    m.add_class::<PyOpenAI>()?;
    m.add_class::<PyGroq>()?;
    m.add_class::<PyCerebras>()?;
    m.add_class::<PyDeepSeek>()?;
    m.add_class::<PyOpenAICompat>()?;
    // Expose the well-known base URLs as module attributes for convenience.
    m.add("OPENAI_BASE_URL", OPENAI_BASE_URL)?;
    m.add("GROQ_BASE_URL", GROQ_BASE_URL)?;
    m.add("CEREBRAS_BASE_URL", CEREBRAS_BASE_URL)?;
    m.add("DEEPSEEK_BASE_URL", DEEPSEEK_BASE_URL)?;
    m.add("OLLAMA_BASE_URL", OLLAMA_BASE_URL)?;
    Ok(())
}
