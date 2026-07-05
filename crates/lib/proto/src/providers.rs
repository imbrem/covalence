//! Known LLM providers — env-var names, default base URLs, and resolution.
//!
//! Hand a [`Provider`] to [`Provider::resolve_api_key`] / [`Provider::resolve_base_url`]
//! to read the key and endpoint from the environment using the
//! [`secrets`] module's `COV_<VAR>` → `<VAR>` override chain.

use crate::secrets::{self, SecretError, SecretString};

/// Canonical SDK env-var names. Exposed for callers that want to build a
/// custom resolution chain or report which env var was checked.
pub mod env {
    // API keys.
    pub const OPENAI_API_KEY: &str = "OPENAI_API_KEY";
    pub const ANTHROPIC_API_KEY: &str = "ANTHROPIC_API_KEY";
    pub const GROQ_API_KEY: &str = "GROQ_API_KEY";
    pub const CEREBRAS_API_KEY: &str = "CEREBRAS_API_KEY";
    pub const DEEPSEEK_API_KEY: &str = "DEEPSEEK_API_KEY";

    // Base URL overrides (`COV_<VAR>` takes precedence; see secrets module).
    pub const OPENAI_BASE_URL: &str = "OPENAI_BASE_URL";
    pub const ANTHROPIC_BASE_URL: &str = "ANTHROPIC_BASE_URL";
    pub const GROQ_BASE_URL: &str = "GROQ_BASE_URL";
    pub const CEREBRAS_BASE_URL: &str = "CEREBRAS_BASE_URL";
    pub const DEEPSEEK_BASE_URL: &str = "DEEPSEEK_BASE_URL";
    pub const OLLAMA_BASE_URL: &str = "OLLAMA_BASE_URL";
}

/// Hardcoded default base URLs. Each can be overridden by the matching env
/// var (see [`Provider::resolve_base_url`]).
pub mod default_url {
    pub const OPENAI: &str = "https://api.openai.com/v1";
    pub const ANTHROPIC: &str = "https://api.anthropic.com";
    pub const GROQ: &str = "https://api.groq.com/openai/v1";
    pub const CEREBRAS: &str = "https://api.cerebras.ai/v1";
    pub const DEEPSEEK: &str = "https://api.deepseek.com/v1";
    pub const OLLAMA: &str = "http://localhost:11434/v1";
}

/// Known LLM providers wrapped by `covalence-llm`.
///
/// `Ollama` is included even though it doesn't take an API key — it still
/// benefits from the `OLLAMA_BASE_URL` override (e.g. for a remote ollama
/// instance on the network).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Provider {
    OpenAI,
    Anthropic,
    Groq,
    Cerebras,
    DeepSeek,
    Ollama,
}

impl Provider {
    /// Stable short name (`"openai"`, `"groq"`, …). Suitable for config
    /// files, CLI flags, error messages.
    pub fn name(self) -> &'static str {
        match self {
            Provider::OpenAI => "openai",
            Provider::Anthropic => "anthropic",
            Provider::Groq => "groq",
            Provider::Cerebras => "cerebras",
            Provider::DeepSeek => "deepseek",
            Provider::Ollama => "ollama",
        }
    }

    /// SDK env-var name for the API key, or `None` for providers that don't
    /// take one (Ollama).
    pub fn api_key_env_var(self) -> Option<&'static str> {
        match self {
            Provider::OpenAI => Some(env::OPENAI_API_KEY),
            Provider::Anthropic => Some(env::ANTHROPIC_API_KEY),
            Provider::Groq => Some(env::GROQ_API_KEY),
            Provider::Cerebras => Some(env::CEREBRAS_API_KEY),
            Provider::DeepSeek => Some(env::DEEPSEEK_API_KEY),
            Provider::Ollama => None,
        }
    }

    /// SDK env-var name for the base URL override.
    pub fn base_url_env_var(self) -> &'static str {
        match self {
            Provider::OpenAI => env::OPENAI_BASE_URL,
            Provider::Anthropic => env::ANTHROPIC_BASE_URL,
            Provider::Groq => env::GROQ_BASE_URL,
            Provider::Cerebras => env::CEREBRAS_BASE_URL,
            Provider::DeepSeek => env::DEEPSEEK_BASE_URL,
            Provider::Ollama => env::OLLAMA_BASE_URL,
        }
    }

    /// Hardcoded default base URL.
    pub fn default_base_url(self) -> &'static str {
        match self {
            Provider::OpenAI => default_url::OPENAI,
            Provider::Anthropic => default_url::ANTHROPIC,
            Provider::Groq => default_url::GROQ,
            Provider::Cerebras => default_url::CEREBRAS,
            Provider::DeepSeek => default_url::DEEPSEEK,
            Provider::Ollama => default_url::OLLAMA,
        }
    }

    /// Resolve this provider's API key from the environment.
    ///
    /// Returns `Ok(None)` for providers that don't take a key (Ollama).
    /// Returns `Err(Missing)` when a key is required but no env var in the
    /// chain is set.
    pub fn resolve_api_key(self) -> Result<Option<SecretString>, SecretError> {
        match self.api_key_env_var() {
            Some(var) => secrets::from_env(var).map(Some),
            None => Ok(None),
        }
    }

    /// Resolve this provider's base URL: env override if set, otherwise the
    /// hardcoded default. Always returns a value.
    pub fn resolve_base_url(self) -> String {
        secrets::endpoint_from_env(self.base_url_env_var())
            .unwrap_or_else(|| self.default_base_url().to_string())
    }
}
