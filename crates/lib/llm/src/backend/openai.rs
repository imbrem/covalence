//! OpenAI-compatible chat-completion backend.
//!
//! Talks to `POST {base_url}/chat/completions` with the standard
//! `{ model, messages, temperature, … }` payload and parses
//! `choices[0].message`. This shape is supported by OpenAI itself and by
//! several other providers (Groq, Cerebras, DeepSeek, Ollama's `/v1`
//! compatibility endpoint) — see the `Llm::groq` / `Llm::cerebras` /
//! `Llm::deepseek` / `Llm::ollama` constructors for ready-made setups.
//!
//! Streaming and tools are deferred.

use serde::Deserialize;
use serde_json::{Value, json};

use crate::{ChatMessage, ChatRequest, ChatResponse, FinishReason, LlmError, Role, TokenUsage};

// Default base URLs live in `covalence_proto::providers::default_url`. The
// `Llm::openai` / `Llm::groq` / … sugar constructors read them from there.

fn chat_url(base_url: &str) -> String {
    format!("{}/chat/completions", base_url.trim_end_matches('/'))
}

fn build_request_body(req: &ChatRequest) -> Value {
    let messages: Vec<Value> = req
        .messages
        .iter()
        .map(|m| json!({ "role": m.role, "content": m.content }))
        .collect();

    let mut body = json!({
        "model": req.model,
        "messages": messages,
        "stream": false,
    });

    if let Some(t) = req.options.temperature {
        body["temperature"] = json!(t);
    }
    if let Some(t) = req.options.top_p {
        body["top_p"] = json!(t);
    }
    if let Some(n) = req.options.max_tokens {
        body["max_tokens"] = json!(n);
    }
    if let Some(s) = req.options.seed {
        body["seed"] = json!(s);
    }
    if !req.options.stop.is_empty() {
        body["stop"] = json!(req.options.stop);
    }

    body
}

#[derive(Debug, Deserialize)]
struct OpenAIChatResponse {
    choices: Vec<Choice>,
    #[serde(default)]
    usage: Option<Usage>,
}

#[derive(Debug, Deserialize)]
struct Choice {
    message: Message,
    #[serde(default)]
    finish_reason: Option<String>,
}

#[derive(Debug, Deserialize)]
struct Message {
    role: Role,
    #[serde(default)]
    content: Option<String>,
}

#[derive(Debug, Deserialize)]
struct Usage {
    #[serde(default)]
    prompt_tokens: Option<u32>,
    #[serde(default)]
    completion_tokens: Option<u32>,
}

fn map_response(r: OpenAIChatResponse) -> Result<ChatResponse, LlmError> {
    let choice = r
        .choices
        .into_iter()
        .next()
        .ok_or_else(|| LlmError::Decode("response had no choices".into()))?;
    let finish_reason = match choice.finish_reason.as_deref() {
        Some("stop") | None => FinishReason::Stop,
        Some("length") => FinishReason::Length,
        Some(_) => FinishReason::Other,
    };
    let usage = r.usage.unwrap_or(Usage {
        prompt_tokens: None,
        completion_tokens: None,
    });
    Ok(ChatResponse {
        message: ChatMessage {
            role: choice.message.role,
            content: choice.message.content.unwrap_or_default(),
        },
        finish_reason,
        usage: TokenUsage {
            prompt_tokens: usage.prompt_tokens,
            completion_tokens: usage.completion_tokens,
        },
    })
}

// ── Blocking ─────────────────────────────────────────────────────────────────

#[cfg(feature = "sync")]
pub struct OpenAI {
    base_url: String,
    api_key: Option<String>,
    agent: ureq::Agent,
}

#[cfg(feature = "sync")]
impl OpenAI {
    /// Construct against an arbitrary OpenAI-compatible endpoint.
    /// `api_key` may be `None` for endpoints that don't require auth
    /// (e.g. local Ollama).
    pub fn new(base_url: impl Into<String>, api_key: Option<String>) -> Self {
        // Disable ureq's default behaviour of converting 4xx/5xx into
        // `Error::StatusCode`. We want the response back so we can read the
        // body and return `LlmError::Backend { status, message }` instead of
        // `LlmError::Transport`.
        let config = ureq::Agent::config_builder()
            .http_status_as_error(false)
            .build();
        Self {
            base_url: base_url.into(),
            api_key,
            agent: ureq::Agent::new_with_config(config),
        }
    }
}

#[cfg(feature = "sync")]
impl crate::ChatBackend for OpenAI {
    fn chat(&self, req: &ChatRequest) -> Result<ChatResponse, LlmError> {
        let body = build_request_body(req);
        let url = chat_url(&self.base_url);

        let mut request = self.agent.post(&url);
        if let Some(key) = &self.api_key {
            request = request.header("Authorization", format!("Bearer {key}"));
        }

        let mut resp = request
            .send_json(&body)
            .map_err(|e| LlmError::Transport(e.to_string()))?;

        if resp.status().as_u16() >= 400 {
            let status = resp.status().as_u16();
            let message = resp
                .body_mut()
                .read_to_string()
                .unwrap_or_else(|_| "<unreadable body>".into());
            return Err(LlmError::Backend { status, message });
        }

        let parsed: OpenAIChatResponse = resp
            .body_mut()
            .read_json()
            .map_err(|e| LlmError::Decode(e.to_string()))?;

        map_response(parsed)
    }
}

// ── Async ────────────────────────────────────────────────────────────────────

#[cfg(feature = "async")]
pub struct AsyncOpenAI {
    base_url: String,
    api_key: Option<String>,
    client: reqwest::Client,
}

#[cfg(feature = "async")]
impl AsyncOpenAI {
    pub fn new(base_url: impl Into<String>, api_key: Option<String>) -> Self {
        Self {
            base_url: base_url.into(),
            api_key,
            client: reqwest::Client::new(),
        }
    }

    pub fn with_client(
        base_url: impl Into<String>,
        api_key: Option<String>,
        client: reqwest::Client,
    ) -> Self {
        Self {
            base_url: base_url.into(),
            api_key,
            client,
        }
    }
}

#[cfg(feature = "async")]
#[async_trait::async_trait]
impl crate::AsyncChatBackend for AsyncOpenAI {
    async fn chat(&self, req: &ChatRequest) -> Result<ChatResponse, LlmError> {
        let body = build_request_body(req);
        let url = chat_url(&self.base_url);

        let mut builder = self.client.post(url).json(&body);
        if let Some(key) = &self.api_key {
            builder = builder.bearer_auth(key);
        }

        let resp = builder
            .send()
            .await
            .map_err(|e| LlmError::Transport(e.to_string()))?;

        let status = resp.status();
        if !status.is_success() {
            let message = resp
                .text()
                .await
                .unwrap_or_else(|_| "<unreadable body>".into());
            return Err(LlmError::Backend {
                status: status.as_u16(),
                message,
            });
        }

        let parsed: OpenAIChatResponse = resp
            .json()
            .await
            .map_err(|e| LlmError::Decode(e.to_string()))?;

        map_response(parsed)
    }
}
