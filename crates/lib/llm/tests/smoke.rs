//! Smoke tests against a local Ollama daemon via its OpenAI-compat endpoint.
//! Run with:
//!
//!     cargo test -p covalence-llm -- --ignored
//!
//! Expects `mathstral:7b` to be available locally. Override with COV_LLM_MODEL.

#![cfg(all(feature = "openai", any(feature = "sync", feature = "async")))]

fn model() -> String {
    std::env::var("COV_LLM_MODEL").unwrap_or_else(|_| "mathstral:7b".into())
}

#[cfg(feature = "sync")]
#[test]
#[ignore = "requires local ollama daemon on :11434"]
fn ollama_sync_complete() {
    use covalence_llm::{ChatOptions, Llm};
    let mut opts = ChatOptions::default();
    opts.temperature = Some(0.0);
    opts.max_tokens = Some(16);
    let llm = Llm::ollama(model()).with_options(opts);
    let answer = llm
        .complete("Answer with a single integer and nothing else. What is 2 + 2?")
        .expect("complete failed");
    println!("sync complete: {answer:?}");
    assert!(answer.contains('4'), "expected '4' in: {answer}");
}

#[cfg(feature = "async")]
#[tokio::test]
#[ignore = "requires local ollama daemon on :11434"]
async fn ollama_async_complete() {
    use covalence_llm::{AsyncLlm, ChatOptions};
    let mut opts = ChatOptions::default();
    opts.temperature = Some(0.0);
    opts.max_tokens = Some(16);
    let llm = AsyncLlm::ollama(model()).with_options(opts);
    let answer = llm
        .complete("Answer with a single integer and nothing else. What is 2 + 2?")
        .await
        .expect("complete failed");
    println!("async complete: {answer:?}");
    assert!(answer.contains('4'), "expected '4' in: {answer}");
}

#[cfg(feature = "sync")]
#[test]
#[ignore = "requires local ollama daemon on :11434"]
fn ollama_sync_chat_messages() {
    use covalence_llm::{ChatMessage, ChatOptions, Llm};
    let mut opts = ChatOptions::default();
    opts.temperature = Some(0.0);
    opts.max_tokens = Some(16);
    let llm = Llm::ollama(model()).with_options(opts);
    let resp = llm
        .chat(vec![
            ChatMessage::system("Answer with a single integer and nothing else."),
            ChatMessage::user("What is 2 + 2?"),
        ])
        .expect("chat failed");
    println!("sync chat: {resp:?}");
    assert!(resp.message.content.contains('4'));
    assert_eq!(resp.message.role, covalence_llm::Role::Assistant);
}

/// A 4xx response from the sync backend must surface as `LlmError::Backend`
/// (preserving the status code), not `Transport`. Regression test for the
/// ureq-3 default that converted 4xx into `Error::StatusCode` and lost the
/// body — we disable that and read the body ourselves.
#[cfg(feature = "sync")]
#[test]
#[ignore = "requires local ollama daemon on :11434"]
fn ollama_sync_4xx_is_backend_error() {
    use covalence_llm::backend::openai::OpenAI;
    use covalence_llm::{ChatBackend, ChatMessage, ChatRequest, LlmError};

    let backend = OpenAI::new("http://localhost:11434/v1", None);
    let req = ChatRequest::new(
        "definitely-not-a-real-model:xyz",
        vec![ChatMessage::user("hi")],
    );
    let err = backend.chat(&req).expect_err("should have failed");
    match err {
        LlmError::Backend { status, message } => {
            assert!((400..500).contains(&status), "expected 4xx, got {status}");
            assert!(!message.is_empty(), "expected non-empty error body");
        }
        other => panic!("expected LlmError::Backend, got {other:?}"),
    }
}

/// `Llm::from_env(Provider::Ollama, …)` uses no API key and reads the base
/// URL via the env-override chain, so it works against the local daemon.
#[cfg(feature = "sync")]
#[test]
#[ignore = "requires local ollama daemon on :11434"]
fn ollama_sync_from_env() {
    use covalence_llm::{ChatOptions, Llm, Provider};
    let mut opts = ChatOptions::default();
    opts.temperature = Some(0.0);
    opts.max_tokens = Some(16);
    let llm = Llm::from_env(Provider::Ollama, model())
        .expect("from_env failed")
        .with_options(opts);
    let answer = llm
        .complete("Answer with a single integer and nothing else. What is 2 + 2?")
        .expect("complete failed");
    assert!(answer.contains('4'), "expected '4' in: {answer}");
}
