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
    let answer = llm.complete("Answer with a single integer and nothing else. What is 2 + 2?")
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
    let answer = llm.complete("Answer with a single integer and nothing else. What is 2 + 2?")
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
