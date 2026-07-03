//! Integration tests for the env-based secrets/endpoints resolver.
//!
//! These tests mutate `std::env`, which is `unsafe` under Rust 2024 and unsound
//! under concurrent reads. We sidestep that by giving every test a unique env
//! prefix and serializing the suite via `serial_test`.

use covalence_proto::providers::Provider;
use covalence_proto::secrets::{self, ExposeSecret, SecretError};
use serial_test::serial;

fn set(var: &str, val: &str) {
    unsafe { std::env::set_var(var, val) }
}
fn unset(var: &str) {
    unsafe { std::env::remove_var(var) }
}

#[test]
#[serial]
fn direct_env_resolves() {
    let var = "COV_TEST_DIRECT_KEY";
    set(var, "abc123");
    let s = secrets::from_env(var).unwrap();
    assert_eq!(s.expose_secret(), "abc123");
    unset(var);
}

#[test]
#[serial]
fn cov_override_wins_over_sdk_var() {
    let var = "COV_TEST_OVERRIDE_KEY";
    let cov_var = "COV_COV_TEST_OVERRIDE_KEY";
    set(var, "from_sdk");
    set(cov_var, "from_cov");
    let s = secrets::from_env(var).unwrap();
    assert_eq!(s.expose_secret(), "from_cov");
    unset(var);
    unset(cov_var);
}

#[test]
#[serial]
fn cmd_fallback_runs_shell() {
    let var = "COV_TEST_CMD_FB";
    let cmd_var = "COV_TEST_CMD_FB_CMD";
    unset(var);
    set(cmd_var, "printf 'sk-test\\n'");
    let s = secrets::from_env(var).unwrap();
    assert_eq!(s.expose_secret(), "sk-test");
    unset(cmd_var);
}

#[test]
#[serial]
fn cmd_failure_surfaces() {
    let var = "COV_TEST_CMD_FAIL";
    set(&format!("{var}_CMD"), "exit 7");
    let err = secrets::from_env(var).unwrap_err();
    match err {
        SecretError::CommandFailed { status, .. } => assert_eq!(status, 7),
        other => panic!("expected CommandFailed, got {other:?}"),
    }
    unset(&format!("{var}_CMD"));
}

#[test]
#[serial]
fn missing_returns_error() {
    let var = "COV_TEST_MISSING_KEY";
    let err = secrets::from_env(var).unwrap_err();
    assert!(matches!(err, SecretError::Missing { .. }));
}

#[test]
#[serial]
fn endpoint_uses_override() {
    let var = "COV_TEST_ENDPOINT";
    let cov_var = "COV_COV_TEST_ENDPOINT";
    set(var, "https://sdk.example/v1");
    set(cov_var, "https://override.example/v1");
    let v = secrets::endpoint_from_env(var).unwrap();
    assert_eq!(v, "https://override.example/v1");
    unset(var);
    unset(cov_var);
}

#[test]
#[serial]
fn endpoint_returns_none_when_unset() {
    let var = "COV_TEST_ENDPOINT_NONE";
    assert!(secrets::endpoint_from_env(var).is_none());
}

#[test]
#[serial]
fn provider_resolve_base_url_falls_back_to_default() {
    unset(Provider::OpenAI.base_url_env_var());
    unset(&format!("COV_{}", Provider::OpenAI.base_url_env_var()));
    let url = Provider::OpenAI.resolve_base_url();
    assert_eq!(url, Provider::OpenAI.default_base_url());
}

#[test]
#[serial]
fn provider_resolve_base_url_uses_cov_override() {
    set("COV_OPENAI_BASE_URL", "https://proxy.internal/v1");
    let url = Provider::OpenAI.resolve_base_url();
    assert_eq!(url, "https://proxy.internal/v1");
    unset("COV_OPENAI_BASE_URL");
}

#[test]
#[serial]
fn provider_resolve_api_key_returns_none_for_ollama() {
    let v = Provider::Ollama.resolve_api_key().unwrap();
    assert!(v.is_none());
}
