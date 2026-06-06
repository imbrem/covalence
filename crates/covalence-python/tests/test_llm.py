"""Smoke tests for the covalence-llm Python bindings (feature `llm`).

Skipped automatically unless:
  * The extension was built with the `llm` feature (so `covalence.Llm` exists)
  * A local Ollama daemon is reachable on http://localhost:11434

Run with: COV_LLM_MODEL=mathstral:7b pytest crates/covalence-python/tests/test_llm.py
"""

import urllib.error
import urllib.request

import pytest

import covalence

pytestmark = pytest.mark.skipif(
    not hasattr(covalence, "Llm"),
    reason="built without the `llm` feature",
)


def _ollama_up() -> bool:
    try:
        with urllib.request.urlopen("http://localhost:11434/api/tags", timeout=1) as r:
            return r.status == 200
    except (urllib.error.URLError, OSError):
        return False


needs_ollama = pytest.mark.skipif(
    not _ollama_up(), reason="local ollama daemon not running"
)

MODEL = "mathstral:7b"


@needs_ollama
def test_complete_arithmetic():
    llm = covalence.Ollama(MODEL)
    answer = llm.complete("Answer with a single integer and nothing else. What is 2 + 2?")
    assert "4" in answer


@needs_ollama
def test_chat_messages():
    llm = covalence.Ollama(MODEL)
    resp = llm.chat([
        covalence.ChatMessage.system("Answer with a single integer and nothing else."),
        covalence.ChatMessage.user("What is 2 + 2?"),
    ])
    assert "4" in resp.content
    assert resp.role == "assistant"
    assert resp.finish_reason in {"stop", "length", "other"}


@needs_ollama
def test_subclass_relationship():
    llm = covalence.Ollama(MODEL)
    assert isinstance(llm, covalence.Llm)
    assert llm.model == MODEL


def test_options_roundtrip():
    opts = covalence.ChatOptions(temperature=0.1, top_p=0.9, max_tokens=8, seed=42, stop=["END"])
    assert opts.temperature == pytest.approx(0.1)
    assert opts.top_p == pytest.approx(0.9)
    assert opts.max_tokens == 8
    assert opts.seed == 42
    assert opts.stop == ["END"]


def test_message_helpers():
    m = covalence.ChatMessage.user("hi")
    assert m.role == "user"
    assert m.content == "hi"
    assert covalence.ChatMessage.system("s").role == "system"
    assert covalence.ChatMessage.assistant("a").role == "assistant"


def test_provider_constructors_exist():
    # Don't actually call them (no API keys in CI); just confirm the classes
    # exist and accept the expected signatures.
    for name in ("Ollama", "OpenAI", "Groq", "Cerebras", "DeepSeek", "OpenAICompat"):
        assert hasattr(covalence, name), f"missing class: {name}"
    for url in ("OPENAI_BASE_URL", "GROQ_BASE_URL", "CEREBRAS_BASE_URL", "DEEPSEEK_BASE_URL", "OLLAMA_BASE_URL"):
        assert isinstance(getattr(covalence, url), str)
