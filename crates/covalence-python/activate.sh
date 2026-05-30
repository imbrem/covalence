#!/bin/bash
# activate.sh — Find and activate the Python venv.
# Works both in the main repo and in git worktrees (where .venv is absent).
VENV=".venv"
if [ ! -d "$VENV" ]; then
    MAIN=$(git worktree list --porcelain 2>/dev/null | head -1 | sed 's/^worktree //')
    if [ -n "$MAIN" ]; then
        VENV="$MAIN/crates/covalence-python/.venv"
    fi
fi
if [ ! -d "$VENV" ]; then
    echo "error: Python .venv not found (run: python3 -m venv .venv && source .venv/bin/activate && pip install maturin pytest)" >&2
    return 1 2>/dev/null || exit 1
fi
source "$VENV/bin/activate"
