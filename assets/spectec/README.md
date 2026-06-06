# Vendored SpecTec test corpora

These files are vendored from upstream so `cargo test` does not require
network access. Do not edit them; refresh from upstream when bumping the
pin.

## Upstream

- Repository: <https://github.com/Wasm-DSL/spectec>
- Pinned commit: `acc6e834ff403c82554d081237f327346190ad96`
- License: BSD-3-Clause (`spectec/test/LICENSE` in upstream)

## Contents

| Path | Origin | Purpose |
|---|---|---|
| `wasm-3.0/*.spectec` (36 files, ~334 KB) | `specification/wasm-3.0/` | The full WebAssembly 3.0 specification in SpecTec; the largest real-world source corpus we test against. |
| `test-frontend/test.spectec` (~12 KB) | `spectec/test-frontend/test.spectec` | Focused unit cases targeting parser + elaborator features: mixfix operators, variant extension, empty iterations, hint resolution. |
| `test-middlend/test.spectec` + `.exp` | `spectec/test-middlend/` | Middle-end transformation unit cases. The `.exp` file is the expected output of the upstream middle-end on the corresponding `.spectec` input. |

## Refresh procedure

```sh
COMMIT=<new-sha>

cd assets/spectec
for f in $(gh api repos/Wasm-DSL/spectec/contents/specification/wasm-3.0?ref=$COMMIT \
            --jq '.[] | select(.type=="file" and (.name|endswith(".spectec"))) | .name'); do
  gh api "repos/Wasm-DSL/spectec/contents/specification/wasm-3.0/$f?ref=$COMMIT" \
    --jq '.content' | base64 -d > "wasm-3.0/$f"
done

gh api "repos/Wasm-DSL/spectec/contents/spectec/test-frontend/test.spectec?ref=$COMMIT" \
  --jq '.content' | base64 -d > test-frontend/test.spectec
gh api "repos/Wasm-DSL/spectec/contents/spectec/test-middlend/test.spectec?ref=$COMMIT" \
  --jq '.content' | base64 -d > test-middlend/test.spectec
gh api "repos/Wasm-DSL/spectec/contents/spectec/test-middlend/test.spectec.exp?ref=$COMMIT" \
  --jq '.content' | base64 -d > test-middlend/test.spectec.exp
```

After refreshing, update the pinned commit hash above and re-run
`cargo test -p covalence-spectec`. The `wasm_spec_ast` dependency must be
bumped in lockstep when it ships an updated dump.
