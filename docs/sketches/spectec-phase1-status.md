# SpecTec Phase 1 — status

> Phase 1 lands a SpecTec lexer and a structural parser for `syntax` and
> `def` forms. Everything else (`relation`, `rule`, `var`, `grammar`)
> folds into `Top::Other` as raw token runs and is deferred to Phase 2.

See `docs/sketches/spectec-verification-plan.md` for the overall verification
strategy. This file records the per-corpus parse-pass outcome.

## Test counts

| Suite | Tests | Pass |
|---|---:|---:|
| `parse::tests` + `lex::tests` + `source::tests` unit tests | 38 | 38 |
| `tests/lex_corpus.rs` — full corpus lexing | 3 | 3 |
| `tests/parse_corpus.rs` — full corpus parsing | 4 | 4 |
| `tests/wasm_spec.rs` — pre-existing `wasm_spec_ast` smoke tests | 2 | 2 |
| **Total** | **47** | **47** |

## Corpus parse-pass outcome

Across all 36 vendored `wasm-3.0/*.spectec` files plus
`test-frontend/test.spectec` and `test-middlend/test.spectec`:

- **All files lex without error.**
- **All files parse to a `Vec<Top>` without diagnostic errors.**

WASM 3.0 totals: **2808 top-level forms** across 36 files —
**1614 structurally parsed** (~57%) and **1194 folded to `Top::Other`** (~43%).

| Form kind | Count | Notes |
|---|---:|---|
| `syntax` | 272 | All `syntax` declarations (variant, record, alias, profiled, parametric, forward-decl) |
| `def_sig` | 538 | `def $NAME(...) : ret` signatures plus nullary `def $NAME : ret` and hint-only `def $NAME hint(builtin)` |
| `def_clause` | 804 | `def $NAME(pat) = rhs` clauses, with or without premises |
| `other` | 1194 | `relation` / `rule` / `var` / `grammar` — Phase 2 will structure these |

## Files at 100% structured coverage

These files contain only `syntax`/`def` and are fully structured by Phase 1:

```
0.1-aux.vars         0.2-aux.num            0.3-aux.seq
1.0-syntax.profiles  3.0-numerics.relaxed   3.1-numerics.scalar
3.2-numerics.vector  4.2-execution.types    4.4-execution.modules
X.1-notation.syntax
```

## Files dominated by `Top::Other`

These files are typing-rule heavy (`relation` / `rule`) or grammar-heavy
(`grammar`), so most of their forms are deferred to Phase 2 elaboration:

```
2.2-validation.subtyping              (0/69 structured)
2.3-validation.instructions           (2/151)
4.3-execution.instructions            (3/227)
5.2-binary.types                      (0/20)
5.3-binary.instructions               (2/92)
6.0-text.lexical                      (0/19)
6.2-text.types                        (0/34)
6.3-text.instructions                 (0/111)
7.0-soundness.contexts                (0/2)
7.1-soundness.configurations          (3/82)
```

This split is expected: typing judgments, reduction rules, and
binary/text encodings are exactly the kinds of forms Phase 2's mixfix
elaborator will tackle.

## Language features confirmed working

Phase 1 parsing exercises these SpecTec features in the wild (corpus
test) plus unit tests for each:

**Lexing:**
- `;;` line comments and `\<newline>` line continuations
- Identifiers with subscripts (`t_1`), primes (`C'`, `C''`), leading
  underscores (`_IDX`, `_RESULT`)
- Decimal and hex (`0xFF`) numeric literals
- Text literals with `\n` `\t` `\r` `\\` `\"` `\0` escapes
- All multi-character punctuation including `|-` `<:` `~>` `~>*` `~~`
  `=/=` `<=` `>=` `/\` `\/` `++` `:=` `--` `...` `->`
- Distinguishes `;` (separator) from `;;` (comment)
- Distinguishes `--` (premise) from `-` `-` (token pair)

**Parsing — `syntax`:**
- Variant body with or without leading `|`
- Record body with `{ FIELD ty, ... }`
- Record body with leading `...` for forward extension
- Alias body (single expression)
- `/syn` `/sem` profile suffix and numeric profile suffix (`/1`, `/2`)
- Parametric form `syntax foo(N)` and `syntax list(syntax X)`
- Hint clauses both on the declaration and per-alternative
- Forward declarations (no body)
- Backtick-escaped names (`` syntax `syntax = () ``)
- Backtick-escaped field names (`` `... recorddots ``)

**Parsing — `def`:**
- Standard form `def $NAME(args) : ret`
- Nullary form `def $ANYREF : reftype hint(...)`
- Forward / hint-only form `def $ibits_ hint(builtin)`
- Clauses with `if`/`let`/`otherwise` premises
- Arguments containing `syntax X` type parameters (`def $opt_(syntax X, X*)`)
- Keyword names (`def $var(syntax X)`)

**Robustness — top-level boundary detection:**
- Paren-depth-aware: top-level keywords inside `(...)` aren't boundaries
- Slash-aware: `Foo/def`, `Foo/syn`, `Foo/var` aren't broken at the keyword

## Known limitations (intended, deferred to Phase 2)

- All `relation`, `rule`, `var`, `grammar` forms fold to `Top::Other`
- Hint bodies are opaque `TokenRun`s
- `syntax` variant alternatives are opaque `TokenRun`s
- `def` argument types, return types, RHS, and premises are opaque
  `TokenRun`s
- `syntax` parametric parameter list stored as a single raw `TokenRun`
- `MixOp` recognition and operator-table-driven re-parse is Phase 2

## Verification posture

The strongest available Phase 1 verification is **the structural-parse
corpus test**: every upstream `.spectec` file we have, parses. We do not
yet have a per-AST-node verification because Phase 1 doesn't elaborate
into `spectec_ast` shapes. That comes in Phase 2, where the test moves
from "no errors" to "structurally equal to `wasm_spec_ast::get_wasm_spectec_ast()`."

The Phase 1 acceptance criterion was: **every byte-string accepted by
the OCaml lexer lexes here without error; every byte-string accepted by
the OCaml parser parses here to a `Vec<Top>` without error.** Met.
