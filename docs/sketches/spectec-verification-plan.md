# covalence-spectec verification plan

> Status: live plan; updated as each phase lands.

## What "obeys the SpecTec specification" means here

SpecTec has no machine-readable formal spec of its own concrete syntax. The
authoritative sources are:

1. **The OCaml reference implementation** (`Wasm-DSL/spectec`) — parser
   `spectec/src/frontend/parser.mly`, lexer `spectec/src/frontend/lexer.mll`,
   elaborator `spectec/src/frontend/elab.ml`. Whatever it accepts is what
   we must accept.
2. **The upstream test suites** (`spectec/test-frontend/`,
   `spectec/test-middlend/`) — focused unit cases for the parser and
   transformations.
3. **The WASM 3.0 specification** (`specification/wasm-3.0/*.spectec`,
   36 files) — the largest real-world source corpus.
4. **The pre-dumped WebAssembly AST** (`wasm_spec_ast` crate, version 1.0.1)
   — the OCaml binary's elaborated output for the WASM 3.0 spec, already
   in our `Cargo.lock`. This is **ground truth for Phase 2 differential
   testing** with zero OCaml dependency in the build.

We vendor (1)'s test inputs (not the binary), (2), and (3) into
`assets/spectec/` and pin the upstream commit in a README.

## Per-phase verification

### Phase 1 — lex + parse to CST

**Hypothesis under test:** every byte-string accepted by the OCaml lexer
lexes here without error; every byte-string accepted by the OCaml parser
for the (`syntax`, `def`) subset parses here to a structured CST.

| Test | What it checks |
|---|---|
| `lex_corpus.rs`: lex all 36 wasm-3.0 files | lexer accepts the full real-world corpus |
| `lex_corpus.rs`: lex `test-frontend/test.spectec` | lexer accepts upstream's focused mixfix/variant/iteration cases |
| `lex_corpus.rs`: lex `test-middlend/test.spectec` | lexer accepts upstream's middlend tests |
| `lex.rs` unit cases | tokenizes each punctuation form, primed/subscripted idents, all comment kinds, numeric forms |
| `parse_corpus.rs`: parse two smallest wasm-3.0 files (syntax + def only) | parser accepts the targeted subset end-to-end on real source |
| `parse.rs` unit cases | each `syntax` form (variant, record, alias, parametric, profiled, extended `...`); each `def` form (signature, clause, guards `if`/`let`/`otherwise`) |
| Phase 1 status report | inventory of which corpus files reach each pass cleanly + why others stop |

**Gap acknowledgement:** Phase 1 deliberately doesn't parse `relation`,
`rule`, `grammar`, `hint` bodies, or `var` declarations. The report
documents which corpus files this excludes (most of them — Phase 1 fully
parses only ~5 of the 36 wasm-3.0 files). That's expected and not a bug.

### Phase 2 — mixfix + elaboration

**Hypothesis under test:** for every wasm-3.0 source file, our pipeline
produces an AST structurally equal to the OCaml elaborator's output.

This is the strongest possible verification short of formal proof. The
OCaml dump is in `wasm_spec_ast` as a static fixture; we have it locally
without invoking any OCaml.

| Test | What it checks |
|---|---|
| `elab_corpus.rs`: elaborate each wasm-3.0 file, diff against `wasm_spec_ast::get_wasm_spectec_ast()` | structural equality with OCaml output, file by file |
| `elab_unit.rs`: each focused case from `test-frontend/test.spectec` | mixfix corner cases, variant extension, empty iterations, hint resolution |
| `mixfix.rs` unit cases | precedence climbing on synthetic operator tables; ambiguous-syntax error cases |
| `elab/iter.rs` unit cases | iteration binder inference on hand-crafted patterns from samples 5/6 of the language tour |
| `elab/profile.rs` unit cases | `/syn` `/sem` merge ordering; `...` splicing across multiple decls |
| `elab/var.rs` unit cases | metavar lookup with subscripts/primes; collision detection |

**Acceptance criterion:** `elab_corpus.rs` passes with zero structural
diffs on all 36 wasm-3.0 files, modulo a documented list of
type-checking-dependent transformations deferred to Phase 3 (`Sub`
coercion insertion, SCC mutual-recursion grouping).

### Phase 3 — full type checking (deferred until needed)

**Hypothesis under test:** after Phase 3, the OCaml binary is no longer
required for any production path; only kept as the §5.2 HAZARD mirror.

| Test | What it checks |
|---|---|
| `elab_corpus.rs` passes with zero diffs, no deferred-list exceptions | full structural equality with OCaml |
| `differential_oracle.rs` (optional feature, off by default): shells out to OCaml `spectec` on every file in a corpus, diffs against our output | live cross-check whenever the OCaml binary is available |

Phase 3 is months of work and likely never needed if we keep OCaml as the
permanent mirror.

## Standing rules

- Every new parser feature lands with at least one unit test in the
  relevant module + one corpus-file assertion.
- Every elaboration pass lands with a unit test on a hand-crafted minimal
  case + the relevant focused test from `test-frontend/test.spectec`.
- Whenever a corpus file *fails* in a way we don't expect, capture the
  minimal reproducer into a unit test before fixing.
- The `parse_corpus.rs` and `elab_corpus.rs` tests run on `cargo test`
  by default. The optional `differential_oracle.rs` test is gated by a
  feature flag because it needs the OCaml binary on `$PATH`.

## Sources of truth, in priority order

When two sources disagree, this is the order to trust:

1. **OCaml binary behaviour on real input.** Empirical.
2. **`wasm_spec_ast` pre-dump** for the WASM 3.0 spec. Pinned to a
   specific OCaml commit; matches that commit's behaviour exactly.
3. **`elab.ml` source.** Authoritative reading of what the elaborator
   does, but read carefully — it has historical accretions.
4. **The SpecTec papers and README.** Aspirational; the implementation
   sometimes leads or lags.
5. **The WASM 3.0 spec source.** Our largest in-the-wild sample but does
   not exercise every language feature.
