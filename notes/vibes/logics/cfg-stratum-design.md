# CFG stratum — design (SpecTec grammars → Derives in HOL-omega)

Status: accepted design, implementation in progress on branch `spectec-grammar-cfg`.
Fills the "CFG stratum (headline next step)" entry of
`crates/kernel/hol/init/src/grammar/spectec/SKELETONS.md`. Companion to
[wasm-spec.md](./wasm-spec.md) (the SpecTec front end overall). Produced by a
three-design judge panel; the losing designs' verified corpus probes are folded
in below.

Zero TCB growth: everything here is init-layer / lib-crate untrusted driver
code; the kernel re-checks every construction. Lowering bugs cost
faithfulness/completeness, never soundness.

## Corpus facts (measured against the bundled WASM 3.0 dump — SKELETONS claims were stale)

- `wasm_spec_ast` exposes ~231 grammars: ~89 `B*` binary + ~142 `T*` text —
  the **complete** binary format `Bmagic..Bmodule` (`Binstr`: 498 productions).
  The old "only a handful of B* grammars" claim is wrong; fix it where it
  appears. Pin exact counts in tests **from the parser's output**, not prose.
- The dominant bridge failure is `Attr` (value capture wrapping nearly every
  non-terminal ref), *not* `Var`. Bare-`Var` grammars: `Bcustom`, `Bcustomsec`,
  `Bmodule`, `Bsym`.
- **11 of 89** B* grammars carry production premises (`prs ≠ ∅`): `Bmodule`(3),
  `BuN`(2), `BsN`(3), `Bname`(1), `Bheaptype`(1: the `Bs33` branch),
  `Bsection_`(1), `Bblocktype`, `Bmemarg`, `Btable`, `Bfunc`, `Bcode`. The
  earlier "prs empty across sampled grammars" note was sampling error.
- Parametric grammars: `BuN/BsN/BiN/BfN` (bit-width arg; `Bu32` = `BuN(32)`;
  recursive arg `N−7` terminates at 4), `Blist` (type param + grammar-valued
  param `BX`, iterated `ListN` times — the length-prefixed-vector idiom,
  context-sensitive, beyond CFG), `Bsection_` (3 params).
- The B* corpus is left-recursion-free (byte formats are prefix-coded). Pin as
  a test.
- Verified demo chain: `Breftype` productions are
  `[0x63]·Bheaptype | [0x64]·Bheaptype | Babsheaptype`; `Bheaptype[0]` →
  `Babsheaptype` is premise-free; `0x70 ∈ Babsheaptype` (range 0x69–0x74). So
  `[0x70]` parses via one `Var` hop and `[0x64,0x70]` via the two-hop
  `Breftype→Bheaptype→Babsheaptype` chain.

## Decisions

### 1. Substrate: binary metalogic engine, grammar reified as its clause set

`metalogic::binary::RuleSet2 { nt_ty: nat, word_ty: list u8, clauses }` — a
thin (~120 LoC) binary generalisation of `metalogic::RuleSet`, reusing
`conj`/`nth_conjunct`/`conj_thms` verbatim. Judgement per grammar env E:

```
Derives_E n w := ∀d : nat → list u8 → bool. Closed_E d ⟹ d n w
```

exactly `init/regex`'s `Matches` shape, data-driven from a grammar env the way
`wasm/relation.rs` is data-driven from the spec. Non-terminal tags are **nat
literals** (`mk_nat i` per env index) — literals, not uninterpreted free vars,
so a concrete soundness family `F : nat → set (list u8)` can distinguish tags;
names live only in the Rust symbol table (names = efficiency, never soundness).

A production `NT → σ₁…σₖ` lowers to the first-order clause
`∀w₁…wₖ. A₁ ⟹ … ⟹ Aₖ ⟹ d ⌜nt⌝ (cat w₁ (cat w₂ …))` where terminal segments
give **side antecedents** `Aⱼ = Matches ⌜cⱼ⌝ wⱼ` (embedding the existing
reified `regex u8` terms, fold tvar `'r` left free — existing `prove_matches`
theorems plug in as leaf premises with zero coercion) and non-terminal segments
give `Aⱼ = d ⌜ntⱼ⌝ wⱼ`. All clauses are first-order: the β-capture wall does
not bite.

**SKELETONS amendment (deliberate):** the entry asked for an
"impredicative-encoded reified CFG datatype". The grammar is instead reified
*as its clause set* — `Closed_E` literally quotes every production inside every
`Derives_E` proposition — the same representation decision as prop/PA/Metamath
databases/wasm relations. First-class grammar *values*
(`Derives g nt w` with `g : set (prod nat (list sym))`, one grammar-independent
4-clause rule set, single polymorphic `Models`-discharge) are the recorded
upgrade path once a consumer (grammar-transformation metatheorems, env
transport) exists; the concrete recipe is `metalogic::database`'s
`db_rule_set` + `monotone`.

### 2. Grammar environment: per-env, dependency-closed

`GrammarEnv` (in `init/grammar/cfg`) is built from a neutral
`covalence_grammar::cfg::Cfg<u8>`; assigns dense nat tags, lowers productions
in fixed order, yields one `RuleSet2`. All non-terminals share one `d`, so
mutual recursion, `Rec` groups, and cross-grammar `Var` refs compose for free
(the `tag`-mixing move of `spec_rule_set`). Envs are built as the dependency
closure of root instances (e.g. `{Breftype}`) — never Binstr-scale for demos;
whole-corpus lowering exists only for the coverage *report*. The env caches
the assumed `Closed_E` Thm and per-clause metadata (word-var order = `all_elim`
order). Env-inclusion transport is future work.

### 3. Soundness: discharge-free family least-fixpoint package (lands early)

CFG languages are least fixpoints with no fold denotation, so the headline is
the rule-induction package, stated over an explicit language-family variable:

```
S1 (family_soundness):
⊢ ∀F : nat → set (list u8). ClosedFam_E F ⟹ ∀n w. Derives_E n w ⟹ mem w (F n)
```

where `ClosedFam_E F` is `Closed_E` at `d := λn w. mem w (F n)` with exactly
the two outer β-redexes per `d`-occurrence reduced (audited helper; normal form
pinned by test; `Matches` antecedents and denotation folds never touched).
Derivation: assume, `all_elim` at the predicate, `beta_nf`-bridge, intro —
milliseconds, **independent of grammar size**: no clause is ever discharged,
they ride inside the assumed `ClosedFam`. This kills the per-grammar Closed-D
perf wall by construction.

Vacuity guards: **S0** — concrete trivial family `F_triv := λn. {w | true}`
with `⊢ ClosedFam_E F_triv`. **S3** — regular-fragment agreement on Var-free
envs: family `F_reg` maps tag i to `⟦⌜rᵢ⌝⟧`; per-clause discharge = regex
soundness moves; yields `⊢ Derives_E ⌜i⌝ w ⟹ mem w ⟦⌜rᵢ⌝⟧`. S3's discharge is
per-env (can't reuse regex's polymorphic cache) — run only on tiny envs,
slow tests `#[ignore]`d. **S2** (staged later): comprehension family
`L_E := λn. {w | Derives_E n w}` is E-closed and least — the full fixpoint
characterisation.

### 4. Lowering pipeline (SpecTec-specific bits stay out of the kernel crate)

- `covalence_grammar::cfg` (**`crates/lang/grammar`** — the existing crate):
  neutral IR `Cfg<T> { nts, prods }`, `Seg = Term(Regex<T>) | NonTerm(NtId)`;
  validation, nullable + left-recursion analysis, independent `naive_parse`
  test oracle. SpecTec-agnostic — the K-framework work targets this directly.
- `covalence_spectec::cfg` (`crates/lib/wasm/spectec`): SpecTec `Grammar` →
  `Cfg<u8>`. (a) **Attr-stripping** — `Attr{e,g1} ↦ g1`, counted in the
  report. Honesty: stripping a *fresh-variable capture* is language-preserving;
  a *parameter-equality* attr (e.g. `Bsection_`'s id byte `N:Bbyte` with `N`
  bound) is a constraint, and stripping it over-approximates — classify the
  two cases, strip only captures silently, count constraint-attrs as
  `approximated` (none occur in premise-free non-parametric grammars, so v1 is
  unaffected; the monomorphiser later constant-folds ground parameter-equality
  attrs into literal byte terminals). (b) Maximal Var-free subtrees →
  `sym_to_regex_u8` → `Seg::Term`; `Var` → `Seg::NonTerm`. (c) `Alt` containing
  a Var distributes into multiple productions. (d) `Iter{g,List/List1/Opt}`
  over Var-containing g desugars via synthetic non-terminals
  (`X* ⇒ Xs → ε | X Xs` etc.) — unlocks `Bcustom`'s body. (e) `Var{x,as1}`
  with args ⇒ monomorphisation by const-folded instance key (staged, M6).
  (f) `ListN` ⇒ skip+report (context-sensitive; over-approx `listn_as_list`
  mode is recorded future work, off by default). (g) **`prs ≠ ∅` ⇒
  skip+report** (11 grammars — see census above). Skip granularity =
  production; typed `CfgLowerError`; `CfgReport` mirrors `LoweringReport` with
  per-grammar full/partial/none classification and ratcheted coverage counts.
  **Invariant (direction matters): every lowering is an under-approximation —
  `L(lowered Cfg) ⊆ L(SpecTec grammar)` — so `⊢ Derives_E` theorems imply
  membership in the true spec language.** No premise-drop over-approx mode in
  v1.
- `covalence-init/src/grammar/cfg` consumes only `Cfg<u8>`.

### 5. Recognizer/tactic: two-phase, copied from grammar/regex

Memoised top-down recognizer over `(NodeRef, lo, hi)` (NodeRef = regex Core ptr
or NtId), split enumeration as `CoreKind::Seq`; in-progress set as
belt-and-braces against left recursion (corpus has none, analysis flags it).
→ `CfgPlan` → single builder pass, zero failed kernel calls. Terminal segments
get `⊢ Matches ⌜cⱼ⌝ wⱼ` from the existing regex tactic; non-terminal segments
recurse. Generic application `derive_mixed(rs2, clause_idx, word_args,
premises)` with `Premise::Side(Thm)` vs `Premise::Derivation(Thm)` lives in
`metalogic::binary` (wasm/relation can later reuse it for if-premises).
Public: `GrammarEnv::prove_derives(nt, bytes) → ⊢ Derives_E ⌜nt⌝ w`
(hypothesis-free), `prove_in_every_family` chaining S1. Words stay rule-shaped
cat/cons trees (flattening deferred; oracle tests compare flattened bytes).

## North star (v1, all hypothesis-free, real dump + real bytes)

- T1: `⊢ Derives_{E_pre} ⌜Bmagic⌝ ⌜[0x00,0x61,0x73,0x6D]⌝` and `Bversion` on
  `[0x01,0,0,0]` — the real WASM preamble.
- T2 (headline): `⊢ Derives_{E_ref} ⌜Breftype⌝ ⌜[0x64,0x70]⌝` — three clause
  applications across three grammars, `0x70` leaf via a regex `Matches`
  theorem; plus the one-hop `[0x70]` variant. (`Bheaptype` lowers *partially* —
  its `Bs33` branch is premise-skipped — which the chain doesn't need.)
- T3: S1+T2 → `⊢ ∀F. ClosedFam_{E_ref} F ⟹ mem w (F ⌜Breftype⌝)` — the bytes
  lie in every language family closed under the WASM reftype rules.
- Coverage report over all B* grammars with ratcheted counts (pinned from
  parser output). Honest ratchet: fully-regular grammars + `Bsym` lower fully;
  `Bcustom` lowers as a grammar but its closure needs `Bname` (premise) —
  stretch, not promise. `Bmodule` needs premises+params: out of v1 scope.

## Milestones

M0 neutral IR (`covalence_grammar::cfg`) → M1 `metalogic/binary.rs` +
`GrammarEnv` + toy derives + S0 → M2 tactic (anbn + mutual-recursion toys,
differential vs `naive_parse`) → M3 S1 + normal-form pin + toy S3 → M4 SpecTec
lowering + census/ratchet tests + stale-SKELETONS fixes → M5 north-star demo +
wiring + docs. M6 stretch: monomorphisation (`BuN` chain), S2, `Bname`/
`Bcustom` if reachable. Every milestone lands with green `cargo test`.

## Version lattice + metatheorems (added 2026-07-13, maintainer direction)

Requirements: WASM **1.0 and 2.0** alongside 3.0, plus arbitrary *subsets* of
WASM; and version-inclusion **metatheorems** — WASM 1.0 ⊆ 2.0 ⊆ 3.0 both
syntactically and semantically — as the flagship test of the machinery.

1. **Env transport is promoted from "future work" to a planned milestone
   (M7).** The clause-set representation already supports it with no new
   kernel machinery: to prove `⊢ ∀n w. Derives_E n w ⟹ Derives_E' (ρ n) w`
   (ρ = Rust-computed tag remapping, aligning non-terminals *by name* across
   envs since tags are per-env dense indices), run `rule_induction2` on E at
   `pred := λn w. Derives_E' (ρ n) w` and discharge each E clause with the
   matching E' derivation constructor (`derive_mixed`). Data-driven: a
   Rust-side matcher pairs each E production with an E' production (or a
   derivable composite); unmatched productions ⇒ skip+report, making the
   theorem an honest per-matched-fragment inclusion rather than a false
   blanket claim. Subgrammar-extraction envs get `Derives_sub ⟹ Derives_full`
   the same way — that is the "subsets of WASM" story.
2. **Semantic inclusion** rides the relation leg (`wasm/relation.rs`):
   `spec_rule_set` per version yields `Derivable_S_v`; inclusion by the same
   rule-induction-with-`pred := Derivable_S_v'` move on the unary engine.
   `encode.rs` is version-independent, so rules unchanged across versions
   encode to *identical* clauses (discharge is mechanical); reformulated rules
   (3.0 rewrote several judgement shapes) need per-rule bridge lemmas —
   matched/bridged/unmatched reported, never silently claimed.
3. **Honesty caveat:** the versions are not literal rule-for-rule supersets;
   the deliverable is "inclusion on the matched fragment + explicit residue
   report", tightening as bridge lemmas land. Grammar-side (binary format)
   inclusion is expected to be near-total; typing/reduction less so.
4. **Dumps (blocker resolved to a recipe, 2026-07-13):** upstream bundles only
   the 3.0 dump, but the dump backend is *upstream* SpecTec (`--ast` prints the
   elaborated IL as S-exprs; `spectec/src/backend-ast/` in WebAssembly/spec),
   documented in `wasm_spec_ast`'s CONTRIBUTING.md. Recipe: checkout
   WebAssembly/spec at pinned commit `d7b678327cd370cdbc5acfa94bd108772e2bef68`
   (what `spectec_ast` 2.0's decoder tracks — do NOT use main, IL format
   drifts), build spectec (OCaml ≥5.1 + dune + menhir + zarith + mdx; pure-nix
   shell works, opam fallback), then from `specification/`:
   `../spectec/spectec wasm-1.0/* --ast > wasm-1.0.spectec-ast` (same for
   2.0); validate with `spectec_ast::parse_spectec_stream` before embedding in
   covalence-spectec (`grammar::wasm1/wasm2` next to `wasm3`). **Verified:
   `wasm-1.0/A-binary.spectec` and `wasm-2.0/A-binary.spectec` both define the
   full binary grammars** (Bvaltype…Bmodule; 2.0 incl. SIMD Binstr), and both
   versions ship full syntax/typing/reduction — so both metatheorem legs have
   data. Quirk: 1.0/2.0 spell the magic as literal bytes rather than a named
   `Bmagic` rule — don't key on grammar names across versions.
   **Executed 2026-07-13:** both dumps produced and validated (0 decode
   errors via `parse_spectec_stream`), staged at
   `~/tmp/spectec-dumps/wasm-{1.0,2.0}.spectec-ast` pending embedding:
   1.0 = 315 defs / 61 grams (sha256 4ee41611…), 2.0 = 467 defs / 71 grams
   (sha256 af2da767…); 3.0 bundled = 972 defs / 231 grams. Toolchain notes:
   `nix-shell -p ocaml dune_3 ocamlPackages.{findlib,zarith,menhir,menhirLib,mdx}`
   (plain `nix shell` misses findlib hooks), build with `dune build` (the
   Makefile's opam target fails), binary at
   `_build/default/src/exe-spectec/main.exe`.
5. Once cross-version metatheorems multiply, the grammar-as-value upgrade
   (§1: one `monotone` theorem via `metalogic::database`'s recipe instead of
   per-pair inductions) becomes the economical form — unchanged as the
   recorded end-state; per-pair transport first.

## Risks / mitigations (short)

Per-env S3 discharge cost → S1 is discharge-free, S3 tiny-env-only.
`Closed_E` size / linear `nth_conjunct` → dependency-scoped envs, cached
assumed-Closed, padded-env benchmark; balanced conjunction if needed later.
Cat-tree words → oracle flattens; normalisation is a SKELETONS residual.
Free-`'r` leakage → stay schematic everywhere, pin only at regex-soundness
projection; cross-plugging test in M2. β discipline → one audited ClosedFam
helper + pinned normal form. Attr semantics → capture/constraint split above.
