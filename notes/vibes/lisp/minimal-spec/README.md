# Minimal end-to-end `/lisp` REPL — a fully-defined spec (discussion draft, agent-authored)

Goal (verbatim from the ask): a `/lisp` web endpoint exposing a **very basic Lisp REPL**
where **the user types an S-expression, the S-expression is evaluated *as a theorem*, and
the result is printed**. Minimal but *fully* defined: internal parse/deparse traits, a
Forth-style *dictionary-lookup → numeral → builtin* split (so numeral handling is an
explicit, swappable decision), `#`-directive hooks into the runtime (switch dialects,
prove theorems, name reductions, **content-address via the runtime for now**), and a
high-level API (`parse()`/`reduce()`/`prettyprint()`/…) that is the *only* thing the REPL
is built from — the same API exposed to **Python**, to **WASM via a WIT contract**
([`lisp.wit`](./lisp.wit)), and thereby to **JavaScript**.

Not committed. Companion to [`../initial-ideas/`](../initial-ideas/) (the design corpus
this distills). Scope discipline: everything here is *minimal* — one dialect, a handful of
builtins, refl-only proving — but every piece is defined concretely enough to implement
without another design pass.

---

## 0. The pipeline — three certified phases

The REPL step is a **composition of three kernel theorems** (see
[`../initial-ideas/reduction-relations-and-state.md`](../initial-ideas/reduction-relations-and-state.md)),
not a single equation:

```
Thm 1 (read):    ⊢ Parses  state_in   input_string   input_sexpr
Thm 2 (reduce):  ⊢ Reduces (state_in,  input_sexpr) (state_out, output_sexpr)
Thm 3 (print):   ⊢ Parses  state_out  output_string  output_sexpr
```

"Evaluate as a theorem" = **Thm 2**: reduction is a *relation* `Reduces ⊆ (State ×
SExpr)²`, and the REPL returns the membership theorem `⊢ (state, input) ~~> (state',
output)`. A **relation, not a function**, so it supports **nondeterminism (AMB) with no
mutable state** — one input, several valid outputs, the theorem witnessing one branch. The
equational `⊢ input = nf` is the special case (deterministic, `state_out = state_in`). The
printed line is `output_string` (Thm 3); the reduction/parse theorems are one keystroke
away (`#show`/`#trace`). Nothing printed is un-witnessed.

`state` is `definitions` (the dictionary) for the minimal cut, but is threaded as an
*extensible world* `{ defs, kv, log, … }` (§5.1) so `set!`/`print`/effects slot in later
without re-typing. `Parses`/`Reduces` are inductively-defined HOL relations; the REPL is an
untrusted assembler that discharges membership from their intro rules — the kernel checks.

---

## 1. Data model (the IR)

Reuse the existing canonical IR (`covalence-haskell::sexpr::SExpr`, promoted per the
initial-ideas consolidation) — minimal shape:

```rust
pub enum SExpr {
    Atom(Symbol),        // a bare token: `car`, `foo`, `+`, `42`, `0xFF` — UNRESOLVED
    List(Vec<SExpr>),    // `(f a b)` ; `()` = nil
}
pub struct Symbol(SmolStr);
```

Key decision: **the reader does *not* classify atoms.** `42` and `car` are both `Atom`
at parse time. Classification (word vs numeral) happens in evaluation, Forth-style (§4).
This is what makes numeral handling a *runtime, swappable* decision rather than a lexer
hard-coding. (A cons-based `SExpr` and string/char atoms are post-minimal; `List(Vec)`
is enough for the demo.)

---

## 2. The internal traits — parsing & deparsing

```rust
/// Text -> IR. The reader relation's functional direction (parsing-relations.md).
pub trait Reader {
    fn read_one(&self, src: &str) -> Result<SExpr, ReadError>;      // exactly one top form
    fn read_all(&self, src: &str) -> Result<Vec<SExpr>, ReadError>; // a program
}

/// IR -> text. The canonical Printer = the chosen section of the reader relation
/// (parsing-relations.md §deparse). Its output MUST re-read to an equal SExpr
/// (round-trip), which is also what makes content-address hashing well-defined (§8).
pub trait Printer {
    fn print(&self, x: &SExpr) -> String;
}
```

Minimal `Reader` impl = a hand-written recursive-descent S-expr reader (whitespace,
`(`…`)`, atom-runs); the relational/`covalence-grammar` upgrade is post-minimal. Minimal
`Printer` = single-line canonical form (`(f a b)`, one space, no redundant parens). The
two are a **parse/deparse pair** bundled per dialect (§6).

---

## 3. The high-level API (the REPL is built ONLY from this)

`Session` is a concrete **`impl Repl + SExprRepl`**
([`../initial-ideas/generic-repl-trait.md`](../initial-ideas/generic-repl-trait.md)):
`State`/`Term`/`Eval` + per-phase error types (`StartError`/`ParseError`/`EvalError`),
`start()` yields a fresh `State`, and `parse` is the **event-driven** builder
(`covalence_sexp::parse_with` → an `SExpBuilder` folding straight to `Term`, no `SExpr`
tree; the Forth atom-split lives in `build_atom`). The methods below *are* the trait
methods — nothing in the REPL loop reaches past them, and the Python/WIT/JS bindings mirror
this surface verbatim.

```rust
pub struct Session { /* dialect, kernel, dictionary, named reductions, CA store */ }

impl Session {
    pub fn new() -> Self;

    // text -> IR   (proves Thm 1: ⊢ Parses state_in src x)
    pub fn parse(&self, src: &str) -> Result<SExpr, Error>;
    // IR -> canonical text under current state (a section of Parses; may abbreviate, §5.2)
    pub fn prettyprint(&self, x: &SExpr) -> String;
    // evaluate-as-theorem: ⊢ Reduces (state, x) (state', output)   (Thm 2, §4–§5)
    pub fn reduce(&mut self, x: &SExpr) -> Result<Thm, Error>;
    // resume a nondeterministic (amb) reduction for the next witness, if any (`:next`)
    pub fn next(&mut self, t: &Thm) -> Option<Thm>;
    // a reduction theorem's printed form; full => the whole `~~>` relation, else output_sexpr
    pub fn show(&self, t: &Thm, full: bool) -> String;

    // the whole REPL step: parse -> (#directive | reduce+print). (§7)
    pub fn eval_cell(&mut self, src: &str) -> CellResult;
}

pub enum CellResult { Value(String), Directive(String), Error(String) }
```

`eval_cell` is literally:

```rust
match self.parse(src)? {
    d if is_directive(&d) => self.run_directive(d),           // §7
    x => CellResult::Value(self.show(&self.reduce(&x)?, /*full=*/ false)),
}
```

Everything else (`/lisp` page, `cov lisp` CLI, Python, JS) calls `eval_cell` (or the
finer `parse`/`reduce`/`show` triple). **No REPL logic lives outside these methods.**

---

## 4. Evaluation — the Forth-style dictionary/numeral/builtin split

This is the heart, and the place "how do we handle numerals" is decided. Evaluating an
**atom** (or the head of a list) resolves it in exactly Forth's order:

```rust
enum Resolved<'a> { Word(&'a Word), Literal(Literal), Unbound }

fn resolve(&self, sym: &Symbol) -> Resolved {
    if let Some(w) = self.dict.lookup(sym)          { Resolved::Word(w) }      // 1. dictionary
    else if let Some(l) = self.nums.read_numeral(sym) { Resolved::Literal(l) } // 2. numeral fallback
    else                                            { Resolved::Unbound }      // 3. error
}
```

backed by two swappable traits — **the numeral policy is one trait impl**:

```rust
/// Symbol -> bound word (builtin or user def). Forth's dictionary.
pub trait Dictionary { fn lookup(&self, sym: &Symbol) -> Option<&Word>; }

/// The FALLBACK: try to read an atom as a numeric literal. THE numeral decision —
/// swap this to choose bin/oct/dec/hex/LEB128/… (atoms.md literal zoo). Minimal:
/// decimal `nat` only; `0x…`/`0b…` are a drop-in richer impl, no eval change.
pub trait NumeralReader { fn read_numeral(&self, sym: &Symbol) -> Option<Literal>; }
```

A **word** is a builtin that produces a reduction theorem for its application:

```rust
pub struct Word { pub name: Symbol, pub arity: Arity, pub rule: WordRule }
pub enum WordRule {
    /// ⊢ (name args…) = result, given each arg's reduction theorem.
    Builtin(fn(&mut Kernel, &[Thm]) -> Result<Thm, EvalError>),
    /// a user-named reduction/definition (#name, §7): unfolds to a stored rhs.
    Defined(Thm),
}
```

**Minimal builtin set** (over `sexpr`, reusing `init/lisp.rs`): `cons`, `car`,
`cdr`, `atom?`, `eq`, `nil`, `+` on `nat` literals, and **`amb`** — the nondeterministic
choice operator (two/three intro rules for `Reduces`), which showcases *why* the return
type is a relation (one input, several witnessed outputs; `:next` enumerates). Each
deterministic builtin is one existing kernel reduction rule; `amb` is pure relation
structure, no state.

---

## 5. `reduce` = evaluate-as-theorem, concretely

`reduce(x): SExpr -> Thm` discharges `⊢ Reduces (state, x) (state', output)` from the
`Reduces` relation's introduction rules — bottom-up, congruence-glued so the whole result
is one theorem. Where reduction is deterministic and state is unchanged, this reads off as
`⊢ x = output` (the equational special case):

1. **Atom** `a`: `resolve(a)` → `Literal l` ⇒ `⊢ (s,a) ~~> (s, ⟨l⟩)` (reflexivity of the
   relation on the lowered literal); nullary `Word` ⇒ its intro rule; `Unbound` ⇒ `Error`.
2. **List** `(f a₁ … aₙ)`:
   a. `reduce` each `aᵢ` → `⊢ (s,aᵢ) ~~> (s, nfᵢ)`.
   b. `resolve(f)` → `Word w` (head must be a word; else error).
   c. `w.rule(nf₁…nfₙ)` → the head intro rule `⊢ (s,(f nf₁ … nfₙ)) ~~> (s', nf)`.
   d. glue: **congruence + transitivity of `Reduces`** ⇒ `⊢ (s,(f a₁…aₙ)) ~~> (s', nf)`.
   e. **`amb`**: step (c) has *several* intro rules; each yields a distinct witness
      `⊢ (s,(amb x y)) ~~> (s, x)` / `… (s, y)`. `reduce` returns one; the search resumes
      for `:next` (a lazy stream of derivations — the async-prover `Env` is the first
      consumer).

Deterministic reduction uses `refl`/`cong`/`trans`-flavored lemmas of `Reduces` + the
builtin δ/computation rules (all in `covalence-hol-api` / `init/lisp.rs`). `output` is a
real HOL term; `show(t,false)` = `prettyprint(output_sexpr)` under `state'` (§5.2).
**Zero new TCB** — `reduce` only *composes* existing kernel rules and the inductively
defined `Reduces`/`Parses` relations; soundness is the kernel's.

Lowering `SExpr → Term` (operands) reuses the Haskell path's `HolBackend` (S-expr →
`sexpr` term). The REPL is untrusted; the `Thm` it returns is the trust boundary.

### 5.1. `state` — an extensible world (only `defs` live now)

`state` is a record threaded through `Reduces` (and consulted by `Parses`):

```rust
pub struct State { pub defs: Dictionary, /* later: */ pub kv: (), pub log: () }
```

Minimal keeps only `defs` (extended by `#name`/`Defined` words); `kv` (a mutable
store/heap → `set!`), `log` (a print accumulator → `(print x)` appends, and
`output_string` side-output derives from it) are **empty hooks** so effectful rules slot in
without re-typing the relation. Nondeterminism (`amb`) is orthogonal to state — you get
either or both independently.

### 5.2. Stateful printing (macro abbreviation)

`prettyprint` is a *section of `Parses` under the current state*: it may render a value with
any string the reader would accept back. So after `#name two (cons 1 (cons 2 nil))`, the
printer may show that value as `two` (a valid rendering under `defs`), certified by Thm 3
(`⊢ Parses state_out "two" (cons 1 (cons 2 nil))`). Minimal ships the plain canonical
printer with the *hook* for abbreviation; because Thm 1 and Thm 3 share one `Parses`
relation, any abbreviation the printer uses is one the reader accepts — they can't drift.

---

## 6. Dialects = a bundle (one for the demo, hook for the rest)

A dialect bundles the swappable pieces — this is the seam `#dialect` flips
(`lisp-dialects-and-order.md`):

```rust
pub struct Dialect {
    pub reader:  Box<dyn Reader>,
    pub printer: Box<dyn Printer>,
    pub dict:    Box<dyn Dictionary>,     // builtin set
    pub nums:    Box<dyn NumeralReader>,  // numeral policy
}
```

**Minimal ships exactly one**: `sector` (McCarthy core + `+`, decimal nats). `#dialect`
exists and switches the active bundle; with one dialect it's a no-op-with-ack, but the
*hook is real* so adding `scheme`/`acl2`/`forsp` later is "register another `Dialect`,"
not a refactor.

---

## 7. `#`-directives — instructing the runtime itself

The reader tags a top form as a **directive** iff its head is an `Atom` starting with `#`.
Directives are dispatched to the runtime, *not* evaluated as terms. Extensible registry:

```rust
pub trait Directive {
    fn name(&self) -> &str;                                   // e.g. "prove", "dialect"
    fn run(&self, s: &mut Session, args: &[SExpr]) -> CellResult;
}
```

**Minimal directive set** (each a hook; some are stubs-with-ack, all wired):

| directive | minimal behavior | later |
|---|---|---|
| `#help` | list directives | — |
| `#dialect NAME` | switch `Dialect` bundle (ack; one dialect now) | scheme/acl2/forsp/forth |
| `#prove (== LHS RHS)` | `reduce` both; if outputs equal ⇒ `⊢ (s,LHS) ~~> (s,·)` ∧ `~~> (s,RHS)` share a normal form (refl-only), else `HOLE` | scripts / tactics / linker |
| `#name ID EXPR` | `reduce EXPR`, bind `ID ↦ Defined(thm)` in `state.defs` (**name a reduction**; enables print-abbreviation §5.2) | proper defs, measures |
| `#show EXPR` | `reduce` then `show(_, full=true)` — print `⊢ (s,EXPR) ~~> (s',out)` | `:trace`, `:next` |
| **content-addressing (runtime-only, §8)** | | *internalize into HOL later* |
| `#hash EXPR` | print `H(prettyprint(EXPR))` | Merkle-cons, kernel `Hash<h>` cert |
| `#store ID EXPR` | put `prettyprint(EXPR)` in the CA store; bind `ID ↦ hash` | `cov:store` blob ABI |
| `#ref HASH` | look the hash up in the CA store, print the S-expr | deref-with-recheck |

`#prove` minimal = **refl-only**: it certifies exactly the equalities both sides reduce to
a common normal form (real theorems, honestly limited). `HOLE` when they don't — never a
false `⊢`. That keeps "evaluated as a theorem" honest at the proving layer too.

---

## 8. Content-addressing — runtime-only for now (per current direction)

Explicitly scoped: **the demo does content-addressing *only* through the runtime
`#`-directives above** (`#hash`/`#store`/`#ref`), i.e. **tier 1** of
[`../initial-ideas/content-addressing-sexpr.md`](../initial-ideas/content-addressing-sexpr.md)
— hash the *printed* S-expr, keep a `Map<Hash, String>` in the `Session`. It is pure
sharing/naming: **nothing downstream trusts a hash**, so it's zero-TCB and needs no
kernel change. Internalizing into HOL (the `Hash<h>` certificate, Merkle-cons, `cov:store`)
is **deliberately deferred** — the directives are the seam we promote through *later*. The
`Session` owns the store so the state is per-session; the hash function reuses the kernel's
`O256`/BLAKE3 namespace so tier-1 hashes already agree with future kernel hashes.

---

## 9. Bindings — one API, three faces

The `Session` API (§3) is the single source; each binding is thin and mirrors it exactly.

- **Rust** — `covalence-lisp::Session` (native, the source of truth). Also a `cov lisp`
  CLI subcommand: a readline loop over `eval_cell`.
- **WASM/WIT** — [`lisp.wit`](./lisp.wit) (`cov:lisp@0.1.0`) mirrors `Session` as a
  `resource` with `parse`/`prettyprint`/`reduce`/`show`/`eval-cell`. For the **immediate**
  `/lisp` demo, wire it through the existing `covalence-web-kernel` (wasm32-unknown-unknown
  + wasm-bindgen — browser-kernel-async-decision) by adding one export
  `lisp_eval_cell(session, src) -> cell_result`; the WIT is the forward contract that
  **jco** transpiles to JS later (jco-load-pattern) so the browser converges on the same
  interface. (Two WASM paths, one API: wasm-bindgen now, component/WIT next.)
- **Python** — a `pyo3`/maturin shim (`build:python`) wrapping the *same* `Session`:
  `class Session: parse/reduce/prettyprint/show/eval_cell`. Direct native call, no WASM in
  the loop — the fast path and the API-quality ratchet (sketch-separation-thoughts.md).
- **JavaScript** — falls out of the WIT via jco; until then the `/lisp` page calls the
  wasm-bindgen `lisp_eval_cell` directly.

The web page holds one `session` handle (state persists across lines, so `#dialect`,
`#name`, `#store` stick) and calls `eval_cell` per submit.

---

## 10. The `/lisp` web endpoint

Parallel to `/haskell`:

- **SvelteKit route** `src/routes/lisp/+page.svelte`: a REPL pane — input box + transcript.
  On submit: `session.eval_cell(input)`; render `Value` as a result line, `Directive` as a
  muted ack line, `Error` in red. A one-time `session = new Session()` on mount.
- **wasm glue**: `covalence-web-kernel` gains `lisp_eval_cell` (+ a session handle export),
  built into the existing wasm bundle exactly like `haskell_to_sexpr`.
- **transcript target** (what "end-to-end" means):

```text
λ> (car (cons 1 2))
1
λ> (cons 1 (cons 2 nil))
(1 2)
λ> #show (car (cons 1 2))
⊢ (defs, (car (cons 1 2))) ~~> (defs, 1)
λ> (+ 1 (amb 10 20))          ; nondeterminism, no state — the relation has two witnesses
11                            ; ⊢ (defs, (+ 1 (amb 10 20))) ~~> (defs, 11)
λ> :next
21                            ; ⊢ (defs, (+ 1 (amb 10 20))) ~~> (defs, 21)
λ> #name two (cons 1 (cons 2 nil))
two := (1 2)                  ; extends defs (state); printer may now abbreviate as `two`
λ> (car two)
1
λ> #prove (== (car (cons 1 2)) 1)
⊢ (defs, (car (cons 1 2))) ~~> (defs, 1)     ; refl-only: both sides share a normal form
λ> #hash (cons 1 2)
#9f3ac1…
λ> #store p (cons 1 2)
p := #9f3ac1…
λ> #ref #9f3ac1…
(cons 1 2)                    ; runtime CA store deref prints the stored S-expr
λ> #dialect scheme
dialect: scheme (not yet registered — using sector)
```

Every printed value line is backed by a real `⊢ (state, input) ~~> (state', output)`
reduction theorem (with `Parses` theorems bracketing it, §0); `#show`/`:next`/`#trace`
expose them.

---

## 11. Build order (step by step)

- **M0 — IR + parse/print.** `covalence-lisp` crate; `SExpr`; `Reader`/`Printer` traits +
  the sector impls; `Session::{parse, prettyprint}`. Test: round-trip.
- **M1 — Forth split.** `Dictionary` + `NumeralReader` traits; `resolve`; the minimal
  builtin words (`cons/car/cdr/atom?/eq/+` + `amb`) + decimal `NumeralReader`. `State` with
  `defs` live. Not yet kernel-glued.
- **M2 — reduce = evaluate-as-theorem (the `Reduces` relation).** `Session::reduce`/`show`:
  lower via `HolBackend`, discharge `⊢ Reduces (s,input) (s',output)` bottom-up
  (cong/trans lemmas of `Reduces` + `init/lisp.rs` rules); `amb` = multi-witness + `next`.
  Test: `⊢ (defs,(car (cons 1 2))) ~~> (defs,1)`; `amb` yields ≥2 distinct witnesses;
  never-false; hyps-free.
- **M3 — directives + session state.** `Directive` trait + registry; `#help/#dialect/
  #prove(refl)/#name/#show` and the content-addressing trio `#hash/#store/#ref` (runtime
  store). `eval_cell` complete.
- **M4 — WIT + web.** `lisp.wit`; `covalence-web-kernel::lisp_eval_cell`; the `/lisp`
  SvelteKit page. **This is the end-to-end demo.**
- **M5 — Python.** pyo3 `Session` shim; a `cov lisp` CLI loop. (JS-via-jco: post-minimal,
  the WIT is already the contract.)

M0–M4 is the whole ask: type an S-expr → `⊢ input = value` → printed, in the browser, on a
high-level API that's already a WIT contract, with every hook (dialects, proving, naming,
content-addressing) present as a live `#`-directive.

---

## 12. Open questions (small, for us)

- **Numeral minimal scope** — decimal `nat` only for M1, or ship `0x`/`0b` immediately
  (it's just a richer `NumeralReader`, no eval change)? I lean decimal-only, note the seam.
- **`#prove` beyond refl** — keep it refl-only for the demo (honest, tiny) and route real
  proofs through the linker post-minimal? (Yes, I think.)
- **Session in wasm** — one JS-held `session` resource (WIT-native), or a module-global in
  the wasm-bindgen build until jco lands? (Global now, resource with jco.)
- **`show` default** — print `rhs` only (cleaner) with `#show` for the full equation, or
  always show `⊢ lhs = rhs`? (rhs-only default; the theorem is one keystroke away.)
