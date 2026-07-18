+++
id = "N0024"
status = "draft"
review = "unreviewed"

[[contributions]]
role = "author"
actor = "agent:claude"
at = "2026-07-13T20:42:09+01:00"
source = "legacy"
agent = "claude"
harness = "claude"
+++

# Minimal Lisp → metacircular interpreter in the browser: step-by-step plan

> **STATUS (branch `lisp-demo`):** the first build has landed — see
> [`../STATUS.md`](../STATUS.md). What ships is the **equational special case**
> covering Little Schemer **ch1** (Phases 0–1, a ch1 slice of 2–3, and 5's
> wasm+`/lisp` wiring). The metacircular-interpreter target below — ch2 recursion
> (`defun`/env/recursor), the `Reduces` step-relation for non-termination, and
> the differential harness — is **deferred**; the parametric refactor in
> [`../initial-ideas/parametric-reduction.md`](../initial-ideas/parametric-reduction.md)
> supersedes the single-seam design.

Target: the `/lisp` web page boots a REPL in which the **metacircular interpreter runs** —
you type `(eval '(car (cons 1 2)) env)` and get `1` back, every result a kernel reduction
theorem. Same path is exercised by **integration tests** (the metacircular interpreter is
one). APIs stack **`Repl` ≤ `SExprRepl` ≤ `Lisp`**; the `Lisp` layer owns a `Resolve`
function (symbols / numbers / strings), so a numeral like `1342` can become a HOL binary
numeral `double (succ …)` *or* an internal Lisp binary numeral — by swapping one impl.

Not committed. Companion to [`README.md`](./README.md) (the spec) and
[`../initial-ideas/`](../initial-ideas/).

## The stack

```
covalence-repl    (crates/lib/repl)    — the generic Repl trait. no deps, wasm-clean.
     ▲
covalence-lisp::sexpr                  — SExprRepl: Term built from sexp EVENTS + the Resolve trait
     ▲                                   (deps: covalence-repl, covalence-sexp)
covalence-lisp::lisp                   — the Lisp: Resolve impls, builtins, Reduces relation, dialect
     ▲                                   (dep: covalence-hol-api, feature `hol`)
covalence-web-kernel + /lisp page      — wasm entry + SvelteKit REPL
```

(Three logical layers; `sexpr`/`lisp` are modules of `covalence-lisp` to start — split into
`covalence-sexpr-repl` later if a second S-expr language wants the middle layer.)

---

## Phase 0 — `covalence-repl`: the generic trait

**Do:** new crate `crates/lib/repl`. The `Repl` + `ReplStep` traits exactly as in
[`../initial-ideas/generic-repl-trait.md`](../initial-ideas/generic-repl-trait.md):
assoc `State`/`Term`/`Eval`, errors `StartError`/`ParseError`/`EvalError`, methods
`start`/`parse`/`eval`/`next`/`show`, default `step = parse;eval;show`. No dependencies,
`#![forbid(unsafe_code)]`, compiles to `wasm32-unknown-unknown`.

**Test (proves the trait is usable in isolation):** an `EchoRepl` with `Term = Eval =
String`, `State = ()` — `step("hi") == "hi"`. Confirms the lifecycle + `step` default.

**DoN:** `cargo test -p covalence-repl` green; wasm target builds.

---

## Phase 1 — `covalence-lisp::sexpr`: Term from events + `Resolve`

**Do:** new crate `crates/lang/lisp`, module `sexpr`.

1. The `Resolve` trait — the atom-classification seam the `Lisp` layer fills:
   ```rust
   pub trait Resolve {
       type Term;
       fn resolve_symbol(&self, s: &str) -> Self::Term;
       fn resolve_number(&self, s: &str) -> Option<Self::Term>;   // None ⇒ not a numeral
       fn resolve_string(&self, format: &str, bytes: &[u8]) -> Self::Term;
   }
   ```
2. `SExprRepl: Repl` + a `TermBuilder<R: Resolve>` implementing
   `covalence_sexp::SExpBuilder` with `Output = R::Term`, folding events straight to terms
   — **the Forth split lives in `build_atom`** (dictionary is part of `Resolve` at the Lisp
   layer; here `build_atom` = `resolve_symbol`-or-`resolve_number`):
   ```rust
   fn build_atom(&mut self, text: &str) -> R::Term {
       self.r.resolve_number(text).unwrap_or_else(|| self.r.resolve_symbol(text))
   }
   fn build_list(&mut self, kids: Vec<R::Term>) -> R::Term { (self.mk_app)(kids) }
   ```
3. Default `parse` = `covalence_sexp::parse_with(src, &mut TreeBuilder::new(builder,
   dialect))` → `assemble(into_results())`. **No `SExpr` tree is materialized.**

**Test:** a `SexprEcho` where `R::Term = String` and `resolve_*` just format — parse
`(a (b c))` via events, assemble, print, assert round-trip. Assert (with a counter in
`Resolve`) that `resolve_*` fires per atom and no `covalence_sexp::SExpr` is built.

**DoN:** `cargo test -p covalence-lisp` green (module `sexpr`); wasm builds.

---

## Phase 2 — `covalence-lisp::lisp`: the interpreter (TestLisp, no kernel yet)

This is where "a Lisp" becomes concrete and where the metacircular interpreter first runs
— all in fast native Rust, no kernel, so it's cheap to get right.

**Do:**

1. **Value/AST** — `enum Val { Sym(Symbol), Num(BinNat), Str(…), Nil, Cons(Rc<Val>,
   Rc<Val>), Closure(…) }`. `BinNat` = an **internal binary numeral** (the "represent 1342
   as internal binary numerals" option — a `Vec<bit>`/bignum, not `succ`-unary).
2. **`Resolve for TestLisp`** — `resolve_number` parses decimal→`BinNat` (the numeral
   policy; swap for bin/hex later), `resolve_symbol` → `Sym`, `resolve_string` → `Str`.
3. **`Dictionary` + builtins** — `cons car cdr atom eq cond quote lambda label`, `+` on
   `BinNat`, and `amb` (nondeterministic — `eval` returns the first witness + a resumable
   thunk for `next`).
4. **`eval`** — the McCarthy evaluator over `Val` + an assoc-list env. Special forms
   (`quote/cond/lambda/label`), application (eval head, eval args, apply closure/builtin).
   `impl Repl for TestLisp` with `Eval = Val` (+ the `next` stream for `amb`).

**Tests (integration, via the REPL surface — `step`):**
- `(car (cons 1 2))` → `1`; `(cdr (cons 1 2))` → `2`; `(eq 'a 'a)` → `t`.
- `(+ 21 21)` → `42` (exercises `BinNat`).
- `amb`: `(+ 1 (amb 10 20))` → `11`, `next` → `21`.
- **THE metacircular test** — load [`metacircular.lisp`](#metacircularlisp) defining `eval`/
  `apply`/`assoc`/`evcon`/`evlis`/`pair`/`append` in Lisp, then run through the *host*
  interpreter:
  ```
  (eval '(car (cons 1 2)) nil)                 ⇒ 1
  (eval '((lambda (x) (cons x x)) 7) nil)      ⇒ (7 . 7)
  (eval '(cond ((eq 1 1) 'yes) (t 'no)) nil)   ⇒ yes
  ```
  i.e. the Lisp-defined `eval` computes the same answers as the host `eval` — the
  metacircular fixpoint, as a passing test.

**DoN:** `cargo test -p covalence-lisp` green incl. the metacircular test; the REPL runs a
real (nondeterministic) Lisp with internal binary numerals — **no kernel yet**.

---

## Phase 3 — kernel bridge: evaluate-as-theorem

Now `Eval` becomes the reduction **theorem** and numbers can become **HOL** binary
numerals — the second `Resolve` option — without touching phases 0–2's structure.

**Do (feature `hol`, dep `covalence-hol-api`):**

1. **`HolResolve`** — `resolve_number("1342")` → the `sexpr` HOL term for 1342 as a
   *binary* numeral (`double (succ …)` style, reusing the nat literal path), `resolve_symbol`
   → the HOL symbol term. Same `Resolve` trait, different `Term = hol::Term`. This is the
   "1342 as `double (succ n)` in HOL *or* internal" switch — it's literally `TestLisp` vs
   `HolResolve` as the `Resolve` impl.
2. **`CertifiedLisp`** — `impl Repl` with `Eval = Thm` of `⊢ Reduces (state,input)
   (state',output)`; `eval` discharges membership of the `Reduces` relation from its intro
   rules (bottom-up cong/trans + the `init/lisp.rs` builtin rules; §README §5).
3. **Differential harness** — run each test input through both `TestLisp` and
   `CertifiedLisp`; assert the `Val` and the theorem's `output` agree (the runtime = logic
   check, `reduction-relations-and-state.md`).

**Tests:**
- `⊢ (defs,(car (cons 1 2))) ~~> (defs,1)`; hyps-free; never-false.
- **metacircular, certified** — the same three metacircular runs from Phase 2, now each
  returning a `Thm`; differential-agree with TestLisp.

**DoN:** `cargo test -p covalence-lisp --features hol` green; differential harness green;
zero new TCB (only composes existing kernel rules).

---

## Phase 4 — directives + session state

**Do:** `State = { defs, kv:(), log:() }`; the `#`-directive registry
(`#help/#dialect/#prove/#name/#show` + runtime-only `#hash/#store/#ref`, §README §7–§8);
`eval_cell = #directive-precheck else step`. `#name` extends `state.defs`; the content-
address store is a `Map<Hash,String>` in `State`.

**Test:** `#name two (cons 1 (cons 2 nil))` then `(car two)` → `1`; `#hash`/`#store`/`#ref`
round-trip; `#prove (== (car (cons 1 2)) 1)` → a real `Thm`.

**DoN:** `cargo test -p covalence-lisp --features hol` green; all directives wired.

---

## Phase 5 — WASM + `/lisp` web page (the boot target)

**Do:**

1. **`covalence-web-kernel`** gains `lisp_new_session() -> handle` + `lisp_eval_cell(handle,
   src) -> CellResult` (wasm-bindgen, mirroring `haskell_to_sexpr`; the `lisp.wit` contract
   is the forward interface for jco).
2. **`/lisp` SvelteKit route** (`src/routes/lisp/+page.svelte`) parallel to `/haskell`:
   input box + transcript, one `session` on mount, `eval_cell` per submit.
3. **Preload** the metacircular interpreter definitions into the fresh session (or a
   `#load metacircular` directive) so the page **boots into a REPL where `eval` is already
   defined** — the "boots up to the metacircular interpreter" milestone.

**Test (web integration):** a headless check that `lisp_eval_cell(s, "(eval '(car (cons 1
2)) nil)")` returns `1` through the wasm boundary; the `/lisp` page renders a result line.

**DoN:** `bun run build` clean; `/lisp` loads; typing the metacircular `eval` call returns
`1` in the browser, backed by a `Thm`.

---

## Phase 6 — Python (follow-on)

pyo3 `Session` shim over the same trait surface (`start/parse/eval/show/step`); `cov lisp`
CLI loop. JS-via-jco from `lisp.wit` later. Not on the critical path to the boot target.

---

## `metacircular.lisp`

The classic McCarthy evaluator, minimal, used by the Phase 2/3/5 tests and preloaded in
Phase 5. Needs only the Phase-2 builtins:

```lisp
(label assoc (lambda (k a)
  (cond ((eq (car (car a)) k) (car (cdr (car a))))
        (t (assoc k (cdr a))))))

(label evlis (lambda (m a)
  (cond ((eq m nil) nil)
        (t (cons (eval (car m) a) (evlis (cdr m) a))))))

(label evcon (lambda (c a)
  (cond ((eval (car (car c)) a) (eval (car (cdr (car c))) a))
        (t (evcon (cdr c) a)))))

(label pair (lambda (ks vs)
  (cond ((eq ks nil) nil)
        (t (cons (cons (car ks) (cons (car vs) nil))
                 (pair (cdr ks) (cdr vs)))))))

(label eval (lambda (e a)
  (cond
    ((atom e) (assoc e a))
    ((atom (car e))
     (cond ((eq (car e) (quote quote)) (car (cdr e)))
           ((eq (car e) (quote atom))  (atom (eval (car (cdr e)) a)))
           ((eq (car e) (quote eq))    (eq   (eval (car (cdr e)) a) (eval (car (cdr (cdr e))) a)))
           ((eq (car e) (quote car))   (car  (eval (car (cdr e)) a)))
           ((eq (car e) (quote cdr))   (cdr  (eval (car (cdr e)) a)))
           ((eq (car e) (quote cons))  (cons (eval (car (cdr e)) a) (eval (car (cdr (cdr e))) a)))
           ((eq (car e) (quote cond))  (evcon (cdr e) a))
           (t (eval (cons (assoc (car e) a) (cdr e)) a))))
    ((eq (car (car e)) (quote lambda))
     (eval (car (cdr (cdr (car e))))
           (append (pair (car (cdr (car e))) (evlis (cdr e) a)) a))))))
```

(`append` is a Phase-2 builtin. `'x` sugar optional — `(quote x)` works. When this `eval`
computes the same results as the host evaluator, the metacircular loop is closed — the
central integration test and the browser boot target.)

---

## What each phase buys (why this order)

- **0–1**: the trait stack + the zero-alloc event reader, tested with trivial impls — the
  reusable spine, no Lisp semantics yet.
- **2**: a **real running Lisp** with the metacircular interpreter, fast and kernel-free —
  the semantics are correct *before* the kernel is involved.
- **3**: the *same* interpreter now emits **theorems**, and the `Resolve` swap gives HOL
  binary numerals — the evaluate-as-theorem payoff, differential-checked against Phase 2.
- **4–5**: directives + the **browser boot to the metacircular interpreter** — the deliverable.

The critical path to the demo is **0→1→2→3→5** (Phase 4 directives can trail; Phase 6 is
off-path). The metacircular interpreter is a passing test from Phase 2 on, so the headline
demo is continuously verified, not a big-bang at the end.
