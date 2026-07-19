+++
id = "N0025"
status = "draft"
review = "unreviewed"

[[contributions]]
role = "author"
actor = "agent:claude"
at = "2026-07-16T00:22:16+01:00"
source = "legacy"
agent = "claude"
harness = "claude"
+++

# Relational recursion: β/λ and δ/`defun` in the `Step` relation

*Agent design note, 2026-07-15. Status: DESIGN ONLY — not implemented. The
open-work pointer lives in `crates/lang/lisp/SKELETONS.md`.*

The default `/lisp` dialect drives the genuine small-step relation
(`crates/lang/lisp/src/relation.rs`): `Step`/`Reduces` are defined on the
kernel's binary inductive-relation engine (`metalogic::binary::RuleSet2`), and
every printed value is read off a hypothesis-free `⊢ Reduces input value`.
Function definitions (`defun`/`define`/`lambda`) are **honestly rejected**
today (a clean error pointing at `#lang scheme`). This note sketches the path
to native relational recursion, following the template the congruence and
integer clauses already established.

## What exists to build on

- **Congruence clauses with a `Premise::Derivation`** — the unary elimination
  contexts (clauses 12–16) and the int-operand pairs (25–34) show how a
  premise-carrying clause is stated (`∀…. Step a a' ⟹ Step (K a) (K a')`) and
  fired by the driver (`derive_mixed` with word args + one `Derivation`).
- **Computation-backed redex clauses** — the int clauses (20–24) state a
  generic `∀a b. Step (op (int a)(int b)) (TARGET a b)` and let the driver
  normalise `TARGET` with *kernel* equations (`TermExt::reduce`); no fact is
  asserted, only proved.
- **defun-as-hypothesis** — the `scheme` dialect (`defs.rs`/`semantics.rs`)
  already installs `f = (λ…)` as an assumed kernel equation that rides result
  theorems as a hypothesis, never an axiom.

## The plan, in two strata

### 1. β for a *fixed* body: one clause schema per `defun` (δ-style)

The cheap, sound first step is **δ/`defun` via per-definition clauses**, not a
general β. When the user enters `(defun f (x) body)`:

1. Compile `body` with `x` free, exactly as `scheme` does, but into the
   *relational* sexpr carrier (predicates already return sexpr `t`/`nil`
   there, so the bool/data type split that plagues `scheme` mostly dissolves).
2. Extend the session's `Step` `RuleSet2` with **one clause schema**
   `∀x. Step (f x) body[x]` — a base clause, no premise, in the same shape as
   the cond clauses (the substitution is the engine's ordinary ∀-instantiation,
   so nothing new is trusted).
3. Add the matching **argument congruence** pair for `f`'s application
   position, cloning the int-op congruence template.

Consequences to design around:

- **The rule set becomes session-state.** Today `step_rule_set()` is rebuilt
  from `&self` per call; the dialect would carry a `Vec` of user clause
  builders (name, params, compiled body) and append them after clause 34.
  Clause indices stay stable per session snapshot; `#lang` reset drops them.
- **Recursion = the clause fires again.** `(f (f x))` needs no fixpoint
  machinery: each unfolding is one more `Step`, and `Reduces` chains them.
  Non-termination is already handled by fuel + the honesty guard (a clean
  "ran out of fuel" error, never a printed non-value).
- **Soundness/honesty:** the clause is part of the *defined* relation, so
  `⊢ Reduces` stays hypothesis-free — but the relation itself now depends on
  user input. That is fine (it is still a genuine theorem about *that*
  relation), but the REPL should say which relation it proved membership in
  (e.g. `#show` printing the clause set version). Alternatively, keep the
  defun equation as a `Premise::Side` hypothesis so the theorem shape matches
  `scheme`'s "rides as a hypothesis" story; that needs the engine to accept a
  side-condition equation, which `derive_mixed` already supports.

### 2. General β/λ: `Step ((λx. b) a) b[a/x]`

A first-class λ needs the *object-level* λ in the sexpr carrier (a `lam` code
constructor + an environment or substitution function), i.e. the deep-embedding
route (cf. `lambda_iter` in covalence-init). That is a real project: closures,
capture-avoiding substitution as a carved function, and decrease laws for the
decoder. Do it only after (1) proves out; (1) covers the Little Schemer corpus.

## Order of work

1. Session-held clause extensions (defun → clause schema + congruence pair).
2. `try_define` in the relational arms of `session.rs` (mirroring `scheme`).
3. Fuel/guard already done; `#show` clause-set provenance note.
4. Metatheorems (`Step` determinism, `sector ⊑ sector+int ⊑ sector+int+defs`)
   via `rule_induction2`, once clause sets are session-versioned.
