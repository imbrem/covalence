# The ACL2 dialect — slice 1 (agent-authored)

`crates/lang/lisp/src/acl2.rs` — the first slice of the tower's ACL2 layer: an
honest, applicative, first-order Lisp with ACL2 spellings, a *stated* (not
proved) admissibility discipline for `defun`, and a `defthm` that only mints
what the kernel actually proves. Standalone `Acl2Session` (mirrors
`session::Session`'s `eval_cell`/`render` shape), wired into the `#lang`
dispatch as `Lang::Acl2` (`#lang acl2`; a `Session` holds an `Acl2Session`
sub-session, reset like `defs` on every `#lang` switch).

## What's in this slice

- **Primitives**: `car cdr cons`, `consp atom endp`, ternary `if` (no `cond`),
  `equal`, and integers `+ - * <= = zp natp`. All are surface translations
  onto the value semantics (`LispSemantics`): `endp → null?`, `atom → atom?`,
  `zp n → (<= n 0)`, `natp n → (<= 0 n)`, `equal →` integer `=` when a side is
  syntactically arithmetic, else `eq?`. Integers ride the semantics'
  `IntBackend` integration (typed kernel `int` terms; reductions are
  kernel-proved computation equations).
- **`defun`** installs the assumption `{f = λ…} ⊢ f = λ…` (`crate::defs`,
  never an axiom); return type is inferred by attempt (`bool`, then `sexpr`,
  then `int` — so `len`-style integer-valued recursion works).
- **`defthm`** proves ground goals by driving the certified reduction to a
  `bool` literal and applying `eqt_elim`: `hyps ⊢ goal`, where `hyps` are
  exactly the `defun` equations unfolded (empty for pure arithmetic).
- **Honesty**: every printed value is the RHS of the backing kernel theorem
  (`Acl2Outcome::thm`); everything unprovable is a clean `Err`.

## The admissibility criterion (exactly)

`(defun f (x₁ … xₙ) body)` is admitted iff (1) every head in `body` is a
primitive, an already-admitted `defun`, or `f`, at the right arity (definition
before use, no forward refs); (2) every atom is `t`/`nil`/a numeral/a formal;
and (3) there is a formal position `i` such that **every** recursive call
passes a non-empty `car`/`cdr` chain of `xᵢ` in position `i`.

This is a **syntactic discipline, not a termination proof** — no measures, no
ε₀ ordinals, and the `endp`/`consp` guard is not verified (kernel `cdr snil =
snil`, so an unguarded "structural" recursion still diverges — caught by the
fuel-bounded driver, never a hang). Soundness never rests on admission:
definitions are hypotheses, so a wrongly-admitted `defun` cannot produce a
hypothesis-free falsehood.

## The defthm story + induction roadmap

Slice 1 = the ground/decidable fragment (ACL2's "evaluation" leg). A goal with
free variables is a universal claim; the honest slice **rejects** it with a
message naming induction as the missing piece. Roadmap:

1. **Structural induction on `sexpr`** — the carved datatype's induction
   theorem instantiated per `defthm` goal, with base/step subgoals discharged
   by the same certified reduction (symbolic evaluation on the open term where
   possible).
2. **Measure-based admission** — replace criterion (3) with a user-suppliable
   measure + a kernel proof of decrease (ACL2's definitional principle); turns
   the defun hypothesis into a genuine conservative definition.
3. **The-method loop** — simplification (rewriting with proved `defthm`s)
   before induction, ACL2-style.

## Known limits (also in `crates/lang/lisp/SKELETONS.md`)

- `equal` decides: atoms (via the `eq?` leaf step, both ways), and composite
  values that reduce to **syntactically identical** terms (trans/sym +
  `eqt_intro`). Disequality of composites/bools is a clean error — needs the
  `scons` discrimination laws.
- Kernel ints are typed `int` terms, not sexpr data: mixed structures
  (`(cons 1 nil)`, integers passed to list formals) are rejected with a clear
  message. `equal`-routing is syntactic (a user call returning `int` compared
  against a non-arithmetic side routes to `eq?` and errors).
- Formals are always `sexpr`-typed; integer-*argument* functions are not
  expressible yet.
