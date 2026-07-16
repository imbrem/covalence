# covalence-lisp — SKELETONS

See [`notes/vibes/lisp/STATUS.md`](../../../notes/vibes/lisp/STATUS.md) for the
full picture.

## Severe

- **The full metacircular interpreter does not run yet.** The ground fragment
  (`quote`/`car`/`cdr`/`cons` dispatched by `eq?` on the operator symbol) runs
  and is certified (`tests/little_schemer_ch2.rs::metacircular_*`). Two gaps
  block the complete `metacircular.lisp`
  (`notes/vibes/lisp/minimal-spec/implementation-plan.md` §metacircular):
  1. **Truthy-data `cond` conditions.** Lisp `cond`/`if` test any non-`nil`
     value as true; the kernel `cond α c x y` needs a **`bool`** condition. So a
     clause like `evcon`'s `((eval (car (car c)) a) …)`, whose test is *data*,
     fails to type. Needs a data→bool coercion (a `truthy`/`null?`-style fold)
     applied to non-bool `cond` tests, or a Lisp-native `cond` over `sexpr`.
  2. **Polymorphic `eval` return + `assoc`/env + lambda-in-`eval`.** The plan's
     `eval` returns *data* on most branches but *bool* on the `atom`/`eq`
     branches, so it has no single HOL type; `assoc`/`pair`/`evlis` and the
     `((lambda …) …)` application path inside `eval` inherit that. Needs the
     data-as-boolean bridge above plus a uniform `sexpr` representation of
     `t`/`nil` (Lisp-level constants via the carved recursor) so predicates
     return data.
- **The REPL bypasses the `ReductionStrategy` seam** (legacy `hol.rs`).
  `Session`/`semantics.rs` now drive the parametric `Semantics<LispRepr>` +
  `RunToValue` seam directly, but the older one-shot `SymbolicStrategy`
  (`ReductionStrategy` in `hol.rs`) is unused except by `LispHol::eval` and its
  own tests. Fold it into the `Semantics` seam or retire it.

## Minor

- **ACL2 slice (`src/acl2.rs`) — open ends** (design + roadmap in
  [`notes/vibes/lisp/acl2-dialect.md`](../../../notes/vibes/lisp/acl2-dialect.md);
  the reified-certificate `defthm` path in `acl2-s0-s3-design.md` §9.5):
  - **No induction**: `defthm` accepts only ground decidable goals;
    universally quantified goals are rejected (in the REPL AND the `#book`
    pipeline — the fixture book's `app-assoc`/`len2-app` pin the rejection).
    The kernel-side S6 path exists (`covalence-init` `init/acl2`: `s6_env` +
    `derive_ind` + `hilbert::derive_under` + `transport_equal_open`, gate =
    app-assoc), but its base/step premises are hand-built per theorem
    (~150 bespoke `hilbert::Step`s for app-assoc). Wiring surface `defthm`s
    onto it needs a generic premise builder (an object-level simplifier:
    defun unfolding under `if-true`/`if-false`, `CongImpl` chains, IH
    splicing, per candidate induction variable) — see
    `notes/vibes/lisp/acl2-book-frontend.md` §5.
  - **Book pipeline (`src/book.rs`) — deliberately-lite slice** (design +
    tally semantics in `notes/vibes/lisp/acl2-book-frontend.md`): no `'x`
    reader macro / `#|…|#` comments (fixtures write `(quote …)`); no
    `encapsulate`/`defmacro`/`mutual-recursion` (rejected events); no
    `include-book :dir` directories; `local` is pass-1 only (installed,
    never undone at end-of-book); single package; `:rule-classes` recorded,
    never interpreted; best-effort (continues past rejections, unlike
    ACL2's fail-fast certification).
  - **Certificate fragment is narrower than the 11 PrimRow rows.** Ground
    `(equal L R)` defthms over quoted data / int literals /
    `car cdr cons consp equal +` go via `Derivable_ACL2` + soundness +
    `transport_equal`; `*`, unary `-`, `<`, `integerp`/`symbolp` (not surface
    ops), `consp` at atoms, and `equal` disequality beyond distinct int
    literals fall back to reduction — init's `Prims` exports no ground
    folding law for them (only `plus_lit`). Needs public
    `times_lit`/`neg_lit`/`lt_lit` + recognizer-at-payload laws in
    `init/acl2/prims.rs`, then extend `CertEngine::comp_cert` +
    `row_spelling`.
  - **Admissibility is syntactic, not a termination proof**: structural
    car/cdr-descent check only — no measures/ordinals, guard not verified
    (fuel bound catches divergence). Soundness rests on defun-as-hypothesis.
  - **`equal` cannot decide composite disequality** (equal-values and
    atom-disequality only); needs `scons` discrimination laws. `equal`
    int-vs-sexpr routing is syntactic (a user call returning `int` compared
    to a non-arithmetic side routes to `eq?` and errors).
  - **No int-typed formals** (params always `sexpr`; return type inferred
    bool/sexpr/int by attempt); mixed int/list data (`(cons 1 nil)`) rejected.
- **`relation.rs` reduction relation — next-phase clauses.** The `Step`/`Reduces`
  relations (on the binary engine, `src/relation.rs`) land the primitive fragment
  (car/cdr/cons, atom?/consp/null?, eq? on *equal* atoms, cond truthy/falsy
  select, unary-elimination congruence) and the **integer dialect** (`sector+int`:
  `Step (+ (int a)(int b)) (int a+b)` etc. for `+`/`-`/`*`/`<=`/`=`, the result
  proved via the kernel int-computation equation, plus left/right congruence into
  the int operands so nested arithmetic reduces; `int`/`nat` flavours behind the
  `int_backend::IntBackend` trait; `sector` leaves `(+ 2 2)` stuck). Deferred:
  **β/λ** (`Step ((λx.b) a) b[a/x]`) and **δ/`defun`** (`Step (f args) body[args]`
  via session-held clause schemas — design in
  `notes/vibes/lisp/relational-recursion.md`); **`eq?` on distinct atoms** (needs
  the blob-disequality clause) and congruence *into* `eq?` operands; **congruence
  into `cond` tests** (so a predicate result can drive a `cond`); and the
  metatheorems (`Step` determinism, `Reduces` = `Step*`, `sector ⊑ sector+int`
  inclusion) via `rule_induction2`. No `RelationalSemantics` `Semantics<LispRepr>`
  wrapper / `#semantics` toggle yet (driver is standalone
  `prove_step`/`prove_reduces`).

- **Relational recursion / more `#lang`s.** The `lisp`/`sector` dialects are the
  relation; `defun`/`lambda` recursion is **only** in `scheme` (the value
  semantics) because the `Step` relation lacks β/δ clauses — relationally these
  forms are a clean error pointing at `#lang scheme`. The implementation path
  (per-`defun` clause schemas + congruence pairs, then general β) is sketched in
  `notes/vibes/lisp/relational-recursion.md`. Future `#lang`s
  (`forsp`/`forth`/`haskell`) would slot into the same `session::Lang` dispatch.

- **`defun` return type is a 3-way guess; parameters are always `sexpr`.**
  `Session::install` tries `bool`, then `sexpr`, then `int` for a recursive
  function's head (predicates vs data vs counting functions like `len`).
  Mixed / higher-order returns are not installable, and **parameters are always
  `sexpr`-typed**, so `int`-parameter recursion (`(defun fact (n) …)`) does not
  compile — needs per-parameter type inference. No real Lisp type inference.
- **Value-semantics integers are typed `int` terms, not `sexpr` data.** Great
  for `(+ 2 2)`/`len` (kernel-proved, hyps-free equations), but `(cons 1 nil)`
  or an int passed to a list position is a compile-time "expects integer
  operands"/stuck error, not a heterogeneous list. A `sexpr` integer injection
  (the relational dialect's `(int n)`) with equational laws would unify them.
  Also: an `int`-typed `cond` with no matching clause falls through to the
  literal `0` (the typed stand-in for Lisp's `nil` default).
- **Forward references default to `sexpr… → sexpr`.** A call to a not-yet-defined
  function compiles a `sexpr`-returning free-variable head
  (`semantics.rs::forward_head_ty`), so mutual recursion only closes when the
  later `defun` also has a `sexpr` return of the same arity. A forward-referenced
  *predicate* (bool return) would not unify.
- **`carved → sexpr` rename pending.** The code still uses the `carved` jargon
  (`CarvedSExpr`, `carved()`); the plan is to rename to an `SExpr`-family that
  does not clash with `covalence_sexp::SExpr`, coordinated with the kernel.
- **`null?` is the `consp` complement** (`⊢ ¬ consp v`), correct on lists;
  `null?` of a non-nil *atom* answers `nil` rather than erroring as a strict
  list-only `null?` would.
- **`eq?` is atoms-only.** Both operands must reduce to `atom b` values; the
  step decides the closed blob (dis)equality via `atom` injectivity
  (`CarvedSExpr::inj_atom`) + congruence. `eq?` on lists (structural `sexpr`
  equality) is `Stuck` / future work.
- **Predicate/`eq?` values are `bool` literals, data values are `sexpr`.** See
  the metacircular gap (2): a uniform `sexpr`-valued `t`/`nil` (so predicates
  compose as data) would need Lisp-level `t`/`nil` constants.
- The aspirational `Reduces (state,input) (state',output)` *relation* (with
  `amb` nondeterminism + threaded state, streaming for non-terminating fns) is
  future work; today's `⊢ input = output` is its deterministic special case.
  Non-termination IS handled (fuel-bounded `drive_fueled` → `Status::Diverging`,
  never a hang), but only as the equational fragment.
- `resolve_number`/`resolve_string` numeral-vs-symbol split is cosmetic (both
  lower to raw-byte atoms); strings with whitespace/parens do not round-trip.
- The `#`-directive table has only `#help` / `#show` / `#lang`; extensible
  (`session::Directive`) but no `#defun` / `#load` / `#type`.
