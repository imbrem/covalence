+++
id = "N001F"
status = "draft"
review = "unreviewed"

[[contributions]]
role = "author"
actor = "agent:claude"
at = "2026-07-19T00:00:00+01:00"
source = "legacy"
agent = "claude"
harness = "claude"

[[contributions]]
role = "editor"
actor = "agent:gpt-5.6-sol"
at = "2026-07-22T00:00:00+01:00"
source = "lisp-sexpr-trait-consolidation"
agent = "gpt-5.6-sol"
harness = "codex"
+++

# Abstract S-expressions + abstract reductions — a reusable-API design (agent-authored)

Status: **historical design**. The current implementation uses the smaller
`covalence-sexpr-api::{SExprSyntax, SExprView}` waist, with parser policy in
`covalence-lisp::carrier::LispDatum`; the parser-owned `AbstractSExpr` proposed
below was implemented and then removed as a duplicate. Campaign directive: the
Lisp dialects (relational `lisp`/`sector`, value-semantics `scheme`, `acl2`,
future `forsp`/`forth`) should share **one S-expression abstraction** and **one
reduction abstraction** instead of four parallel encodings.

Companions: `initial-ideas/generic-repl-trait.md` (the `Repl` trait, now built
in `crates/lib/repl-core`), `initial-ideas/parametric-reduction.md` (the
three-axis reduction API, ditto), `relational-recursion.md`,
`acl2-book-frontend.md`, `acl2-s5-design.md`. SKELETONS entries this design is
scoped to resolve: `crates/lang/lisp/SKELETONS.md` "REPL bypasses the
`ReductionStrategy` seam" and "`carved → sexpr` rename pending".

---

## 0. The current landscape (what "four parallel encodings" means concretely)

**S-expression value encodings in the tree today:**

| # | encoding | where | atoms | ints | nil |
|---|----------|-------|-------|------|-----|
| E1 | `covalence_sexp::SExpr` (`SExp<Atom>`) | `crates/lib/sexp` | `Atom::Symbol`/`Str` | numerals are symbols | `List([])` by convention |
| E2 | carved `sexpr` kernel terms | `init/inductive/carved.rs`, payload `bytes` | `atom b` (blob) | **off-carrier**: value semantics uses typed `int` literals (`ValueKind::Int`); relational dialect uses the `(int n)` free-var injection (`int_backend::int_head`) | `snil` |
| E3 | ACL2 carrier `A` | `init/acl2/carrier.rs`, payload `coprod int bytes` | `aatom (inr s)` = `asym s` | **in-carrier**: `aint i = aatom (inl i)` | `anil` |
| E4 | ACL2 pseudo-terms | `init/acl2/term.rs` | carrier values again (deep embedding *inside* E3: `Terms::quote`, `mk_equal`, …) | quoted `aint` | `anil` |

Each of `semantics.rs`, `relation.rs`, `acl2.rs` (+ init's `Terms` encoders)
re-implements the same construction/recognition helpers against its encoding
(`as_scons`/`as_atom`/`is_snil` appear near-verbatim in three files;
`Session.render_sem` exists *only* to borrow one copy of them). And
`Lisp::lower` in `lib.rs` is already a proto-version of the constructor half of
the abstraction (nil/cons/resolve-atom fold) — unused by the modern paths.

**Reduction shapes in the tree today (the three the abstraction must cover
without flattening):**

| shape | output theorem | composition | hypotheses | driver |
|-------|----------------|-------------|------------|--------|
| **A. equational** (value semantics, `semantics.rs`) | `⊢ from = to` per step; composite `⊢ input = value` | `Thm::trans`, **left-fold** (streaming: `⊢ input = cur` at every prefix) | the `defun` equations unfolded | `repl-core` `Reduction` + `RunToValue` (the only path on the seam) |
| **B. relational** (`relation.rs`) | `⊢ Step from to` per step; composite `⊢ Reduces input value` | `reduces_step` clause, **right-fold** seeded with `reduces_refl(value)` (`prove_reduces` buffers all steps, folds at the end) | none for closed programs | standalone `prove_step`/`prove_reduces` + `REL_FUEL` (bypasses repl-core) |
| **C. certificate/derivability** (`acl2.rs::CertEngine` over `init/acl2`) | `⊢ Derivable_ACL2 ⌜(EQUAL e 'v)⌝`, then soundness + `transport_equal` → base-HOL model equation | object-level derivation rules (`derive_mp`, `equal-trans` INSTed, …) — **not a step relation at all**; big-step structural recursion over E4 | none (certificate path) | `CertEngine::comp_cert` + the `cert_fragment` pre-check, falling back to shape A |

The dialect dispatch (`session.rs::Lang`) is a hand-written 4-way match over
these; the ACL2 book pipeline (`book.rs`) drives shape C with an A fallback
inside `defthm` events; `int_backend::IntBackend` is the one *existing*
retargeting seam (two impls, `IntVariant`/`NatVariant`, shared by shapes A
and B).

---

## 1. The `AbstractSExpr` trait (working name)

### 1.1 Shape: two layers, values first

The mistake to avoid: one mega-trait that is simultaneously a parser target, a
kernel theory, and a prover. Split by *what the implementor must have*:

**Layer 1 — `AbstractSExpr` (kernel-agnostic; the S-expression *value*
algebra).** Anything that can build and observe atom/nil/cons data with payload
injections. Implementable by plain Rust data (E1) as well as kernel terms
(E2/E3), so generic code (readers, printers, golden tests, the metacircular
ground fragment) runs over all of them.

```rust
/// An abstract S-expression carrier: construction + observation of
/// atom/nil/cons values with payload injections. `Value` is the dialect's
/// value representation — `covalence_sexp::SExpr` for the free surface
/// instance, a kernel `Term` for theory-backed instances.
pub trait AbstractSExpr {
    type Value: Clone;
    type Error;

    // -- constructors (total, untrusted building) --
    fn nil(&self) -> Self::Value;
    fn cons(&self, h: Self::Value, t: Self::Value) -> Result<Self::Value, Self::Error>;
    /// Payload injections. Extensible via the non_exhaustive enum, NOT a
    /// type-level payload parameter (see non-goals §5).
    fn atom(&self, p: PayloadLit<'_>) -> Result<Self::Value, Self::Error>;

    // -- observers (syntactic recognizers on values; partial by design) --
    fn as_cons(&self, v: &Self::Value) -> Option<(Self::Value, Self::Value)>;
    fn as_atom(&self, v: &Self::Value) -> Option<PayloadOwned>;
    fn is_nil(&self, v: &Self::Value) -> bool;

    // -- surface bridge (defaults derived from the above) --
    /// Surface data → value ("quote"): the `data()` folds of semantics.rs /
    /// relation.rs / acl2's `quoted_value`, once. Default impl folds the
    /// SExpr tree through nil/cons/atom with the dialect's numeral policy.
    fn quote(&self, data: &covalence_sexp::SExpr) -> Result<Self::Value, Self::Error>;
    /// Value → surface data (rendering); `None` for a non-datum (stuck term,
    /// off-carrier literal — the caller decides how to print those).
    fn render(&self, v: &Self::Value) -> Option<covalence_sexp::SExpr>;
}

#[non_exhaustive]
pub enum PayloadLit<'a> { Sym(&'a [u8]), Int(&'a Int) }
#[non_exhaustive]
pub enum PayloadOwned { Sym(Vec<u8>), Int(Int) }
```

Design points:

- **`atom(Int …)` is fallible on purpose** — this is exactly where the
  dialects genuinely differ, and the trait must expose it, not paper it over:
  - `sector`: `Err` (no integers; the numeral stays a `Sym` per its policy);
  - `sector+int`: the `(int n)` free-var injection via the installed
    `IntBackend` (incl. the `NatVariant` negative-literal rejection — an
    honest per-dialect `Err`);
  - ACL2 `A`: the genuine payload constructor `aint`.
- **Numeral policy lives in `quote`**, mirroring today's split: the value
  semantics quotes numerals as *symbol* atoms (numerals-in-data stay
  uninterpreted), the relational int dialect quotes them as `(int n)`, ACL2
  quotes them as `aint`. `quote` is therefore a method with a default, not a
  provided-only fold.
- **`render` replaces** `Session::render` / `Acl2Session::render`'s
  structural halves and deletes the `Session.render_sem` borrowed-helpers hack.
- The **capability difference** between E2+`int_head` and E3 must be
  documented on the impls, not hidden by the trait: `int_head` is an
  unconstrained free variable (no ∀-lifted arithmetic facts range over it —
  the "int_head trap" `acl2/carrier.rs` names), while `aint` is genuine
  payload with the proved `init/int.rs` theory behind it. Both satisfy
  `atom`/`as_atom`; only E3 supports quantified arithmetic transport. A
  `fn payload_is_carrier(&self) -> bool`-style advisory flag (or just doc
  discipline) records this; nothing generic may *prove* through it.

**Layer 2 — `KernelSExpr: AbstractSExpr<Value = Term>` (the kernel-term
image + the structural laws).** What theory-backed impls add:

```rust
pub trait KernelSExpr: AbstractSExpr<Value = covalence_init::Term> {
    /// The carrier type (`sexpr`, or ACL2's `A`).
    fn tau(&self) -> Type;
    /// Proved structural laws, delegated to the carved instance:
    /// `⊢ car/cdr (scons h t) = h/t`, the leaf defaults, `atom` injectivity.
    fn proj(&self, take_cdr: bool, v: &Term) -> Result<Thm, Self::Error>;
    fn inj_atom(&self, b1: &Term, b2: &Term) -> Result<Thm, Self::Error>;
    /// The induction/recursor seam (structural induction at a motive;
    /// wraps CarvedSExpr::induct / prec) — what defun-admission and the
    /// metatheorem layers consume.
    fn induct(&self, motive: &Term, cases: Vec<Thm>) -> Result<Thm, Self::Error>;
}
```

Everything here is **delegation to already-proved theorems** on the wrapped
`CarvedSExpr` — the trait mints nothing. The two initial impls are thin
adapters living in `covalence-lisp` (see §4 for the crate decision):

- `CarvedCarrier` wrapping `&'static CarvedSExpr` from `carved()` (payload
  `bytes`) plus an `Option<Arc<dyn IntBackend>>` for the `atom(Int)` policy —
  one struct covers `sector`, `sector+int(int)`, `sector+int(nat)`, and the
  value semantics' data half, as *configurations*, which is what
  `Lang::dialect()` already expresses;
- `Acl2Carrier` wrapping `&'static Acl2` from `init::acl2::carrier::acl2()`
  (payload `coprod int bytes`).
- `SurfaceSExpr` — the free instance on `covalence_sexp::SExpr` itself
  (`quote` = clone modulo numeral policy, laws absent). Useful for
  carrier-generic tests and for the reader/printer round-trip harness.

**The payload-parametric link:** `CarvedSExpr::build_with(payload, prefix)` is
already the payload-parametric *theory* constructor; the trait is its
*consumer-side* mirror. A third carved instance (say a Forth cell payload)
gets an `AbstractSExpr` impl by writing one more thin adapter — no generic
machinery re-derivation. The existing `CarvedSExprBackend`
(`InductiveBackend`, shape-pinned to the bytes payload) is a *different* seam
— engine-facing realization, not value algebra — and stays as is; do not merge
them.

### 1.2 What `AbstractSExpr` is *not*: a program compiler

Programs and data coincide only in some dialects. In ACL2/metacircular land
compile ≈ quote (pseudo-terms *are* carrier data, E4); in the equational value
semantics compile ≠ quote (programs are typed operator applications with
kernel `cond`, HOL `bool` tests, typed int redexes — `LispSemantics::compile`
with its `Hint` machinery). Forcing one `compile` into the value trait would
recreate the truthy-`cond` wall inside the abstraction. So compilation is its
own small axis, per dialect, *over* a carrier:

```rust
/// Surface program → the dialect's evaluable term. The three existing
/// compilers (LispSemantics::compile, LispRel::compile_surface, the acl2
/// encoder) become instances; quote-heavy dialects default compile = quote
/// on data positions.
pub trait ProgramCompiler<C: AbstractSExpr> {
    type Error;
    fn compile(&self, e: &covalence_sexp::SExpr) -> Result<C::Value, Self::Error>;
}
```

---

## 2. The abstract reduction API

### 2.1 What generalizes and what must not

`repl-core`'s three-axis API (`Repr` / `Semantics` / `Strategy` +
`Reduction`) is already shape-agnostic in its *types* (the `Thm` associated
type never says "equation") but shape-A-biased in one *signature*:
`Semantics::compose(prev: Option<Thm>, step_thm) -> Thm` is a **left-fold** —
it demands "extend `⊢ input ↝ cur` by one step on the right". Shape B cannot
do that today: `Reduces` is defined by `refl` + left-cons
(`Step a b ⟹ Reduces b c ⟹ Reduces a c`), so `prove_reduces` buffers steps
and right-folds from `reduces_refl(value)`. (A left-fold would need the
derived transitivity metatheorem `Reduces a b ∧ Step b c ⟹ Reduces a c`,
which is exactly the not-yet-proved `Reduces = Step*` SKELETONS item — the API
must not silently depend on it.)

Shape C is not a step relation at all — no `Semantics` instance exists for it,
and pretending otherwise (e.g. "steps" = derivation-rule applications) would
be lossy: its natural unit is a big-step structural recursion over E4 with an
*exit transport*. So:

- **Shapes A and B unify at the `Semantics` axis** — with the composition
  axis honestly split (§2.2).
- **Shapes A, B, and C unify one level up**, at a one-shot certified-eval
  seam (§2.3) — which is also the level `Session::Lang` and the book pipeline
  actually dispatch on.

### 2.2 `Composer`: splitting the composition axis (repl-core change)

Replace `Semantics::compose` with a composer object owned by the semantics:

```rust
/// How per-step certificates aggregate into the composite claim
/// `⊢ input ↝ cur`. Two lawful shapes; the trait does not promise streaming.
pub trait Composer<T: Clone /* the step/composite Thm type */, Term> {
    type Error;
    /// Absorb one step certificate (⊢ from ↝ to, from = current head).
    fn push(&mut self, step: T) -> Result<(), Self::Error>;
    /// The composite `⊢ input ↝ cur` for the CURRENT head `cur`.
    /// May cost O(steps) (buffered shapes refold); callers pull it at
    /// checkpoints, not per step.
    fn composite(&self, cur: &Term) -> Result<Option<T>, Self::Error>;
}
```

- **`TransFold`** (shape A): `push` = `Thm::trans` onto the running
  equation; `composite` = clone. Streaming, O(1) per step — current
  behaviour, unchanged.
- **`ReducesFold`** (shape B): `push` = buffer the `⊢ Step` cert;
  `composite(cur)` = seed `reduces_refl(cur)` and right-fold the buffer with
  `reduces_step`. This is `prove_reduces`'s exact loop, and — pleasantly — it
  gives shape B something it does not have today: a *genuine partial*
  certificate `⊢ Reduces input cur` at any fuel checkpoint (fold with refl at
  the current head), so `Status::Diverging` outputs become certified for the
  relational dialects too. Cost: O(n) per checkpoint; acceptable because
  checkpoints are user-driven (`drive` boundaries), not per step.
- If/when the `Reduces = Step*` transitivity metatheorem lands, `ReducesFold`
  can switch to a streaming left-fold internally with **zero API change** —
  that is the test that the axis is cut correctly.

`Reduction<R, S>` then stores a `Composer` instead of `Option<Thm>`;
`Reduction::composite()` takes the O(n)-refold caveat into its docs. `pull`
becomes `step` → `composer.push`. `Strategy`/`RunToValue`/`Fuel`/`Status` are
untouched.

With that, `relation.rs` gains the wrapper the SKELETONS entry ("No
`RelationalSemantics` `Semantics<LispRepr>` wrapper / `#semantics` toggle
yet") already anticipates:

```rust
/// Shape B on the Semantics axis: step = prove_step (⊢ Step from to),
/// composer = ReducesFold. Repr is the same LispRepr (kernel Term).
pub struct RelationalSemantics { rel: LispRel }
impl Semantics<LispRepr> for RelationalSemantics { /* delegation */ }
```

and `Session::reduce`'s relational arm goes through the same
`Reduction`/`RunToValue` driver as `scheme`, retiring the bespoke
`REL_FUEL` loop.

### 2.3 `CertifiedEval`: the one-shot seam all three shapes satisfy

```rust
/// Evaluate a compiled term to a value, backed by a theorem in this
/// dialect's JUDGMENT SHAPE. The printed value is always read off the
/// theorem (per shape, below) — no theorem, no value.
pub trait CertifiedEval<C: AbstractSExpr> {
    type Thm: Clone;
    type Error;
    /// Cheap syntactic pre-check: is `e` in this evaluator's fragment?
    /// (Shape C's `cert_fragment`; `true` by default.)
    fn supports(&self, e: &C::Value) -> bool { let _ = e; true }
    fn eval(&self, e: &C::Value, fuel: Fuel) -> Result<Evaluated<C::Value, Self::Thm>, Self::Error>;
}

pub struct Evaluated<V, T> {
    pub value: V,
    /// The judgment: A `⊢ e = v` | B `⊢ Reduces e v` | C `⊢ Derivable_X ⌜(EQUAL e 'v)⌝`.
    pub thm: T,
    pub status: Status,   // Value / Diverging(steps) — non-termination stays first-class
    pub steps: u64,
}
```

Instances:

- **Blanket for step shapes**: `Driven<S: Semantics<R>, St: Strategy>` —
  compile-free driver glue; A and B come along for free. This same blanket,
  restricted to `RunToValue` + `Fuel::UNBOUNDED`, provides the legacy
  `ReductionStrategy` impl (§2.4).
- **Shape C directly**: `CertEngine` (refactored to hold an `Acl2Carrier`)
  implements `CertifiedEval<Acl2Carrier>` with `supports` = `cert_fragment`
  and `eval` = `comp_cert` (+ `refl_cert` packaging). Fuel is advisory (the
  recursion is structural); `steps` counts derivation nodes if cheap, else 0.
- **Fallback composition as a combinator**: today's defthm logic
  ("certificate path if in fragment, else reduction") becomes
  `OrElse<A, B>(a, b)` where `eval` tries `a` when `a.supports(e)`, else `b`
  — with the *output* preserving which arm fired. That is `Acl2Proof`
  {`Certificate`, `Reduction`} generalized:

```rust
pub enum EitherThm<TA, TB> { Primary(TA), Fallback(TB) }
```

  Session-level rendering keeps discriminating (the honesty requirement:
  never present a defun-hypothesis reduction theorem as a hyp-free
  certificate).

- **The transport exit stays explicit** (never folded into `eval`): shape C's
  certificate is *about the deep embedding*; crossing to a model theorem is
  its own audited move:

```rust
/// Judgment C → judgment A over the model: soundness + transport_equal.
pub trait Transport<TFrom, TTo> {
    type Error;
    fn transport(&self, cert: &TFrom) -> Result<TTo, Self::Error>;
}
```

  instantiated by `ladder::soundness` + `derivable::transport_equal` (ground)
  and, on the S6 path, `transport_equal_open`. Keeping it a separate trait
  is what lets the same pattern serve the other certificate families later
  (Metamath `Derivable_DB`, SpecTec `Derivable_R` — the memory-noted
  existence-transport pillar), without claiming that design here.

### 2.4 Resolving the "REPL bypasses the `ReductionStrategy` seam" entry

`hol.rs::SymbolicStrategy` (the legacy one-shot `ReductionStrategy`) is used
only by `LispHol::eval` and its own tests; `Session` drives
`Semantics` + `RunToValue` directly. Resolution, in order:

1. Add the blanket `impl<R, S> ReductionStrategy for Driven<R, S, RunToValue>`
   in repl-core (or covalence-lisp if orphan rules bite — `Driven` is ours,
   so repl-core works). Now *every* `Semantics` instance satisfies the seam
   **by construction**; there is no second path to bypass.
2. Retire `hol.rs::SymbolicStrategy` and port `LispHol::eval` (or retire
   `LispHol` too — see below) onto the blanket impl.
3. `Lisp`/`LispHol` (`lib.rs`): the trait's real content — the Forth-style
   atom-resolution fold — is subsumed by `AbstractSExpr::quote` + the
   dialect's `ProgramCompiler`. Recommendation: keep the `Lisp` trait
   *deprecated-in-docs* for one slice (it is the crate's public name), fold
   its tests onto `SurfaceSExpr`/`CarvedCarrier`, then delete trait + `hol.rs`
   together and delete both SKELETONS lines.

### 2.5 Where `Session::Lang` dispatch sits on this

`Lang` stays an enum (users pick dialects by name); what changes is what it
selects: a `(carrier, compiler, evaluator)` triple instead of four
hand-written arms in `reduce`:

```text
Lang::Sector  → (CarvedCarrier{int:None},  RelCompiler,   Driven(RelationalSemantics))
Lang::Lisp    → (CarvedCarrier{int:Int},   RelCompiler,   Driven(RelationalSemantics))
Lang::Scheme  → (CarvedCarrier{int:Int},   ValueCompiler, Driven(LispSemantics))
Lang::Acl2    → (Acl2Carrier,              Acl2Compiler,  OrElse(CertEngine, Driven(LispSemantics)))
```

Because the `Thm`/`Error` types differ per shape, the session boundary keeps a
small output enum (today's `Outcome`/`Acl2Outcome` merged, with the judgment
tagged) rather than `dyn`-erasing theorems — theorem types are part of the
honesty story and must stay visible. The `Repl` impl on `Session` is
unchanged in shape; `eval` routes through the triple. A future `#semantics`
directive (SKELETONS) is then literally "swap the evaluator component while
keeping the carrier".

---

## 3. Retargeting demonstrations (the acceptance tests for this design)

1. **The metacircular ground fragment, one source, two dialects.** The
   `little_schemer_ch2.rs::metacircular_*` slice (quote/car/cdr/cons
   dispatched by `eq?`) rewritten once against
   `AbstractSExpr + ProgramCompiler + CertifiedEval`, executed over
   (a) `scheme` (shape A; assert value + hyps = exactly the defun equations)
   and (b) `lisp` relational (shape B; assert value + `hyps().is_empty()` +
   conclusion is literally `Reduces input value`). Same program text, same
   expected `render` output, different asserted judgments — the differences
   are *displayed*, not erased. (The full metacircular interpreter's
   truthy-`cond`/polymorphic-`eval` walls are untouched by this design and
   remain SKELETONS items; the demonstration is the ground fragment only.)
2. **The book pipeline's certificate path against the trait.** `book.rs`
   `defthm` events call `OrElse(CertEngine, reduction).eval` + the explicit
   `Transport` exit, and the stored `Acl2Theorem` keeps its provenance from
   `EitherThm`. Gate: the existing fixture book's tallies are unchanged
   (including the pinned `app-assoc`/`len2-app` rejections), proving the
   refactor moved no goalposts.
3. **A third carrier without new proofs.** Instantiate `AbstractSExpr` for a
   fresh `CarvedSExpr::build_with` instance (any payload) in a test, and run
   the carrier-generic quote/render round-trip + structural-law suite
   (`proj`, `inj_atom`) against all three impls. This is the "same proofs at
   another payload" claim made operational.
4. **Where `IntBackend` folds in.** `IntBackend` becomes the *payload policy
   component* of `CarvedCarrier`: `atom(Int)`/`as_atom` delegate to
   `lit`/`as_lit`, and the arithmetic law supply (`prove_reduce`) stays what
   shapes A/B consume for their int redex steps. For `Acl2Carrier` the same
   role is played natively (`aint` + init's `Prims` ground folds:
   `plus_lit`, `lt_lit`, …). Explicitly **not** unified further: `IntBackend`
   proves kernel equations about *typed int redexes injected via a free
   head*; `Prims` proves *model-carrier* folding laws — different theorem
   families, one shared trait-shaped role (injection + proved folds). A
   later `PayloadBackend` generalization (symbols, bytes payloads) is
   plausible but not needed by any current dialect — defer.

---

## 4. Migration plan

Smallest honest slices, each independently landable and test-gated:

**Slice 1 — the value algebra (no behaviour change).**
- New module (see crate decision below): `AbstractSExpr` + `PayloadLit` +
  the three impls (`SurfaceSExpr`, `CarvedCarrier`, `Acl2Carrier`).
- Port the duplicated helpers onto it: `semantics.rs`/`relation.rs`/
  `acl2.rs` `as_scons`/`as_atom`/`is_snil`/`data`/`quoted-value` folds;
  delete `Session.render_sem` (render via the carrier). Existing tests are
  the gate; add the carrier-generic round-trip suite (§3.3).
- Constructors must follow the LazyLock re-entrancy discipline
  (adapters call `carved()`/`acl2()` directly, never through a new nested
  `LazyLock`) and — per the standing rule — any change touching
  kernel/defs/env paths is cargo-test-gated, never merged build-only.

**Slice 2 — the `ReductionStrategy` seam fix (small, resolves a SKELETONS
severe-adjacent entry).** `Driven` + blanket `ReductionStrategy` impl in
repl-core; retire `SymbolicStrategy`; start the `Lisp`-trait deprecation.
Delete the SKELETONS entry.

**Slice 3 — the `Composer` split + `RelationalSemantics`.** repl-core change
(one crate, kernel-agnostic; `TransFold` keeps shape A bit-identical);
`relation.rs` gains the wrapper; `Session`'s relational arm moves onto the
shared driver. Gate: relational tests unchanged, plus a new test asserting a
*partial* `⊢ Reduces input cur` at a fuel checkpoint (the new capability).

**Slice 4 — `CertifiedEval` + `OrElse` + `Transport`.** Refactor
`CertEngine`'s entry points onto the traits; `acl2.rs::defthm` and
`book.rs` route through them. Gate: fixture-book tallies + the pinned
`Acl2Proof` provenance assertions unchanged.

**Slice 5 — the `carved → sexpr` rename (coordinated, mechanical).** Do it
*after* slice 1 so call sites are already funneled through the adapters and
the rename touches few files. Naming proposal that avoids the
`covalence_sexp::SExpr` clash three ways:
- surface parse tree: stays `covalence_sexp::SExpr` (it owns the plain name);
- kernel theory struct: `CarvedSExpr` → **`SExprTheory`** (constructors
  `sexpr_theory()` / ACL2's stays `acl2_carved` → `acl2_theory()`);
- the trait family: **`AbstractSExpr`** / `KernelSExpr` as above (never bare
  `SExpr`).
Then delete the "carved → sexpr rename pending" SKELETONS line.

**Crate placement.**
- `AbstractSExpr` + `PayloadLit` + `SurfaceSExpr`: **`covalence-sexp`**
  (`crates/lib/sexp`) — it owns the surface type consumed by
  `quote`/`render` defaults, and stays kernel-free (Layer 1 has no kernel
  types). This is the same crate the generic-repl-trait note earmarked for
  the events-based builder extension; the trait is that idea's value-level
  half.
- `Composer`, `Driven`, the blanket `ReductionStrategy` impl,
  `CertifiedEval`, `OrElse`, `Transport` (all kernel-agnostic):
  **`covalence-repl-core`** — they are the reduction axes' natural
  extensions, and repl-core must stay free of covalence-init deps (all
  kernel contact through associated types, as today).
- `KernelSExpr`, `CarvedCarrier`, `Acl2Carrier`, `RelationalSemantics`, the
  compilers, the shape instances: **`covalence-lisp`** — keeping
  `covalence-init` untouched (no new deps into the kernel closure; the
  adapters wrap init's already-public surface). **No new crate** until a
  second *language family* (forsp/forth) actually consumes the traits from
  outside `covalence-lisp`; then the adapters + carrier impls could split
  into a `crates/lang/sexpr-kernel` crate. Deciding that now would be
  speculation.

**What stays dialect-specific (deliberately, after full migration):** the
three compilers (Hint/`cond`-typing inference; truthy relational forms; ACL2
macro normalization + defun encoding), `defun` admission (both the lang-lisp
hypothesis dictionary and init's S4 admissibility), `CertEngine`'s derivation
construction, the S6 induction premise builders, `NatVariant`'s guards, and
every `Step`-clause set. The traits carry values, judgments, and drivers —
not proof strategy.

---

## 5. Non-goals and risks

**Non-goals.**
- **No single lossy reduction interface.** The three shapes keep distinct
  judgment types, hypothesis disciplines, and composite-availability
  profiles; the unification points are exactly two (the `Semantics` axis for
  A/B with the composition split, and `CertifiedEval` for A/B/C), and shape
  C's transport exit stays a visible, separate move. Anywhere the design
  would need a method one shape can't honestly implement, the method belongs
  one level up or on a sub-trait.
- **No type-level payload genericity** (GAT payload families, const-generic
  arities). Two payload instances exist; `PayloadLit` (non_exhaustive) covers
  them and extends by enum variant. Revisit only when a third payload with a
  *different* injection discipline is real.
- **No TCB/kernel changes.** Everything is adapters over already-proved
  theorems in `covalence-init`; `crates/kernel/hol/core` and `kernel/base`
  are untouched by construction, and `covalence-init` itself gains no code
  in slices 1–4 and only renames in slice 5.
- **Not a fix for the metacircular walls.** Truthy-data `cond`, polymorphic
  `eval` return, `sexpr`-valued `t`/`nil` remain open SKELETONS items; this
  API makes the eventual fix land once instead of thrice, nothing more.
- **Not the E4 (pseudo-term) abstraction.** `Terms`' encoders are a deep
  embedding *program* representation with their own invariants
  (representation contract: never `asym "NIL"`); they consume `Acl2Carrier`
  but are not themselves forced under `AbstractSExpr`.

**Risks / open questions.**
1. **`Composer::composite` cost for shape B** is O(steps) per checkpoint
   (refold from refl). Fine at REPL scale (`REL_FUEL` = 10k); a book-scale
   relational replay would want the `Reduces = Step*` left-transitivity
   metatheorem first. The API is deliberately indifferent to which is inside.
2. **Type plumbing at the Session boundary.** Per-shape `Thm`/`Error` types
   mean the dispatch triple is an enum of concrete stacks, not a
   `Box<dyn …>`; that is more code than a trait object but is the honest
   choice (theorem provenance stays typed). Watch for combinatorial growth
   if dialects multiply — the mitigation is that new dialects reuse existing
   stacks (forsp over `CarvedCarrier` + shape B, say).
3. **Orphan-rule friction** for the blanket `ReductionStrategy` impl if
   `Driven` ends up in covalence-lisp instead of repl-core — keep `Driven`
   in repl-core to avoid it.
4. **`quote` policy duplication**: numeral policy appears in both `quote`
   and the compilers; the design accepts one deliberate seam (data numerals
   vs expression numerals genuinely differ per dialect) but the impls should
   share a single `NumeralPolicy` helper to prevent drift.
5. **Behavioural freeze during migration**: slices 1/3/4 refactor live REPL
   paths; the gates are the existing test suites *unchanged* plus the pinned
   negative controls (fixture-book rejections, `sector` stuck `(+ 2 2)`).
   Any output change is a design bug, not an acceptable delta.
6. **Future dialects that are not S-expression-shaped** (forth's stack
   programs): they implement `Repl` and possibly `CertifiedEval`, but should
   *not* be shoehorned into `AbstractSExpr` unless they adopt sexpr data.
   The trait is for the S-expression family; the reduction axes are for
   everyone.

---

## 6. Implementation report — slice 1 (2026-07-17, agent)

**Landed** (migration plan slice 1 only, per the campaign directive):

- `covalence-sexp::abstract_sexpr` — `AbstractSExpr` + `PayloadLit` /
  `PayloadOwned` + `NumeralPolicy` + default `quote`/`render` folds +
  `SurfaceSExpr` (with unit tests). `covalence-sexp` gained the kernel-free
  `covalence-types` dep for `Int` (the design's `PayloadLit::Int` type,
  crate unnamed in §1.1).
- `covalence-lisp::carrier` (`hol` feature) — `KernelSExpr` +
  `CarvedCarrier` (any carved instance + optional `IntBackend`, covering
  `sector` / `sector+int(int|nat)` / value-semantics-data as configurations)
  + `Acl2Carrier`.
- Helper porting: `semantics.rs` and `relation.rs`
  `as_scons`/`as_atom`/`is_snil`/`atom_bytes`/`data`/`data_atom` now
  delegate to a `CarvedCarrier` field (signatures unchanged; full
  covalence-lisp suite unchanged-green = the behavioural-freeze gate).
- `tests/carrier.rs` — the §3.3 suites, written once and run over
  `SurfaceSExpr` / carved-`bytes` / carved-`bytes`+int / ACL2 / a fresh
  `build_with(int, "test.icell")` instance: quote/render round-trips,
  exact-statement `proj`/`inj_atom`/`induct` checks (`hyps().is_empty()` +
  independently built conclusions), a slice-1 retargeting demonstration
  (one generic `second_element` walker producing per-dialect theorems whose
  statements differ while the rendered value agrees), and dialect-honest
  negative controls (`sector` no-int, `NatVariant` negatives, the ACL2
  `asym "NIL"` contract, stuck `proj`, string-literal data in ACL2).

**Deviations from the design body:**

1. **Scope fence.** `session.rs` / `acl2.rs` / `book.rs` were owned by the
   concurrent book/phase-3 agent this round, so slice 1's "delete
   `Session.render_sem`, port `acl2.rs` quoted-value" half is *not* in this
   change. Integration steps are recorded in `crates/lang/lisp/SKELETONS.md`
   ("Abstract S-expr API" entry): `Acl2Carrier::quote` already mirrors
   `Acl2Session::datum` exactly (pinned by `tests/carrier.rs`), so the port
   is a swap, not a re-derivation.
2. **`KernelSExpr` gained `proj_op(take_cdr) -> Term`** (not in §1.1): a
   pure term accessor for the projection operators, needed to *state* the
   projection laws generically (exact-statement tests) and to build walker
   terms. No proof surface.
3. **Quote-policy correction to §1.1.** The design said the relational int
   dialect "quotes numerals as `(int n)`"; the code truth (`relation.rs::data`)
   is that *every* carved dialect quotes data numerals as uninterpreted
   symbol atoms — the `(int n)` injection is expression-position
   compilation, not quoting. `CarvedCarrier` therefore defaults its quote
   policy to `Sym` even with a backend installed (behavioural freeze);
   `with_quote_policy(NumeralPolicy::Int)` is the explicit opt-in (used by
   the int-payload third carrier). `Acl2Carrier` overrides `quote`
   wholesale with the datum discipline (numerals → `aint`, `nil`/`t` any
   case → canonical `anil`/`t`, string literals rejected).
4. **`CarvedSExpr::build_with` was made `pub`** (visibility-only change in
   `covalence-init`; the design said init gains no code in slices 1–4).
   Needed for the §3.3 "third carrier without new proofs" demonstration;
   the doc comment carries the once-per-instance + re-entrancy discipline.
5. **The canonical ACL2 `t`** (a defined constant, not syntactically
   `asym "T"`) observes via `as_atom` as the symbol payload `"T"`, backed
   by its defining equation; `proj` at the *derived* `aint`/`asym` forms
   composes the payload unfold with the leaf default so the law is stated
   about the value as written. `proj` at the bare `t` constant errors
   (unfold first) — acceptable for slice 1; revisit if a consumer needs it.
6. **Layer-1 `render` is dotted-pair-free** (returns `None` on improper
   lists — the surface `SExpr` tree cannot represent them); the dialect
   printers keep their own ` . ` fallbacks, as §1.1 anticipated for
   non-datum values.
7. **`Lisp`-trait deprecation not started** — that is slice 2's first move
   (§2.4), out of slice-1 scope.

**Slice-1 gate results:** full `covalence-lisp --features hol` suite
unchanged-green + the new `tests/carrier.rs` battery (7 tests) green +
`covalence-sexp` unit tests green.
