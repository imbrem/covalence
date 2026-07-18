+++
id = "N0035"
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

# Covalence — Surface Syntax

> **DESIGN SKETCH — rationale only.** The high-level Haskell-like syntax for
> theories, definitions, and proofs that today live as hand-written Rust
> (`defs/`, `init/`, `proofs/`).
>
> **Canonical concrete forms live in
> [`surface-compiler.md`](./surface-compiler.md) §3.0** (`#sig`/`#thy`/`#spec`/
> `#model`/`#models`, the artifact taxonomy, the `#comp` calc form). This doc is
> the *rationale and aspirational reach*: the declarative/pluggable north star
> (§1.1), the SQL analogy (§1.2), the pure-S-expr lexical rule (§1.3), the
> term-sublanguage-into-TCB idea (§1.4), the mixfix layer (§1.5), the
> spec-vs-definition distinction (§2), and the entailment/categoricity questions
> (§6). Elaborates down to the kernel TCB
> ([`kernel-design.md`](../kernel/kernel-design.md)).

---

## 1. Why a surface syntax

Today every definition and every proof is **Rust**. A type like `option` is a
`TypeSpec` built in `defs/option.rs`; its constructors are `TermSpec`s built with
`poly_let_term!`; its theorems (`some_ne_none`, exhaustiveness, the recursor
equations) are hand-assembled in `init/option.rs` by threading kernel rules. That
is the right *substrate* — small, auditable, inside the TCB — but a terrible
*authoring* surface:

- A one-line definitional equation (`case (some a) b f = f a`) becomes a dozen
  lines of `Term::app` / `Thm::trans` / `cong_arg` plumbing.
- There is no separation between *what* a theory says and *how* the kernel
  realizes it.
- Definitions cannot be referenced, shared, or content-addressed; they are Rust
  symbols compiled into one binary.

**The goal:** a high-level S-expression syntax for theories, definitions, and
proofs that *elaborates* down to the existing kernel objects and rules. Over
time the `defs/`/`init/` catalogue migrates out of Rust into this syntax, and the
Rust becomes purely the elaborator + checker. Later, each fragment becomes a
**content-addressed object** and theories are *linked* graphs of fragments (§7).

The surface syntax sits *above* the canonical low-level S-expressions already
emitted by the kernel (the `(app …)`, `(abs …)`, `(thm (hyps …) (concl …))`
forms). That low-level form is the elaboration target and serialization format;
the surface form is what a human writes.

### 1.1 The north star: declarative meaning, pluggable computation

In the limit this is a **Haskell-like language** — algebraic data types, typed
functions, equations — with one twist: **it has no fixed operational semantics.**
Reduction is left entirely to the kernel.

In an ordinary functional language, `case (some a) b f` *reduces* to `f a` by a
fixed evaluator. Here `case (some a) b f = f a` is a *theorem* the kernel can
establish, and **how** is open:

- a **proof tactic** (the `(by …)` scripts of §5);
- an **LLM** proposing the rewrite (untrusted — the kernel checks it);
- a **WASM-compiled decider** computing the normal form + a checkable certificate
  ([`observers.md`](../observers/observers.md)).

Every route terminates in the *same* kernel rules, so the computation strategy is
**pluggable without ever compromising soundness**. Swap a naive rewriter for an
LLM-guided one for a WASM-JITted one: the set of provable theorems is unchanged,
only the *cost* of reaching them. (This is also the deeper reason for the HOL-ω
direction, [`metatheory.md`](../logics/metatheory.md) §5.2: a genuinely
Haskell-like *type* language wants higher-kinded type-constructor variables.)

Generalized: this is **handler dispatch**. Reduction, rewriting, and
*unification* are open-ended operations the tactic engine *requests* and the
**environment supplies a handler** for — so first-order, higher-order,
dependent-type, or domain-specialized (arithmetic-aware `Bits[n+m]` unifier)
handler sets make a *different logic* feel native through the *same* surface. The
proof-theoretic treatment is [`metatheory.md`](../logics/metatheory.md) §7; the
product framing is [`frontend.md`](./frontend.md) §4. The seed exists today: the
script layer's `Env` is the dispatcher, and `Env::apply_unify` / `Env::rw_unify`
are registered seams kept separate so a custom unifier can be installed later.

### 1.2 Analogy: SQL with set theory, and an LLM query planner

**Imagine writing queries in SQL, except the query language is set theory (HOL)
and the query planner can be an LLM.**

- SQL: you write *what* you want; the **planner** decides *how* to execute; the
  engine guarantees the answer matches the query.
- Here: you write *what* is true; the **planner** — a tactic, an LLM, a WASM
  decider — decides *how* to derive it; the **kernel** guarantees the result is
  genuinely a theorem.

The planner can be arbitrarily clever, learned, or wrong: a bad plan is slow or
fails, never *unsound*. That is what makes "the query planner can be an LLM" safe
to say out loud.

### 1.3 Everything is a pure S-expression

The language is **pure S-expressions with no sugar**. No infix syntax, no
surface-level shorthand: every reserved word is a **`#`-headed builtin**, and the
parser accepts *only* these forms — nothing desugars.

The arrows and colons that appear in this doc — `'a -> 'b`, `none : option 'a`,
`lhs => rhs` — are **informal prose notation only**, not accepted by the parser.
The real forms:

| informal notation | actual (and only) form |
|---|---|
| `'a -> 'b` | `(#fn 'a 'b)` |
| `none : option 'a` | `(#sig none (option 'a))` |
| `lhs => rhs` | `(#rw lhs rhs)` |
| `(= a b)` | `(#eq a b)` |
| `λa. body` | `(#lam a body)` |
| `(by …)` | `(#by …)` |

A token's **lexical class is a pure function of its spelling**, so the parser
never needs scope to route it:

- **`#…`** — a **builtin** keyword: directive heads (`#theory`, `#def`, `#thm`)
  *and* every type/term head (`#fn`, `#lam`, `#eq`, `#sel`, `#abs`, `#rep`). An
  unknown `#foo` is *malformed*, not a name.
- **`'…`** — a **type variable** (`'a`, `'b`).
- **everything else** — an ordinary **name**: a *dotted catalogue* reference
  (`coprod.case`, `option.some`) or a *local* name (a bound variable or a symbol
  the enclosing `#theory` declares). Whether a local name is a bound variable or
  a declared constant is the elaborator's decision; the parser only records the
  token.

### 1.4 The term sublanguage (and lifting it into the TCB)

One fragment is special enough to name: the **term sublanguage** — the grammar
`#def` bodies and the leaves of `(#by …)` proofs are written in. It is a
**simply-typed lambda calculus** over the kernel's two logical primitives and the
`defs/` catalogue:

```text
term ::= NAME                         ;; var / local constant / dotted catalogue ref
      |  (term term+)                 ;; curried application (f x y …)
      |  (#lam x term)                ;; lambda  — (#lam (x A) term) to type-ascribe
      |  (#eq term term)              ;; primitive equality  =
      |  (#sel (x A) term)            ;; Hilbert choice  ε
      |  (#abs SPEC (ty*) term)       ;; TypeSpec carrier→wrapper coercion
      |  (#rep SPEC (ty*) term)       ;; TypeSpec wrapper→carrier coercion
      |  NUMERAL                      ;; integer literal
      |  (#blob …)                    ;; byte-string literal
```

Two properties make it worth isolating:

1. **It supports lambdas.** `#lam` is the one non-trivial binder, and it lets the
   sublanguage express the `defs/` bodies — `some ≡ λa. abs (inl a)` becomes
   `(#lam a (#abs option ('a) (inl a)))`, one-for-one with the Rust `let`-body.
2. **It has no operational semantics of its own.** It *names* terms; it never
   *reduces* them.

Because it is this small and closed, the term sublanguage is the natural
candidate to eventually **move into the TCB**: a trusted elaboration of just
these constructors into kernel `Term`s would let us write the `defs/` catalogue
in this sublanguage instead of hand-threaded `Term::app` / `Term::abs` Rust. The
directive and proof layers stay firmly outside the TCB (they only produce
checkable obligations); the term sublanguage is the one piece we may choose to
trust directly, so it is kept sharply delimited from the start. Its AST + parser
now live in the **fused** script layer
[`crates/kernel/hol/init/src/script/`](../../../crates/kernel/hol/init/src/script/)
(the standalone `surface/` module was folded into `script/` per the
surface↔script fusion — [`surface-compiler.md`](./surface-compiler.md) §3.0).

### 1.5 Above the pure form: the concrete-syntax layer (planned)

The pure S-expressions above are the *canonical* form — deliberately **not** what
a human types. The planned top layer is a real concrete syntax: a lexer + an
operator-precedence (Pratt) parser that reads the notation people want — infix
`a + b * c`, `'a -> 'b`, `none : option 'a`, `lhs => rhs` — and genuinely
**parses** it into the canonical AST.

- **Precedence + associativity** come from a table — ideally *declarable*
  (Lean/Isabelle/Agda-style `notation`/`mixfix`), so a theory introduces its own
  operators with their fixity. The table is the only place precedence lives.
- **The pure S-expr stays canonical.** The concrete layer elaborates *down* to it
  and adds no expressive power — **stage 0** of the compiler
  ([`surface-compiler.md`](./surface-compiler.md) §6). Two texts that elaborate
  to the same S-expr are the same program; the S-expr is what hashes, serializes,
  and feeds the rest of the pipeline.

---

## 2. Two artifacts: **specs** and **definitions**

> **Terminology.** "Spec" here means a *logical specification* — axioms/
> constraints, possibly with many models. **Not** the kernel's `TypeSpec` /
> `TermSpec` (the content-addressed handle types in `covalence-core`,
> [`type-hierarchy.md`](../kernel/type-hierarchy.md)); those are *implementations*.
> A surface **definition** elaborates to a `TypeSpec`/`TermSpec`; a surface
> **spec** elaborates to axioms.

The most important distinction in the surface language:

| | **Spec** (loose) | **Definition** (tight) |
|---|---|---|
| says | *constraints* a theory must satisfy | a concrete kernel object |
| shape | clauses (disjunctions of equations) | a `let`-body or selector predicate |
| models | possibly many | exactly one (up to the kernel's equality) |
| elaborates to | axioms / characterizing theorems | `TypeSpec` / `TermSpec` |

A spec is *what option is*. A definition is *the option we built*. They are
connected by **discharge**: prove the spec categorical (all models isomorphic) or
a symbol uniquely determined, and a definition is admitted as *the* realization
of the spec — with the existence/uniqueness obligation proved, not postulated.
This is the pattern the roadmap already describes for `natRec` (it *exists* from
its ε-uniqueness predicate); the surface syntax makes it general.

The concrete `#theory`/`#def`/`#thm`/`#spec`/`#clause` directives, the `option`
worked example (spec form → definition form → the end-to-end mapping), and the
`(#by …)` / `#comp` proof forms are in
[`surface-compiler.md`](./surface-compiler.md) §3.0 — that doc is canonical where
this one's older notation differs.

---

## 3. The questions we can ask

The surface syntax should let us *state* (and the kernel/metatheory *prove*):

```scheme
(spec a |- spec b)              ;; does spec A entail spec B?
(spec a |- unique (spec b))     ;; does spec A determine B uniquely?
(|- categoricity (spec a))      ;; is spec A categorical (models all ≅)?
```

These bridge §2's *loose* world to its *tight* world:

- **entailment** (`spec a |- spec b`) is theory interpretation — the
  symbolic-metatheory morphisms of [`metatheory.md`](../logics/metatheory.md).
- **uniqueness** is the discharge condition for turning a declared symbol into a
  `#def` (the ε-uniqueness predicate pattern).
- **categoricity** justifies treating a spec as *the* definition up to
  isomorphism — the cleanest discharge.

---

## 4. Content addressing (future)

The endgame, deliberately deferred:

1. Each directive (`#def`, `#thm`, `#clause`, `#tydecl`) is serialized to its
   canonical low-level S-expression and **hashed** (BLAKE3, via
   `covalence-hash`/`O256`, the scheme already used to content-hash terms and
   types).
2. References between fragments are **by hash**, not by name. `#import` resolves
   to a content-address; a theory is a *graph of fragments*.
3. Identical definitions deduplicate; a proof is reusable across any theory that
   imports the fragments it depends on; nothing is tied to a single binary.

This is where the surface syntax meets the store
([`VISION.md`](../vision/VISION.md), the `covalence-store` content-addressed blob
layer). Until then, fragments are named within a file and the Rust elaborator
resolves them by name.

---

## 5. Migration path

1. **Elaborator first.** Build the surface → low-level-S-expr → kernel-object
   elaborator in Rust. The kernel rules are unchanged.
2. **Port the catalogue.** Re-express `defs/{logic,nat,int,option,list,prod,…}`
   and the `init/` proofs as surface files; the Rust versions become the golden
   test (surface must produce the *same* checked theorems).
3. **Flip the source of truth.** Once parity holds, the surface files are
   canonical and the Rust catalogue is generated/retired.
4. **Content-address.** Layer §4 on top.

Throughout, **the kernel TCB and its inference rules do not change** — the
surface syntax is an authoring and linking layer, never a new source of trust.
