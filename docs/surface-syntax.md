# Covalence — Surface Syntax

> **STATUS: WORKING DRAFT / DESIGN SKETCH.** Fleshes out the original
> scratch sketch (`docs/sketches/SAMPLE.md`). Describes the *high-level*
> syntax we want for (a) **specifying theories** and (b) **writing the
> definitions and proofs that today live as hand-written Rust** in
> `covalence-core` (`defs/`, `init/`) and `covalence-hol` (`init/`,
> `proofs/`). Nothing here is implemented yet; this is the target.
>
> See also: [`surface-compiler.md`](./surface-compiler.md) (the *language* this
> syntax feeds — theories and their many models across many logics, and the
> multi-stage compiler that unifies `surface/` + `script/`),
> [`observers.md`](./observers.md) (how untrusted code feeds
> facts into the kernel), [`metatheory.md`](./metatheory.md) (theories,
> derivations, and models as first-class objects),
> [`kernel-design.md`](./kernel-design.md) (the kernel TCB this
> elaborates down to).

---

## 1. Why a surface syntax

Right now every definition and every proof in the system is **Rust**.
A type like `option` is a `TypeSpec` built in `defs/option.rs`; its
constructors are `TermSpec`s built with the `poly_let_term!` macro; the
theorems about it (`some_ne_none`, exhaustiveness, the recursor
equations) are hand-assembled in `init/option.rs` by threading kernel
rules. This is the *right* substrate — it is small, auditable, and lives
inside the TCB boundary — but it is a terrible *authoring* surface:

- A one-line definitional equation (`case (some a) b f = f a`) becomes
  a dozen lines of `Term::app`/`Thm::trans`/`cong_arg` plumbing.
- There is no separation between *what* a theory says and *how* we
  realize it in the kernel.
- Definitions cannot be referenced, shared, or content-addressed; they
  are Rust symbols compiled into one binary.

**The goal:** a high-level S-expression syntax in which we can write
theories, definitions, and proofs directly, that *elaborates* down to
the existing kernel objects and rules. Over time we migrate the
`defs/`/`init/` catalogue out of Rust and into this syntax, and the Rust
becomes purely the *elaborator + checker*. Later still, each fragment of
syntax becomes a **content-addressed object** and theories are *linked*
graphs of fragments (see §7).

The surface syntax sits *above* the canonical low-level S-expressions
already emitted by `covalence-hol` (the `(app …)`, `(abs …)`,
`(thm (hyps …) (concl …))` forms in `crates/covalence-hol/src/sexp.rs`).
That low-level form is the *elaboration target* and serialization
format; the surface form is what a human writes.

### 1.1 The north star: declarative meaning, pluggable computation

The surface syntax is, in the limit, a **high-level, Haskell-like
language** — algebraic data types, typed functions, equations — but with
one decisive twist: **it has no fixed operational semantics.**
*Reduction / computational behaviour is left entirely to the kernel.*

In an ordinary functional language, `case (some a) b f` *reduces* to
`f a` by a fixed evaluator baked into the compiler. Here, `case (some a)
b f = f a` is a *theorem* the kernel can establish, and **how** it gets
established is open:

- by a **proof tactic** (the `(by …)` scripts of §5),
- by an **LLM** proposing the rewrite / derivation (untrusted — the
  kernel checks it),
- by a **WASM-compiled decider** that computes the normal form and emits
  a checkable certificate ([`observers.md`](./observers.md)).

Because every one of these routes terminates in the *same* kernel rules,
the computation strategy is **fully pluggable without ever compromising
soundness**. Swap a naive rewriter for an LLM-guided one for a
WASM-JITted one and the set of provable theorems does not change — only
the *cost* of reaching them. (This is also the deeper reason for the
HOL-ω direction in [`metatheory.md`](./metatheory.md) §5.2: a genuinely
Haskell-like *type* language wants higher-kinded type-constructor
variables.)

Generalized one step further, this is **handler dispatch**: reduction,
rewriting, and *unification* are open-ended operations the tactic engine
*requests* and the **environment supplies a handler** for — so a
first-order, higher-order, dependent-type, or domain-specialized
(arithmetic-aware `Bits[n+m]` unifier, …) handler set makes a *different
logic* feel native through the *same* surface. The proof-theoretic
treatment is [`metatheory.md`](./metatheory.md) §7; the user-facing /
product framing is [`frontend.md`](./frontend.md) §4. The seed exists
today: the script layer's `Env` is already the dispatcher, and
`Env::apply_unify` / `Env::rw_unify` are registered seams kept separate so
a custom unifier can be installed later.

### 1.2 Analogy: SQL with set theory, and an LLM query planner

The same idea in one sentence: **imagine writing queries in SQL, except
the query language is set theory (HOL) and the query planner can be an
LLM.**

- In SQL you write *what* you want (declarative); the **query planner**
  decides *how* to execute it; the engine guarantees the answer matches
  the query.
- Here you write *what* is true in the surface language (declarative);
  the **planner** — a tactic, an LLM, a WASM decider — decides *how* to
  derive it; the **kernel** guarantees the result is genuinely a
  theorem.

The planner can be arbitrarily clever, learned, or simply wrong: a bad
plan is slow or fails, but it is never *unsound*. That is precisely what
makes "the query planner can be an LLM" a safe thing to say out loud.

### 1.3 Everything is a pure S-expression

The language is **pure S-expressions with no sugar**. There is no infix
syntax and no surface-level shorthand: every reserved word is a
**`#`-headed builtin**, and the parser (`surface::parse` /
`surface::parse_str`) accepts *only* these forms — nothing desugars.

The arrows, colons, and rewrite arrows that still appear in this
document — `'a -> 'b`, `none : option 'a`, `lhs => rhs` — are **informal
notation in the prose of this doc only**; they are *not* part of the
language and are *not* accepted by the parser. The real forms are:

| informal notation in this doc | actual (and only) form |
|---|---|
| `'a -> 'b` | `(#fn 'a 'b)` |
| `none : option 'a` | `(#sig none (option 'a))` |
| `lhs => rhs` | `(#rw lhs rhs)` |
| `(= a b)` | `(#eq a b)` |
| `λa. body` / `(lam a body)` | `(#lam a body)` |
| `(newtype …)` | `(#newtype …)` |
| `(by …)` | `(#by …)` |

A token's **lexical class is a pure function of its spelling**, so the
parser never needs scope to route it:

- **`#…`** — a **builtin** keyword. This covers *both* the directive
  heads (`#theory`, `#def`, `#thm`, …) *and* every type/term form head
  (`#fn`, `#lam`, `#eq`, `#sel`, `#abs`, `#rep`, …). A `#foo` that is not
  a known builtin is a *malformed* token, not a name — the parser rejects
  it.
- **`'…`** — a **type variable** (`'a`, `'b`).
- **everything else** — an ordinary **name**, of two kinds: a *dotted
  catalogue* reference into `defs/` (`coprod.case`, `option.some`,
  `unit.nil`) or a *local* name (a bound variable or a symbol the
  enclosing `#theory` declares: `option`, `some`, `e`, `f`). Whether a
  local name is a bound variable or a declared constant is the
  *elaborator's* decision; the parser only records the token.

So the §4.1 `option` spec, written out in the real pure syntax, is:

```scheme
(#theory option
  (#tydecl
    (option 'a #ty))
  (#decl
    (#sig none (option 'a))
    (#sig some (#fn 'a (option 'a)))
    (#sig case (#fn (option 'a) 'b (#fn 'a 'b) 'b)))
  (#clause
    (#rw e none)
    (#rw e (some a)))
  (#clause
    (#rw (case none b f) b))
  (#clause
    (#rw (case (some a) b f) (f a))))
```

The remaining sections of this doc keep writing the lighter informal
notation for legibility, but remember it is just exposition: the table
above is the whole story, and only the right-hand column is a language.

### 1.4 The term sublanguage (and lifting it into the TCB)

One fragment of the language is special enough to name on its own: the
**term sublanguage**, the grammar that `#def` bodies and the leaves of
`(#by …)` proofs are written in. It is a **simply-typed lambda
calculus** over the kernel's two logical primitives and the `defs/`
catalogue:

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

1. **It supports lambdas.** `#lam` is the one non-trivial binder, and it
   is what lets the sublanguage express the `defs/` bodies at all — `some
   ≡ λa. abs (inl a)` becomes `(#lam a (#abs option ('a) (inl a)))`,
   one-for-one with the Rust `let`-body.
2. **It has no operational semantics of its own.** Consistent with §1.1,
   the sublanguage *names* terms; it never *reduces* them. `case (some a)
   b f = f a` is a theorem the kernel establishes, not a rewrite the
   sublanguage performs.

Because it is this small and this closed, the term sublanguage is the
natural candidate to eventually **move into the TCB**: a trusted
elaboration of just these constructors into kernel `Term`s would let us
write the `defs/` catalogue *in this sublanguage* instead of in
hand-threaded `Term::app` / `Term::abs` Rust. The directive and proof
layers stay firmly outside the TCB (they only ever *produce checkable
obligations*); the term sublanguage is the one piece we may choose to
trust directly, so it is kept as a sharply-delimited grammar from the
start. A first sketch of the AST — and a parser (`parse` / `parse_str`)
lowering pure S-expressions into it — lives in
[`crates/covalence-hol/src/surface/`](../crates/covalence-hol/src/surface/).

---

## 2. Two artifacts: **specs** and **definitions**

> **Terminology.** "Spec" here means a *logical specification* — a set of
> axioms/constraints, possibly with many models. This is **not** the
> kernel's `TypeSpec` / `TermSpec` (the content-addressed handle types in
> `covalence-core`, see [`type-hierarchy.md`](./type-hierarchy.md)); those
> are *implementations*. A surface **definition** is what elaborates to a
> `TypeSpec`/`TermSpec`; a surface **spec** elaborates to axioms.

The single most important distinction in the surface language:

| | **Spec** (loose) | **Definition** (tight) |
|---|---|---|
| says | *constraints* a theory must satisfy | a concrete kernel object |
| shape | clauses (disjunctions of equations) | a `let`-body or selector predicate |
| models | possibly many | exactly one (up to the kernel's equality) |
| elaborates to | axioms / characterizing theorems | `TypeSpec` / `TermSpec` |

A spec is *what option is*. A definition is *the option we built*. They
are connected by **discharge**: prove the spec is categorical (all
models isomorphic) or that a symbol is uniquely determined, and a
definition can be admitted as *the* realization of the spec — with the
existence/uniqueness obligation proved, not postulated. This is exactly
the pattern the roadmap already describes for `natRec` (it *exists* from
its ε-uniqueness predicate); the surface syntax makes it the general
mechanism.

---

## 3. Directives

A surface file is a sequence of **directives**, each a top-level
S-expression headed by a `#`-keyword. The set below is the starting
proposal; `#tydecl`/`#decl`/`#clause` come straight from the original
sketch, the rest are the natural completion.

| Directive | Purpose | Elaborates to |
|---|---|---|
| `#theory` | open a named theory scope | a module / namespace |
| `#tydecl` | declare a type former + its kind | a `TypeSpec` *shape* (carrier TBD) |
| `#decl` | declare constants with signatures | `TermSpec` declarations (sig only) |
| `#clause` | an equational / Horn constraint | an axiom or characterizing theorem |
| `#def` | a tight definition (body) | a `TypeSpec`/`TermSpec` with a body |
| `#thm` | a named theorem + its proof | a checked `Thm` |
| `#import` | pull in another theory / fragment | a dependency edge (see §7) |
| `#spec` | a named axiom that is *any* proposition | an axiom / characterizing theorem |

`#tydecl`, `#decl`, and `#clause` together write a **spec**; `#def` and
`#thm` together write a **definition + its theory**. A real type like
`option` is given *first* as a spec, then *discharged* by a definition.

### 3.1 `#spec P` — axioms that aren't equations

A `#clause` is *equational* (a disjunction of `#rw` rules). But an axiom
need not be an equation — `#spec P` asserts an arbitrary `bool`-valued
proposition `P` directly, so you write `(#spec (mem x (union s t) …))`
rather than the noise of `(#spec (= P true))`. Since every `bool` term
`P` already *is* the proposition "`P = T`", the two are interchangeable;
`#spec P` is just the ergonomic spelling. (`#clause` stays the equational
special case, because equational specs interpret in *more* logics — see
[`surface-compiler.md`](./surface-compiler.md) §1.1.)

---

## 4. Worked example: the `option` theory

### 4.1 As a spec (from the sketch, fleshed out)

```scheme
;; The high-level specification of the `option` type.
(#theory option

  ;; Declare the type former: option takes one type argument 'a and
  ;; yields a type (#ty is its kind).
  (#tydecl
    (option 'a #ty))

  ;; Declare the constants this theory introduces, with signatures.
  (#decl
    (none : option 'a)
    (some : 'a -> option 'a)
    (case : option 'a -> 'b -> ('a -> 'b) -> 'b))

  ;; Exhaustiveness: every option is either none or (some a).
  ;; A #clause is a DISJUNCTION of rules; at least one must hold.
  ;;   - a variable occurring on the LEFT of a rule is universally bound
  ;;   - a variable occurring ONLY on the right is existentially bound
  ;; so this reads:  ∀ e. (e = none) ∨ (∃ a. e = some a)
  (#clause
    (e => none)
    (e => some a))

  ;; The recursor equations. A single-rule clause is just an equation,
  ;; universally closed over its variables.
  (#clause
    (case none b f => b))          ;; ∀ b f.   case none b f     = b
  (#clause
    (case (some a) b f => f a)))    ;; ∀ a b f. case (some a) b f = f a
```

The arrow `=>` is the **rewrite / equality** arrow: a rule `lhs => rhs`
asserts `lhs = rhs`. Variable binding is *positional*, read off the
rule, exactly as annotated in the sketch — no explicit `∀`/`∃` needed,
which is what makes equational specs terse.

This is a *loose* description: any type with these three operations
satisfying these clauses is a model of `option`.

### 4.2 As a definition (what the kernel actually builds)

Today this is `defs/option.rs` + `init/option.rs`. In the surface
syntax it becomes:

```scheme
(#theory option

  ;; option 'a := coprod 'a unit   (a newtype over the carrier)
  (#def option (ty 'a)
    (newtype (coprod 'a unit)))

  (#def some (term ('a -> option 'a))
    (lam a (abs (inl a))))          ;; λa. abs (inl a)
  (#def none (term (option 'a))
    (abs (inr unit.nil)))           ;; abs (inr unit.nil)
  (#def case (term (option 'a -> 'b -> ('a -> 'b) -> 'b))
    (lam o (lam b (lam f
      (coprod.case (rep o) (lam a (f a)) (lam _ b))))))

  ;; Discharge: prove the §4.1 spec holds of this definition.
  (#thm option/exhaustive
    (spec option.exhaustive)
    (by ...))                       ;; proof script, see §5

  (#thm option/some-ne-none
    (concl (not (= (some a) none)))
    (by ...)))
```

The `#def` bodies mirror the Rust `let`-bodies one-for-one (`some ≡ λa.
abs (inl a)` is literally the docstring of `some_spec` in
`defs/option.rs`). The `abs`/`rep`/`inl`/`inr`/`coprod.case` symbols are
the kernel's carrier↔wrapper coercions and the catalogue's dotted names.

### 4.3 The mapping, end to end

| Surface | Current Rust | Low-level S-expr (target) |
|---|---|---|
| `(#tydecl (option 'a #ty))` | `Canonical::Option` shape | — |
| `(#def option (newtype (coprod 'a unit)))` | `TypeSpec::newtype(Canonical::Option, coprod(α, unit))` | `(spec option (tfree a))` |
| `(#def some (lam a (abs (inl a))))` | `poly_let_term!{ some_spec, some(alpha), … some_body() }` | `(term-spec some (tfree a))` w/ body |
| `(#clause (case (some a) b f => f a))` | a proof in `init/option.rs` (e.g. `some_ne_none` and the recursor lemmas) | `(thm (hyps) (concl (eq …)))` |
| `(#thm … (by …))` | hand-threaded `Thm::trans`/`cong_arg` | `(thm (hyps …) (concl …))` |

---

## 5. Proofs in the surface syntax

Today a proof is a Rust function returning `Result<Thm>` that threads
kernel rules by hand (`assume`, `imp_intro`, `all_elim`, `trans`,
`cong_arg`, …). The surface syntax exposes those same rules as a
**tactic / combinator vocabulary** under `(by …)` — an LCF-style script
that bottoms out in the *exact same kernel primitives*, so the TCB does
not grow:

```scheme
(#thm and-comm
  (concl (==> (/\ p q) (/\ q p)))
  (by
    (assume (/\ p q))     ;; {p∧q} ⊢ p∧q
    (and-sym)             ;; {p∧q} ⊢ q∧p
    (imp-intro (/\ p q)))) ;; ⊢ (p∧q) ⟹ (q∧p)
```

This is the surface form of `and_comm` in
`crates/covalence-hol/src/init/logic.rs`. The combinators are not new
trusted code — they are names for the kernel rules already documented
with `Soundness:` docstrings. (The richer "elaboration / unification"
story — schematic proof terms, higher-order matching — is a *future*
layer; see [`metatheory.md`](./metatheory.md) §on layers.)

### 5.1 Calculational proofs (`#comp`) and the default handler

The everyday shape of an equational argument is a *chain* — `a = b = c =
… = g` — with a justification per step. `#comp` is that chain as a
first-class proof form: it folds `trans` over the steps to prove the
end-to-end equality.

```scheme
(#comp a
  (= b (reduce-prim …))   ;; a = b, justified by a tactic
  (= c (rw lemma))        ;; b = c
  (= d)                   ;; c = d — justification OMITTED → the default handler
  (= e (apply foo)))      ;; d = e
;; ⊢ a = e
```

The head term `a` starts the chain; each step gives a relation, the next
term, and an **optional** justification (any `(by …)` tactic/derivation).

**Default handler + omit-if-it-discharges.** A block may set a default
handler; any step whose justification is omitted is closed by it:

```scheme
(#comp a #:by reduce
  (= b)                   ;; a = b by `reduce`
  (= c (rw lemma))        ;; explicit override
  (= d))                  ;; c = d by `reduce`
```

Omitting a step's proof means "let the default handler prove `prev =
rhs`"; if it cannot, that step is a diagnostic pointing exactly there, not
a silent gap. The natural default is **the active model's equational
handler** — the handler dispatch of
[`surface-compiler.md`](./surface-compiler.md) §2/§4. So in a `nat` model
the default is `reduce`; in a *monoid* model it is the monoid normalizer;
in a reified-logic model it is that logic's decision procedure. `#comp` is
thus a clean *consumer* of handler dispatch — the calculation's routine
steps close themselves with whatever rewriter the model installs, and the
author hand-justifies only the interesting ones. (This is "declarative
meaning, pluggable computation," §1.1, at proof-step granularity.)

**Heterogeneous relations (later).** The general form mixes relations
whose transitivity composes — `a = b ≤ c < d ⊢ a < d` — by looking up a
transitivity rule per adjacent pair (cf. Lean `calc` / Isabelle `also`).
Start with `=` (and `⟹` / `⟺`); generalize once a relation/transitivity
registry exists.

---

## 6. The questions we can ask

The sketch closes with the judgement forms the surface syntax should let
us *state* (and the kernel/metatheory should let us *prove*):

```scheme
(spec a |- spec b)              ;; does spec A entail spec B?
(spec a |- unique (spec b))     ;; does spec A determine B uniquely?
(|- categoricity (spec a))      ;; is spec A categorical (models all ≅)?
```

These are the bridge from §2's *loose* world to its *tight* world:

- **entailment** (`spec a |- spec b`) is theory interpretation — the
  symbolic-metatheory morphisms of [`metatheory.md`](./metatheory.md).
- **uniqueness** is the discharge condition for turning a declared
  symbol into a `#def` (it's the ε-uniqueness predicate pattern).
- **categoricity** justifies treating a spec as *the* definition up to
  isomorphism — the cleanest possible discharge.

---

## 7. Content addressing (future)

The endgame, deliberately deferred:

1. Each directive — every `#def`, `#thm`, `#clause`, `#tydecl` — is
   serialized to its canonical low-level S-expression and **hashed**
   (BLAKE3, via `covalence-hash`/`O256`, the scheme already used to
   content-hash terms and types in `covalence-hol` — see
   `covalence-hol/src/hash.rs`).
2. References between fragments are **by hash**, not by name. `#import`
   resolves to a content-address; a theory is a *graph of fragments*.
3. Identical definitions deduplicate; a proof is reusable across any
   theory that imports the fragments it depends on; nothing is tied to a
   single compiled binary.

This is where the surface syntax meets the store
([`VISION.md`](./VISION.md), the `covalence-store` content-addressed
blob layer). Until then, fragments are named within a file and the Rust
elaborator resolves them by name.

---

## 8. Migration path

1. **Elaborator first.** Build the surface → low-level-S-expr →
   kernel-object elaborator in Rust. The kernel rules are unchanged.
2. **Port the catalogue.** Re-express `defs/{logic,nat,int,option,list,
   prod,…}` and the `init/` proofs as surface files; the Rust versions
   become the golden test (surface must produce the *same* checked
   theorems).
3. **Flip the source of truth.** Once parity holds, the surface files
   are canonical and the Rust catalogue is generated/retired.
4. **Content-address.** Layer §7 on top.

Throughout, **the kernel TCB and its inference rules do not change** —
the surface syntax is an authoring and linking layer, never a new source
of trust.
