# Covalence — Surface Syntax

> **STATUS: WORKING DRAFT / DESIGN SKETCH.** Fleshes out the original
> scratch sketch (`docs/sketches/SAMPLE.md`). Describes the *high-level*
> syntax we want for (a) **specifying theories** and (b) **writing the
> definitions and proofs that today live as hand-written Rust** in
> `covalence-core` (`defs/`, `init/`) and `covalence-hol` (`init/`,
> `proofs/`). Nothing here is implemented yet; this is the target.
>
> See also: [`observers.md`](./observers.md) (how untrusted code feeds
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

---

## 2. Two artifacts: **specs** and **definitions**

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

`#tydecl`, `#decl`, and `#clause` together write a **spec**; `#def` and
`#thm` together write a **definition + its theory**. A real type like
`option` is given *first* as a spec, then *discharged* by a definition.

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
| `(#clause (case (some a) b f => f a))` | a `cached_thm!` in `init/option.rs` | `(thm (hyps) (concl (eq …)))` |
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
   (BLAKE3, via `covalence-hash`/`O256`, the scheme already used for
   theorems in `covalence-hol`).
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
