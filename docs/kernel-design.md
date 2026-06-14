# covalence-core: kernel design

> **Canonical reference for the current state of the kernel** as of
> 2026-06-13 (branch `kernel-design`). Supersedes
> [`docs/design/proposals/stacked-pure-hol/`](./design/proposals/stacked-pure-hol/),
> which records the historical Pure→HOL evolution.

## 1. What it is

`covalence-core` is an LCF-style HOL Light kernel written in safe
Rust. The TCB is small (~3 KLoC). Its public interface is a single
opaque type `Thm` with rule methods; the only paths to a `Thm` value
are the inference rules below. Soundness reduces to those rules
plus the kernel's commitment to its primitive types' denotational
semantics.

The kernel was a Pure-shaped LF (Isabelle/Pure-style) for several
intermediate revisions; the current shape is **pure HOL Light** with
a couple of well-justified additions:

- HOL Light's 10 inference rules are primitives.
- Well-known HOL Light derived rules (SYM, DISCH, MP, GEN, SPEC,
  MK_COMB-as-cong, ABS-as-cong, ETA_AX) plus the propositional
  connective rules (CONJ / CONJUNCT1,2 / DISJ1,2 / DISJ_CASES /
  ¬-intro / ¬-elim) are also primitives — ergonomics + performance,
  soundness justified by the standard HOL Light derivation in each
  docstring (and, for the connectives, by an executable witness in
  `covalence-hol::proofs::bool`).
- Three non-computational primitive **rules**: **Peano induction on
  `nat`** (`Thm::nat_induct`: base + step ⟹ `∀n. P n`), **ex falso**
  (`Thm::false_elim`: `⊢ F` ⟹ `⊢ p`), and the **`unit` singleton rule**
  (`Thm::unit_eq`: `⊢ a = b` for any `a, b : unit`, since
  `unit := { b : bool | b = T }` is a one-element type). The classic
  induction *axiom* `⊢ ∀P. (P 0 ∧ …) ⟹ ∀n. P n` is a trivial theorem on
  top of the induction rule.
- Spec **abs/rep coercions** (`Term::spec_abs` / `Term::spec_rep`):
  for any derived `TypeSpec`, the typed leaves `abs : carrier → (spec
  args)` and `rep : (spec args) → carrier`. They carry no theorems
  (the bijection equations are derived downstream), so adding them is
  sound; they let the `defs/` catalogue *define* constructors like
  `option.some := λa. abs (coprod.inl a)`.
- Two accelerated reduction rules (`reduce_prim`, `unfold_term_spec`)
  that emit `⊢ t = canonical_form` for closed-literal computations.
  Sound by the literal's denotation, not a logical postulate.
- Conservative-extension primitives (`define`, `new_type_definition`)
  for introducing fresh constants and subtypes.
- An observer system (`obs_eq`, `obs_true`, `obs_imp`) sound under a
  parametric ε-model — the hook for non-HOL theories (Store, BLAKE3,
  future provers) to inject facts without contaminating the kernel.

The propositional layer (`∧`/`∨`/`¬` rules, `¬p ⇔ (p ⟹ F)`, ex falso,
quantifier intro/elim) is **fully derived** — see
`covalence-hol::{proofs,init}::bool`. The arithmetic tier — `pred`,
`natRec`, addition, multiplication, division, integer induction — is
derivable from `nat_induct` + the rule set + `define` but not yet
done; until those derivations land downstream (slated for the
WASM-based proof rewrite) consumers postulate them via
`Thm::assume(body)`. Each such postulate carries its body as a self-hyp
so the audit chain is visible in any final theorem.

## 2. Files (TCB scope)

```
crates/covalence-core/src/
├── lib.rs             — module declarations + re-exports
├── term/
│   ├── observer.rs    — Observer / ObsTrue / ObsImp / ObsEq traits + Object
│   ├── term.rs        — Term, TermKind (incl. Eq/Select primitives), Def, TypeEnv, type_of_in
│   ├── spec.rs        — TermSpec handle
│   └── set.rs         — TermSet (structurally-shared hyp set backing Ctx)
├── ty/
│   ├── ty.rs          — Type, TypeKind, cached LazyLocks
│   ├── spec.rs        — TypeSpec handle
│   └── list.rs        — TypeList
├── ctx.rs             — Ctx (hypothesis set, structurally shared)
├── subst.rs           — close / open / shift_by / subst_free / subst_tfree_in_* / match_types
├── builtins.rs        — reduce_prim_term + reduce_spec (PRIM_TABLE ptr_id dispatch)
├── hol.rs             — HOL-connective constructors (hol_eq/hol_imp/hol_forall/hol_not/…)
├── thm/
│   ├── mod.rs         — Thm + the equality/connective/induction/observer rules (the LCF API)
│   └── typedef.rs     — define + new_type_definition (conservative extension)
├── error.rs           — Error variants
└── defs/              — TypeSpec / TermSpec catalogue (semi-trusted; see §6)
```

## 3. Types

```
TypeKind                       Constructor          Notes
─────────                      ───────────          ─────
TFree(SmolStr)                 Type::tfree(name)    type variable
Nat                            Type::nat()          kernel-primitive
Bool                           Type::bool()         HOL formula type
Fun(Type, Type)                Type::fun(d, c)      function type
Tycon(SmolStr, Vec<Type>)      Type::tycon(name, args)        named structural tycon
TyConObs(Object, BinderHint,
         Vec<Type>)                                  fresh-identity tycon (typedef result)
Spec(TypeSpec, Vec<Type>)      Type::spec(spec, args)         derived TypeSpec application
```

`Type::int()` returns `Type::spec(int_ty_spec(), [])` where
`int_ty_spec()` is the derived TypeSpec `int := (nat × nat) / ~`
(Grothendieck construction). `Type::bytes()` returns
`Type::spec(bytes_spec(), [])` where `bytes_spec()` is `bytes := list u8`.
`Type::unit()` returns `Type::spec(unit_spec(), [])` where `unit_spec()`
is the bool-subtype `unit := { b : bool | b = T }` (a derived TypeSpec,
no longer a builtin `TypeKind`).

There is **no `TypeKind::Prop`** — the kernel has no Pure meta-prop
type; every formula is `bool`.

## 4. Terms

```
TermKind                       Constructor              Notes
────────                       ───────────              ─────
Bound(u32)                     Term::bound(i)           de Bruijn index
Free(SmolStr, Type)            Term::free(name, ty)
Const(SmolStr, Type)           Term::const_(name, ty)
App(Term, Term)                Term::app(f, x)
Abs(BinderHint, Type, Term)    Term::abs(hint, ty, body)
Nat(Nat)                       Term::nat_lit(n)         arbitrary-precision literal
Int(Int)                       Term::int_lit(n)
Bool(bool)                     Term::bool_lit(b)        T or F
Blob(Bytes)                    Term::blob(bs)           byte-string literal
Eq(Type)                       Term::eq_op(alpha)       `=` at element type α
Select(Type)                   Term::select_op(alpha)   `ε` (choice) at element type α
Spec(TermSpec, Vec<Type>)      Term::term_spec(spec, ty_args)   derived TermSpec
Obs(Object, Type)              Term::obs(o, ty)         observer leaf
Def(Def)                       Term::def(d)             defined constant
```

**`=` and `ε` are the only logical primitives.** `Eq(α)` has type
`α → α → bool` and `Select(α)` has type `(α → bool) → α`; each is an
ordinary applicable operator (formula `a = b` is `App(App(Eq(α), a), b)`,
the same App-shape as everything else). There is **no Pure
meta-layer** — no `TermKind::Imp/All`, no `Trueprop`, no
`TypeKind::Prop`. Every formula is `bool`-typed.

The propositional connectives and quantifiers — `∧ ∨ ¬ ⟹ ⟺ ∀ ∃` —
are **not kernel variants**. They are ordinary let-style definitions
in `defs/logic.rs` over `=`/`ε`/`T`/`F` (the HOL Light `bool.ml`
bootstrap), e.g. `(∧) ≜ λp q. (λf. f p q) = (λf. f T T)` and
`(!) ≜ λP. P = (λx. T)`. So:

- `Thm::unfold_term_spec(op)` hands back the defining equation
  `⊢ op = <body>` — the hook `covalence-hol` uses to *derive* the
  connectives' intro/elim rules instead of postulating them.
- `Thm::reduce_prim` decides them on `bool` literals by the same
  pointer-match dispatch as the arithmetic specs.

`imp_intro`/`imp_elim`/`all_intro`/`all_elim` remain kernel-provided
derived rules that build/parse the `imp`/`forall` specs (sound by the
standard HOL Light derivations); they are not re-derived from
`deduct_antisym`.

Since `Eq`/`Select` store their element type α directly, they are
well-shaped by construction — there is no instance-type validation to
run (the previous `HolOp` shape check and its `HolOpShape` error are
gone).

## 5. Inference rules (the `Thm` API)

### 5.1 The HOL Light primitive ten

```rust
Thm::refl(t)                            -> Result<Thm>  // ⊢ t = t
Thm::trans(self, other)                                 // ⊢ s = u from ⊢ s = t and ⊢ t = u
Thm::mk_comb(self, arg)                                 // ⊢ f x = g y
Thm::abs(self, name, ty)                                // ⊢ (λx. s) = (λx. t) from ⊢ s = t
Thm::beta_conv(app)                                     // ⊢ (λx. body) arg = body[arg/x]
Thm::assume(p)                                          // {p} ⊢ p,  p : bool
Thm::eq_mp(self, p_thm)                                 // ⊢ q from ⊢ p = q and ⊢ p
Thm::deduct_antisym(self, other)                        // (Γ\{q}) ∪ (Δ\{p}) ⊢ p ⇔ q
Thm::inst(self, name, replacement)                      // INST — free term-var substitution
Thm::inst_tfree(self, name, replacement)                // INST_TYPE — free type-var substitution
```

### 5.2 Derived HOL-Light rules (kernel primitives by the
"easily auditable" rule — each has a `Soundness:` docstring
pointing at the standard HOL Light derivation)

```rust
Thm::sym(self)                                          // SYM
Thm::cong_app(self, arg)                                // = mk_comb (alias)
Thm::cong_abs(self, name, ty)                           // = abs (alias)
Thm::imp_intro(self, phi)                               // DISCH
Thm::imp_elim(self, hyp)                                // MP
Thm::all_intro(self, name, ty)                          // GEN
Thm::all_elim(self, witness)                            // SPEC
Thm::eta_conv(abs)                                      // ETA_AX
```

The propositional connectives `∧` / `∨` / `¬` are defined constants
(`defs/logic.rs`), and their intro / elim rules are likewise provided
as fast kernel constructors with `Soundness:` docstrings. The
*executable* derivation — the soundness witness, and the basis for a
future "paranoid mode" that runs it instead of trusting the
constructor — lives and is tested in `covalence-hol::proofs::bool`
(cross-checked against these methods):

```rust
Thm::and_intro(self, other)                             // CONJ
Thm::and_elim_l(self) / and_elim_r(self)                // CONJUNCT1 / 2
Thm::or_intro_l(self, q) / or_intro_r(self, p)          // DISJ1 / 2
Thm::or_elim(self, left, right)                          // DISJ_CASES
Thm::not_intro(self)                                     // p⟹F ⊢ ¬p
Thm::not_elim(self, other)                               // ¬p, p ⊢ F
```

### 5.3 Structural

```rust
Thm::weaken(self, target)                               // Δ ⊢ φ from Γ ⊢ φ and Γ ⊆ Δ
```

### 5.4 Conservative-extension primitives

```rust
Thm::define(name, body) -> Result<Thm>
    // Allocates a fresh Def (unique Arc identity).
    // Returns ⊢ Def(name, body) = body.
    // Phantom-tfree check: every tvar inside body must reach body_type
    // (otherwise inst_tfree could later corrupt the body).

Thm::new_type_definition(hint, abs_hint, rep_hint, witness)
    -> Result<TypeDef>
    // Witness: Γ ⊢ P x for some x : α and P : α → bool.
    // Returns a TypeDef bundle:
    //   tau            — fresh type constructor parametric in α's tvars
    //   abs            — α → τ (Obs leaf, fresh Arc identity)
    //   rep            — τ → α (Obs leaf, fresh Arc identity)
    //   abs_rep        — Γ ⊢ ∀a:τ. abs (rep a) = a
    //   rep_abs_fwd    — Γ ⊢ ∀r:α. P r ⟹ rep (abs r) = r
    //   rep_abs_back   — Γ ⊢ ∀r:α. rep (abs r) = r ⟹ P r
    // Standard HOL Light typedef. Sound under conservative extension.
```

### 5.5 Accelerated reduction rules (not logical axioms — each is a
sound one-shot computation step)

```rust
Thm::reduce_prim(t) -> Result<Thm>
    // Closed-form arithmetic on literal operands. Returns ⊢ t = canonical.
    // Catalogue:
    //   App(App(Eq(_), lit_a), lit_b)         →  Bool(a == b)
    //   App(nat_succ_spec, Nat(n))            →  Nat(n+1)
    //   App(nat_pred_spec, Nat(n))            →  Nat(max(n-1, 0))
    //   App(App(nat_add_spec, Nat(a)), Nat(b)) →  Nat(a+b)
    //   ... similarly for mul/sub/div/mod/pow, int_*, bytes_*
    // Dispatches by TermSpec ptr_eq against catalogue handles.
    // Returns Err(NotReducible) for shapes not in the table.

Thm::unfold_term_spec(t) -> Result<Thm>
    // For a let-style TermSpec (body has same type as carrier).
    // Returns ⊢ Spec(spec, args) = subst_tfree(spec.tm, tvars, args).
    // Each TermSpec is its own opaque atom; the unfolding equation is
    // a let-binding for that atom. Sound regardless of what users put
    // in user-constructed TermSpecs.
```

### 5.6 Observer rules

```rust
Thm::obs_eq<O: ObsEq>(expr1, expr2, hint) -> Result<Thm>
    // ⊢ expr1 = expr2 if both are obs-leaf-headed applications
    // of the same observer Rust-type O, the same final type, and
    // O::obs_eq returns true.

Thm::obs_true<O: ObsTrue>(expr, hint)
    // ⊢ expr for bool-typed obs application if O::obs_true returns true.

Thm::obs_imp<O: ObsImp>(expr, hyps, hint)
    // ⊢ h0 ⟹ h1 ⟹ ... ⟹ expr for bool-typed obs application
    // if O::obs_imp returns true.
```

**All three rules are unconditionally sound regardless of what the
observer's policy returns**, under the parametric ε-model: each Rust
observer type `O` gets its own ε-family in the model
(`ε_O(α → β) = λ_. ε_O(β)`, `ε_O(bool) = ⊤`), so the rule's
conclusions are always true in the model. The policy is a per-`O`
choice of which true facts to expose, not a soundness obligation.
Different `O` and `O'` get independent ε-families, so a bug in
`WasmObs::obs_eq` cannot affect `HolLight` theorems.

### 5.7 The non-computational primitive rules

```rust
Thm::nat_induct(base, step) -> Result<Thm>
    // base : Γ₁ ⊢ p 0   step : Γ₂ ⊢ p n ⟹ p (succ n)  (n free, generic)
    //   ⟹  Γ₁ ∪ Γ₂ ⊢ ∀n:nat. p n
    // Sound because Type::nat() denotes the standard naturals generated
    // by 0 and succ. (The motive p and variable n are read back from
    // the conclusion shapes; n must be free neither in p nor in Γ₂.)

Thm::false_elim(self, p) -> Result<Thm>
    // Γ ⊢ F  ⟹  Γ ⊢ p   (ex falso; F is the Bool(false) literal)

Thm::unit_eq(a, b) -> Result<Thm>
    // a, b : unit  ⟹  ⊢ a = b
    // Sound because unit := { b : bool | b = T } is a one-element type,
    // so any two inhabitants denote the same element.
```

**That is the entire non-computational axiom surface.** The classic
induction *axiom* `⊢ ∀P. (P 0 ∧ (∀n. P n ⟹ P (succ n))) ⟹ ∀n. P n` is a
trivial theorem over `nat_induct` (see
`covalence-hol::nat_axioms::nat_induction`). Every other arithmetic /
logic fact is derivable from these rules + the rule set + `define`.

## 6. `defs/` — the spec catalogue (semi-trusted)

`crates/covalence-core/src/defs/` is the catalogue of derived
TypeSpec / TermSpec entries the kernel ships out of the box. It
sits between the TCB and the user: users CAN construct their own
`TypeSpec::new(symbol, ty, tm)` / `TermSpec::new(symbol, ty, tm)`
values, but those go through the same kernel rules
(`unfold_term_spec`, `Type::spec`) as catalogue entries — no
special trust is needed.

| Module          | Provides                                              |
|----------------|-------------------------------------------------------|
| `canonical.rs`  | `Canonical` symbol enum (kernel-shipped TypeSpec/TermSpec names) |
| `spec.rs`       | `TypeSpec` / `TermSpec` handle types                    |
| `symbol.rs`     | `Symbol` trait + Opaque/Transparent opacity            |
| `nat.rs`        | `nat_succ`, `nat_pred`, `nat_add`, `nat_mul`, …, `nat_rec` |
| `int.rs`        | `int_ty_spec`, `int_succ`, `int_pred`, `int_add`, …     |
| `blob.rs`       | `bytes_spec`, `bytes_cat`, `bytes_len`, …                |
| `set.rs`        | `set 'a := 'a → bool`                                    |
| `coprod.rs`     | `bit` / `u2` / `u4` / `u8` / `u16` / … / `u512` / `coprod` |
| `prod.rs`       | `prod`, `signed1`, `signed2`                            |
| `list.rs`       | `list` + `cons` / `head` / `tail` / `map` / `filter` / …   |
| `option.rs`     | `option`                                                 |
| `rel.rs`        | `rel`, `preord`, `pord`, `per`, `part`                   |
| `stream.rs`     | `stream`                                                 |
| `result.rs`     | `result`                                                 |
| `rat.rs`        | `rat := fieldOfFractions int`                            |
| `real.rs`       | `real := { rat } close ratLe`                            |
| `floats.rs`     | `f32`, `f64`                                              |

The catalogue is the binary-data substrate the kernel was designed
for: every TypeSpec resolves into a content-addressable shape, and
every TermSpec has either a body (let-style) or a selector predicate
(def-style via Hilbert ε).

## 7. The hypothesis context (`Ctx`)

`Ctx` is a hash-tree-like `Option<Arc<BTreeSet<Term>>>` carrying
the hypotheses of a `Thm`. Empty contexts don't allocate; non-empty
contexts share `Arc` across many `Thm`s. Operations:

```rust
Ctx::new()                    // empty
Ctx::singleton(t)             // {t}
ctx.union(&other)             // O(1) when either side is empty / Arc::ptr_eq
ctx.is_subset(&other)         // weaken precondition
ctx.remove(&t)                // DISCH / deduct_antisym hyp cleanup
ctx.insert(&t)                // assume
```

## 8. The trust boundary

**INSIDE the TCB** (audit these — bugs = false theorems):

- `term/` (Term/Type/Eq/Select/Object structural representation)
- `ctx.rs` (hypothesis set)
- `subst.rs` (substitution and de Bruijn shifting)
- `builtins.rs` (reduce_prim_term, reduce_spec)
- `hol.rs` (axiom term + connective constructors)
- `thm.rs` (the rule API)
- `error.rs` (error variants)

**SEMI-TRUSTED** (audit at user-call time, not at kernel-rule time):

- `defs/` — the TypeSpec/TermSpec catalogue. User-constructed specs
  go through the same kernel rules; the catalogue is just the
  kernel-shipped starting set.

**OUTSIDE the TCB** (may be arbitrarily clever; a bug here cannot
produce a false `Thm`):

- `covalence-hol` — HOL-Light builder API (HolLightCtx),
  postulated downstream axioms (nat_axioms, int_axioms), serialization
  (hash.rs, sexp.rs).
- `covalence-store`, `covalence-shell`, `covalence-repl`,
  `covalence-serve`, every higher-level crate.

## 9. Soundness notes

### Things the kernel commits to (the "model" assumptions)

- `Type::nat()` denotes the standard naturals.
- `Type::bool()` has exactly two distinct inhabitants `T` and `F`.
- `Type::unit()` has exactly one inhabitant.
- Distinct kernel literals at the same kind denote distinct values
  (Nat(5) ≠ Nat(6), Int(-3) ≠ Int(3), Blob(`b"hi"`) ≠ Blob(`b"bye"`),
  Bool(true) ≠ Bool(false)).
- HOL `=` is interpreted as equality in the model.

These commitments are what makes `nat_induct` (and `false_elim`)
sound, what makes `reduce_prim`'s `T = F → F` sound, etc.

### Things the kernel does NOT do

- It does not validate that user-supplied bodies in `TermSpec::new`
  match any canonical computation. A user can label two distinct
  TermSpecs `Canonical::NatAdd` with two different bodies — they're
  distinct opaque atoms, both individually consistent, no
  contradiction.
- It does not enforce uniqueness of `Thm::define` names. Two
  `define("foo", body)` calls produce two distinct `Def` atoms,
  both with `Def_i = body`. No contradiction.
- It does not have built-in support for higher-order rewriting,
  proof tactics, or any automation. Those live downstream.

### A coupling the catalogue MUST respect

When a catalogue spec is reachable by **both** `reduce_prim` and
`unfold_term_spec` — i.e. it is a `let_term!` (let-style body) **and**
listed in `builtins::PRIM_TABLE` (e.g. `nat.add`, `nat.mod`,
`bytes.cat`) — the kernel commits to two facts about it:
`spec lit… = reduce_prim(spec lit…)` and `spec = body`. These are
consistent **only if the body denotes the same function `reduce_prim`
computes**, on every input. A divergence makes the theory inconsistent
(it derives `litₐ = lit_b` for distinct literals, hence `⊢ F`).

The risk is **derivable** — and so guarded by
`tests/audit_reduce.rs::audit_reduce_matches_body` — exactly when the
body bottoms out in `reduce_prim`-reducible sub-ops, so the body itself
reduces to a literal. That is the case for `nat.mod` (`n − (n/m)·m`) and
`int.div` / `int.mod` (built from `intSgn`/`intAbs`/`intMul`/`intSub` +
`natDiv`/`natToInt`); for those, `x / 0 = 0` and `x mod 0 = x` (the
Euclidean convention) are forced. The Grothendieck / `iter` ops
(`nat.add`, `int.add`, …) instead bottom out at `ε` (`natRec`,
`abs`/`rep`); their bodies are stuck and cannot be reduced to a literal,
so they are sound by the model alone with no derivable contradiction
(see `iter_based_bodies_are_stuck`). Declaration-only specs (`tm = None`,
e.g. the `uN`/`sN` conversions) have no body and are likewise immune.

**A second coupling — `spec_ax` vs `reduce_prim`.** `Thm::spec_ax`
exposes a *def-style* spec's selector predicate `p` as a kernel fact
(`(p w) ⟹ p(t)`, the per-spec choice axiom). For a def-style spec that
is **also** in `PRIM_TABLE` — currently only `nat.le` and `nat.lt` — the
kernel then commits to *both* `(p w) ⟹ p(t)` and the `reduce_prim`
values, so they must be jointly satisfiable: **every function satisfying
`p` must agree with `reduce_prim` on all reducible inputs.** If `p` were
weak enough to admit a function disagreeing with `reduce_prim` at a
reducible point, `spec_ax` (discharging `p w` for that function) plus
`reduce_prim` would derive `litₐ = lit_b` — `⊢ F`. `nat.le`/`nat.lt`'s
predicates are their four defining recursion equations, which have a
*unique* solution (the real `≤`/`<`) that `reduce_prim` computes, so
they are safe. The guard
`tests/audit_reduce.rs::audit_reduced_def_specs_satisfy_their_predicate`
checks `reduce_prim` satisfies those equations; uniqueness is by
construction. **Any future def-style spec added to `PRIM_TABLE` must
satisfy this** (give it a predicate with a unique solution = its
reduction, and add it to that guard).

### Audit confidence (as of 2026-06-14)

A third audit pass (2026-06-14) found and fixed one real hole: `nat.mod
n 0` reduced to `0` while its let-style body `λn m. n - (n/m)*m`
evaluates to `n` at `m = 0`, so `unfold` + `reduce_prim` derived
`n = 0` (`⊢ 0 = 5` reproduced unconditionally). The reduction now
returns `n` (the Euclidean convention `n mod 0 = n`), matching the body;
see the coupling note above. The same pass added the
`reduce_prim`/`unfold` consistency guards and hardened two non-soundness
panics (`reduce_prim` on an ill-typed `Eq` application; `match_types`
missing its `Bool`/`Spec` arms, panicking in `Def::body`).

A fourth pass (2026-06-14) audited the `high-hol` merge, which added new
TCB primitives/axioms: `succ` as a first-class `TermKind::Succ`
(monomorphic `nat → nat`) with the Peano freeness rules `Thm::succ_inj`
/ `Thm::zero_ne_succ`; Hilbert choice `Thm::select_ax` for `ε`; and
`Thm::spec_ax` (per-def-spec choice). All are standard, sound under the
existing model commitments (standard naturals + classical HOL with
choice); `select_ax`/`spec_ax` coexist with the observer ε-families
(distinct operators). `Succ` is handled as a closed, tvar-free no-op
leaf in every substitution / predicate walk. The pass surfaced the
second coupling documented above (`spec_ax` × `reduce_prim` on `nat.le`/
`nat.lt`) and added its guard; no hole.

With these the kernel has no known soundness holes. Every rule produces
only theorems true in any model that interprets the foundational types
canonically and assigns ε-families per observer Rust-type.

Remaining hardening opportunities (not soundness gaps):

- Property-based tests for substitution commutativity.
- Cross-validation against HOL Light proper on real theorems.
- Formal model of the rule set in Lean/Coq for an independent
  consistency check.
- Doc-comment audit (some references to Pure-meta still in
  legacy docstrings outside `covalence-core`).

## 10. Migration history

The kernel has gone through several large refactors on the
`kernel-design` branch:

1. **Pure → HOL collapse**: the original `covalence-pure` crate was a
   strict Isabelle/Pure-shaped LF (`Term::imp` / `Term::all` /
   `Term::eq` as Pure meta-connectives, `HolOp::Trueprop` as
   `bool → prop` coercion). Folded into `covalence-core` with HOL
   primitives in the kernel, then progressively collapsed the Pure
   meta-layer away: the bridge axioms (`eq_reflection`,
   `forall_reflection`, `imp_reflection`) gone, Pure rules deleted,
   `TermKind::Imp/All/Eq` and `HolOp::Trueprop` and `TypeKind::Prop`
   removed.

2. **Removed all kernel `Prim::*` arithmetic operators**: each became
   a TermSpec constant matched on by `ptr_eq` in `reduce_spec` for
   closed-form reduction.

3. **`int` and `bytes` derived**: `Type::int()` is now
   `Type::spec(int_ty_spec(), [])` (`int := (nat × nat) / ~`);
   `Type::bytes()` is `Type::spec(bytes_spec(), [])`
   (`bytes := list u8`). Literals (`TermKind::Int(Int)`,
   `TermKind::Blob(Bytes)`) stay as kernel built-ins for binary-data
   efficiency.

4. **Single-axiom kernel**: every kernel axiom except
   `nat_induction` was deleted. `nat_pred_zero`, `nat_pred_succ`,
   `nat_rec_zero`, `nat_rec_succ`, `nat_le_refl`,
   `nat_div_zero_right`, `nat_div_less`, `nat_div_recursion`,
   `nat_add_def`, `nat_mul_def`, `nat_sub_def`, `int_induction`,
   `int_add_zero_right`, `int_add_succ_right`, `not_def`,
   `and_intro` — every one of these is derivable from
   `nat_induction` + the rule set + `define`. Until those
   derivations land downstream, postulated via `Thm::assume(body)`
   in `covalence-hol::nat_axioms` / `int_axioms` / `stdlib/*`.

5. **Connectives demoted to definitions**: `TermKind::HolOp` (the
   9-variant connective enum) was removed. Only `=` and `ε` survive as
   logical primitives — the new `TermKind::Eq(Type)` / `Select(Type)`
   leaves. The propositional connectives and quantifiers
   (`∧ ∨ ¬ ⟹ ⟺ ∀ ∃`) became ordinary let-style TermSpecs in
   `defs/logic.rs`, unfolded by `unfold_term_spec`. This dropped the
   bespoke `validate_hol_op_shape` check and its `HolOpShape` error
   (`Eq`/`Select` store α directly, so they're well-shaped by
   construction). The longer-term aim is to derive the connective
   intro/elim rules from these definitions in `covalence-hol`,
   shrinking the postulate set toward content-addressing only.

6. **Connective rules + induction-as-a-rule + ex falso**: the
   propositional connective intro/elim rules were first *derived* from
   the `defs/logic.rs` definitions (in `covalence-hol::proofs::bool`),
   then promoted to fast kernel constructors (`Thm::and_intro`,
   `or_elim`, `not_intro`, …) with `Soundness:` docstrings — the
   derivations remain as cross-checked soundness witnesses. The stored
   induction *axiom* `Thm::nat_induction()` became the induction *rule*
   `Thm::nat_induct(base, step)` (axiom recovered as a theorem), and ex
   falso became the primitive `Thm::false_elim`. With these,
   `covalence-hol::{proofs,init}::bool` are postulate-free; the
   `stdlib` module was renamed `init` (Lean-style).

Git history on `kernel-design` is the authoritative record;
`docs/design/proposals/stacked-pure-hol/` records the design
discussions that led here.
