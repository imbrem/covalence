# covalence-core: kernel design

> **Canonical reference for the current state of the kernel** as of
> 2026-06-13 (branch `kernel-design`). Supersedes
> [`docs/design/proposals/stacked-pure-hol/`](./design/proposals/stacked-pure-hol/),
> which records the historical Pure→HOL evolution.
>
> The (not-yet-built) authoring layer *above* this kernel — surface
> syntax, untrusted observers, and theories/derivations as first-class
> objects — is described in [`surface-syntax.md`](./surface-syntax.md),
> [`observers.md`](./observers.md), and [`metatheory.md`](./metatheory.md).
> Those are design sketches; this doc is the authority on the kernel TCB
> they elaborate down to.

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
- Four non-computational primitive **rules**: **Peano induction on
  `nat`** (`Thm::nat_induct`: base + step ⟹ `∀n. P n`), **ex falso**
  (`Thm::false_elim`: `⊢ F` ⟹ `⊢ p`), the **`unit` singleton rule**
  (`Thm::unit_eq`: `⊢ a = b` for any `a, b : unit`, since
  `unit := { b : bool | b = T }` is a one-element type), and **excluded
  middle** (`Thm::lem`: `⊢ p ∨ ¬p` — the classicality axiom, derivable
  from ε the usual HOL way, exposed directly for now). The classic
  induction *axiom* `⊢ ∀P. (P 0 ∧ …) ⟹ ∀n. P n` is a trivial theorem on
  top of the induction rule.
- Spec **abs/rep coercions** (`Term::spec_abs` / `Term::spec_rep`):
  for any derived `TypeSpec`, the typed leaves `abs : carrier → (spec
  args)` and `rep : (spec args) → carrier`. The bare leaves carry no
  theorems, so adding them is sound; they let the `defs/` catalogue
  *define* constructors like `option.some := λa. abs (coprod.inl a)`.
  Their **witness-free subtype bijection laws** are three rules —
  `Thm::spec_abs_rep` (`⊢ abs (rep a) = a`, unconditional),
  `Thm::spec_rep_abs_fwd` (`⊢ P a ⟹ rep (abs a) = a`), and
  `Thm::spec_rep_abs_back` (`⊢ rep (abs a) = a ⟹ (P a ∨ ¬∃x. P x)`,
  the converse weakened because no non-emptiness witness is supplied).
  `P = spec.tm()` is the carving predicate (`λ_. T` for a `newtype`, so
  the `_fwd` premise discharges to give the unconditional round-trip);
  quotient specs, whose `tm` is a relation, are rejected. These are the
  `TypeSpec` analogue of the `new_type_definition` bijection theorems
  and are what `covalence-hol::init::set` builds its membership /
  extensionality API on.
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

Thm::lem(p) -> Result<Thm>
    // p : bool  ⟹  ⊢ p ∨ ¬p   (excluded middle; the classicality axiom)
    // Sound in the standard two-valued model. HOL Light *derives* this
    // from ε (Select) + extensionality + deduct_antisym; exposed here as
    // a direct constructor for now, a standing derivation target.

Thm::succ_inj(m, n) -> Result<Thm>
    // m, n : nat  ⟹  ⊢ (succ m = succ n) ⟹ (m = n)
Thm::zero_ne_succ(n) -> Result<Thm>
    // n : nat  ⟹  ⊢ ¬(0 = succ n)
    // nat freeness: `0` / `succ` (TermKind::Succ) are distinct, injective
    // constructors of the freely-generated nat — the other half of the
    // commitment nat_induct rests on.

Thm::select_ax(p, x) -> Result<Thm>
    // p : α → bool, x : α  ⟹  ⊢ (p x) ⟹ p (ε p)   (Hilbert choice; the
    // characterising axiom of the ε / Select primitive).
Thm::spec_ax(t, w) -> Result<Thm>
    // t = Spec(spec, args) def-style with predicate p, w : carrier
    //   ⟹  ⊢ (p w) ⟹ p(t)   (each named def-spec is its own choice; the
    // def-style analogue of select_ax). Sound unconditionally; does NOT
    // equate t with ε p or any other spec sharing p. See §9 for its
    // coupling with reduce_prim on the reduced def-specs nat.le / nat.lt.
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
| `floats.rs`     | `f32`, `f64`                                              |

(The reals — `real := { rat } close ratLe` — are **not** in the kernel
catalogue: they are a derived `close`-subtype defined in the shell
[`covalence-hol::init::real`], since the float substrate needs only the
rationals.)

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

## 11. Direction: the Pure base logic and the narrow waist

> **DIRECTION — not yet built; partially *reverses* §10.1.** §10.1 folded
> the old `covalence-pure` crate away. This re-introduces a `covalence-pure`,
> but in a **different shape** — not an Isabelle/Pure LF, a *first-order
> base logic with observation and computation as primitives*. Coupled with
> the trusted-observer direction in [`observers.md`](./observers.md) §7.

The target is three rungs, with HOL as a **narrow waist**:

```
   …diverse logics on top  (FOL, PA, ZFC, MLTT, …)   ← built inside HOL
   ─────────────────────────────────────────────────
   HOL   (covalence-core)                            ← THE NARROW WAIST
   ─────────────────────────────────────────────────
   covalence-pure: first-order base logic            ← positive, concrete,
     with observation + computation as primitives       efficient
```

### 11.1 `covalence-pure` — the base logic (opaque, computational)

A **first-order** logic kept *as weak as possible on purpose*. It reasons
only about **opaque predicates** and the simple first-order **implications**
between them — e.g. `WASM_holds ⟹ HOL_holds` — and it **cannot express** what
those predicates *mean*: not WASM's reduction relation, not HOL theoremhood,
nothing about their internal structure. A predicate is an uninterpreted
symbol; the logic commits to nothing about it. Committing to almost nothing
is exactly what makes Pure *trivially correct* — there is barely anything for
it to be wrong about — and *trivially re-hostable* (§11.5).

It is **computational in character**: in practice a *template metaprogram
over a handful of Rust traits*. A Pure fact is a Rust value built only
through those trait rules (LCF discipline), and Rust's type system tracks
which opaque predicates a fact depends on. The **observation substrate moves
here**: the `Obs` leaf and the `ObsEq` / `ObsTrue` / `ObsImp` policy traits
(today in `covalence-core/src/term/observer.rs`,
[`observers.md`](./observers.md) §2) become *the* primitive of the base
logic — an observer attests an opaque atomic predicate, and a first-order
rule chains it into an implication. The trusted-observer story of
[`observers.md`](./observers.md) §7 is precisely this: a trusted observer is
a Rust trait impl that mints an opaque fact by running code (bignum add, a
store fetch, a WASM component), and the §11.4 "zoo" is the catalogue of those
impls.

Pure does **not** reason *about* the WASM engine or the store; it only
*records* (opaquely) that an observation was made, and proves first-order
implications over such records. All meaning lives one rung up.

### 11.2 Lifting into HOL: meaning by assumption

HOL is where the opaque predicates *acquire meaning*. A Pure fact over opaque
predicates **lifts into HOL under assumptions about what those predicates
mean** — and those assumptions enter as ordinary **scoped hypotheses** (the
"scoped truths, no global lies" discipline). Concretely: a Pure theorem
`WASM_holds ⟹ HOL_holds` lifts to a HOL theorem of the same shape once you
assume `WASM_holds ⟺ ⟦the real WASM fact⟧` and `HOL_holds ⟺ ⟦the real HOL
proposition⟧`; the two correspondences ride along as hypotheses until
discharged — e.g. against the SpecTec-lowered `T_wasm` (§11.5,
[`observers.md`](./observers.md) §4). This is the kernel's `obs_imp` rule
generalized and relocated: **Pure proves the *structure* of the implication,
computationally and opaquely; HOL supplies the *meaning*.**

So `covalence-core` stays *mostly unchanged* — morally "`Thm` implements a
trait": a `Thm` is one lifted observer (the HOL observer) among peers (the
WASM observer, the bytes observer), and the existing HOL kernel API keeps
working while becoming one logic *expressed over* Pure rather than the
absolute bottom. It is the same reflective move as the metatheory program
([`metatheory.md`](./metatheory.md) §1) applied *downward*; and the judgement
`WASM(P,D,A) ⟹ ∃D'. ZFC(D',A)` ([`metatheory.md`](./metatheory.md) §6) is
literally a Pure opaque-predicate implication lifted into the metatheory.

### 11.3 Why it is a *narrow waist*

HOL is the waist because **different implementations may have a different
`covalence-pure`** underneath. The base logic is abstracted away by the
*untrusted* `covalence-hol` API, which is what **most consumers should
use**; lower-level consumers drop to the `covalence-core` (HOL kernel) API;
the raw `covalence-pure` API is **mostly an implementation detail** — a
substrate the waist hides. So:

- **above the waist** — a diversity of related logics, all riding the HOL
  API ([`frontend.md`](./frontend.md), [`metatheory.md`](./metatheory.md));
- **at the waist** — the stable HOL surface every consumer targets;
- **below the waist** — a swappable, trivially-correct first-order substrate
  doing the efficient / low-level work.

The *waist logic itself* is also a choice, not a fixity: HOL Light today, but
**HOL-ω** (higher-kinded — first-class monads / transformers / profunctors) is
a live candidate for the waist, exactly because the waist is an API that
different implementations can meet differently
([`metatheory.md`](./metatheory.md) §5.2).

The flat-TCB and "scoped truths" disciplines are unchanged — the base logic
is *smaller and more concrete*, so if anything the audit story improves.

### 11.4 Pure as a metaprogramming layer; the `covalence-hol` zoo

`covalence-pure` is not only a logic you *write proofs in* — it is a layer
where **Rust itself is the metalanguage**, used to *construct* logical
objects (terms, observers, and the "trusted" assumptions of
[`observers.md`](./observers.md) §7) **freely**. Think **template
metaprogramming**: the host language computes and builds the object-language
artifacts. It is "computation and observation as primitives" (§11.1) taken to
its conclusion — a trusted assumption is just a Rust value you constructed,
and the freedom to construct it in ordinary Rust *is* the metaprogramming
facility.

The payoff is a precise, small trust story: because an efficient construction
is Rust code, **its soundness reduces to the soundness of the Rust compiler**
(plus the audit of that one small, concrete construction). No new *logical*
axiom is granted — the assumption's content is fixed and auditable (§11.1,
[`observers.md`](./observers.md) §7); Rust only supplies an efficient way to
*mint instances* of it. "Trusted" keeps its §7 meaning — a sound assumption
with a compiled-in representation — and the compiler is the thing doing the
compiling.

On top of this, `covalence-hol` can hold a **zoo of efficient
implementations**: many Rust realizations of the same logical content — an
efficient `nat`, an efficient `bytes`, a WASM-spec observer, a store-backed
observer, several coexisting — each an independent, separately-auditable Rust
construction, each **trusted only insofar as Rust is sound and that impl is
correct**. This is the flat-TCB property again
([`observers.md`](./observers.md) §5): adding the 20th efficient impl does
not enlarge the trust surface of the first 19. And it is *why* the narrow
waist holds — the zoo's diverse, swappable implementations all present the
**same HOL waist API** while differing underneath, including over different
`covalence-pure` substrates.

### 11.5 Portability constraint: paranoid mode and re-hosting

A hard requirement on the "different `covalence-pure`" freedom (§11.3): the
design must keep two things *easy*.

**Paranoid mode.** The efficient, compiled constructions of §11.4 — the zoo,
the trusted observers of [`observers.md`](./observers.md) §7 — must be
**demotable to untrusted wrappers around a simple dynamic core**. The *simple
dynamic core* is a minimal, obviously-correct interpreter of `covalence-pure`:
no compiled fast paths, every assumption and computation represented
explicitly and checked at runtime. In paranoid mode the efficient impls only
*propose* results; the simple core *re-checks* them — so the TCB shrinks from
"the Rust compiler + every efficient construction" (§11.4) down to just the
simple core. This is the LCF / mirror discipline ([`VISION.md`](./VISION.md))
turned on the kernel's *own* representations: the fast path is untrusted, the
slow obvious path is the checker. It is possible *only because* §7 / §11.1
keep an assumption's **content** (what the simple core implements) separable
from its **efficient representation** (what the zoo compiles) — paranoid mode
just makes the content authoritative.

**Re-hosting.** `covalence-pure` + `covalence-core` must be **re-implementable
in another language** — OCaml, Haskell, JS, whatever. So the logical design is
specified by the **narrow-waist HOL API and the simple core's semantics**, not
by Rust internals: Rust-specific tricks live only in the *efficient
representations*, never in the *content*. A re-host implements the small
simple core (and gets the same logical content for free); it may then grow its
*own* efficient zoo, or just run pure paranoid mode. A re-implementation in
another language is, in effect, "paranoid mode in that language" plus whatever
fast paths that host chooses to add.

The two requirements reinforce each other: the **simple dynamic core is the
portable spec**, and everything efficient — in any language — is an optional,
untrusted-checkable optimization layered over it. That is what keeps "a
different `covalence-pure` per implementation" a *cheap, safe* move rather
than a fork of the trust story.
