# covalence-core: kernel design

> **Canonical reference for the current state of the kernel** as of
> 2026-06-13 (branch `kernel-design`). Supersedes the historical Pure→HOL
> evolution notes (`notes/vibes/design/proposals/stacked-pure-hol/`, retired to the
> `backup/pre-hol-cleanup` branch).
>
> The (not-yet-built) authoring layer *above* this kernel is described in
> the design sketches ([`surface-compiler.md`](./surface-compiler.md),
> [`observers.md`](./observers.md), [`metatheory.md`](./metatheory.md)); the
> kernel's own audit is [`soundness-audit.md`](./soundness-audit.md). See
> [`notes/vibes/README.md`](./README.md) for the full index. This doc is the authority
> on the kernel TCB.

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
- ~~An observer system~~ **DELETED (toHOL purge, 2026-07)**: the observer
  rules and leaves are gone; external facts now enter as admits-gated
  base-language rules (`toHOL` denotations + `IsThm` certificates — see
  [`pure-hol-and-build-plan.md`](./pure-hol-and-build-plan.md)). Typedef
  freshness survives as the dedicated `FreshId` token
  (`TermKind::FreshConst` / `TypeKind::FreshTyCon`).

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
│   ├── fresh.rs       — FreshId (Arc-identity typedef-freshness token)
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
FreshTyCon(FreshId, Vec<Type>)                     fresh-identity tycon (typedef result)
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
Free(Var)                      Term::free(name, ty)     Var = (name, type)
Const(SmolStr, Type)           Term::const_(name, ty)
App(Term, Term)                Term::app(f, x)
Abs(Type, Term)                Term::abs(ty, body)      anonymous binder (de Bruijn)
Nat(Nat)                       Term::nat_lit(n)         arbitrary-precision literal
Int(Int)                       Term::int_lit(n)
Bool(bool)                     Term::bool_lit(b)        T or F
Blob(Bytes)                    Term::blob(bs)           byte-string literal
Eq(Type)                       Term::eq_op(alpha)       `=` at element type α
Select(Type)                   Term::select_op(alpha)   `ε` (choice) at element type α
Spec(TermSpec, Vec<Type>)      Term::term_spec(spec, ty_args)   derived TermSpec
FreshConst(FreshId, Type)     (pub(crate))             fresh typedef constant (abs/rep)
Def(Def)                       Term::def(d)             defined constant
```

**Free variables carry their type in their identity.** `Free(Var)` where
`Var = (name, type)`, so `Var("x", nat)` and `Var("x", bool)` are
**distinct** variables that may coexist in one theorem (HOL Light's
`Var(name, ty)` model). Equality / hashing / ordering consider both
fields, and `subst_free`/`close_var` match a variable by name **and**
type. Consequently there is **no** cross-term name/type consistency check
in `type_of`/`Thm::build` (an earlier design enforced one); a
type-mismatched `inst` is simply a no-op. The name-only `subst::close` is
a construction convenience (the name has a single known type at the binder
site); the kernel rules that take arbitrary theorem terms (`abs`,
`all_intro`, `inst`, `nat_induct`) use the type-aware `close_var` /
`has_free_var_typed` / `subst_free`.

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

### 5.6 Observer rules — DELETED (toHOL purge S1/S2, 2026-07)

The three observer rules (`obs_eq`/`obs_true`/`obs_imp`), the
`Observer`/`Object` machinery, the `Obs`/`TyConObs` leaves, and
`has_no_obs` no longer exist. Their replacement is the base layer:
uninterpreted `toHOL` ops + admits-gated unfolding/certificate rules
(enumerated in `docs/deps/core-manifest.txt` + the Builtins manifest),
per [`pure-hol-and-build-plan.md`](./pure-hol-and-build-plan.md). The
parametric-ε-model soundness story lives on only in the history
(`git log covalence-core -- '**/observer.rs'`).

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

Git history on `kernel-design` is the authoritative record; the design
discussions that led here (`notes/vibes/design/proposals/stacked-pure-hol/`) are
retired to the `backup/pre-hol-cleanup` branch.

## 11. Direction: the Pure base logic and the narrow waist

> **DIRECTION — not yet built; partially *reverses* §10.1.** §10.1 folded
> the old `covalence-pure` crate away. This re-introduces a `covalence-pure`,
> but in a **different shape** — not an Isabelle/Pure LF, a *first-order
> base logic with observation and computation as primitives*. Coupled with
> the trusted-observer direction in [`observers.md`](./observers.md) §7.
> **The concrete starting blueprint — the meta-sorts, the two assumption sets,
> the observer port plan — is [`covalence-pure.md`](./covalence-pure.md).**

The target is three rungs, with HOL as a **narrow waist**:

```
   …diverse logics on top  (FOL, PA, ZFC, MLTT, …)   ← built inside HOL
   ─────────────────────────────────────────────────
   HOL   (covalence-core)                            ← THE NARROW WAIST
   ─────────────────────────────────────────────────
   covalence-pure: first-order base logic            ← positive, concrete,
     with observation + computation as primitives       efficient
```

This section is a brief; the **full treatment is
[`covalence-pure.md`](./covalence-pure.md)** (crate reorg in
[`refactor-plan.md`](./refactor-plan.md)).

### 11.1 `covalence-pure` — the base logic (opaque, computational)

A first-order logic kept *as weak as possible on purpose*: opaque predicates +
first-order implications, with no way to express what the predicates *mean*.
Committing to almost nothing makes it trivially correct and trivially
re-hostable. The observation substrate (`Obs` + `ObsEq`/`ObsTrue`/`ObsImp`,
today in `covalence-core/src/term/observer.rs`) moves here as the base
primitive; a trusted observer ([`observers.md`](./observers.md) §7) is a Rust
trait impl that mints an opaque fact by running code.

### 11.2 Lifting into HOL: meaning by assumption

A Pure implication `WASM_holds ⟹ HOL_holds` lifts into HOL once you assume each
opaque predicate ⟺ its real meaning; those correspondences ride as scoped
hypotheses until discharged. This is `obs_imp` generalized: **Pure proves the
*structure*; HOL supplies the *meaning*.** `covalence-core` stays mostly
unchanged — a `Thm` becomes one lifted observer among peers.

### 11.3 Why it is a *narrow waist*

HOL is the *shared* semantic surface; what diverges is the two ends — below,
`covalence-pure` + efficient representations (a Rust observer "zoo", a paranoid
simple core, an OCaml/JS re-host); above, a diversity of object logics. A
`covalence-hol` zoo holds many Rust realizations of the same logical content,
each separately auditable, none enlarging the others' trust surface (flat TCB).

### 11.4 Metaprogramming layer; 11.5 paranoid mode + re-hosting

`covalence-pure` is also a layer where **Rust is the metalanguage** for
constructing logical objects freely, so an efficient construction's soundness
reduces to the Rust compiler's plus the audit of that one small construction.
Those efficient constructions must be **demotable to untrusted wrappers around a
*simple dynamic core*** (an obvious Pure interpreter that re-checks proposed
results — shrinking the TCB to just that core), and `covalence-pure` +
`covalence-core` must be **re-implementable in another language**. The simple
core is the portable spec; everything efficient is an optional,
untrusted-checkable optimization over it.

### 11.6 Roadmap: HOL Light → HOL Light over Pure → HOL-ω over Pure

The final shared waist is **HOL-ω** (higher-kinded — first-class
monads/transformers/profunctors), reached additively (HOL-ω's API is a superset
of HOL Light's). Building over Pure first makes substitution/typing auditable;
the endgame closes the computational-metatheory loop — an HOL-ω compiler/runtime
that bootstraps to WASM and proves each compilation sound by *translation
validation*.

> **Two "waist" usages, reconciled.** This §11 calls HOL the *narrow waist*
> (the shared semantic surface between `covalence-pure`-below and
> object-logics-above). The canonical [`VISION.md`](./VISION.md) §1 three-layer
> stack uses *thin waist* for a **different** object — **internal Metamath**,
> reified inside HOL on *top*. No conflict: HOL is the **middle** metalogic,
> `covalence-pure` + executors + content addressing are the **bottom** (Phase E),
> and internal Metamath is the **top** thin waist
> ([`theories-models-and-logics.md`](./theories-models-and-logics.md) §5.6/§5.7).
> This §11 is the *bottom*-rung direction.

## Typedness caching — representation options (design note)

To avoid re-deriving a term's type on every kernel step (the `type_of`
O(N) re-walk in `Thm::build` / `hol::hol_eq`), three representations were
weighed. The enabling fact is that **typing is context-free**: free
variables carry their type (`Var(name, ty)`), so `term : ty` holds in any
context — there is no typing Γ to thread.

1. **`Typed(term, ty)` — a context-free typing witness. [chosen]** A value
   pairing a term with its type; constructible only via LCF-style checked
   constructors (`app`/`abs`/`eq`/…, each O(1) by combining children's
   cached types) or `Typed::infer` (which runs the existing `type_of`).
   It captures *exactly* the context-free fact. TCB cost is small: a value
   type plus constructors that mirror the existing typing rules — no new
   logical commitments, `Term`/`Thm` representation unchanged. `Thm`
   accepts a `Typed` conclusion (`from_typed`) and skips re-walking it;
   the legacy `build(.., concl: Term)` delegates via `Typed::infer`.

2. **`Eq(Ctx, Lhs, Rhs, Ty)` — equality as a structured kernel judgement.
   [rejected]** Would cache the element type and sides for the equational
   fragment (the bootstrap's hot path), making refl/trans/cong O(1). But
   it bifurcates `Thm` into two judgement forms and re-privileges `=`
   (against the design invariant that `=`/`ε` are the only primitives and
   every formula is App-shaped), and its `Ctx` merely duplicates
   `Thm.hyps` — equality is context-*dependent* (it holds under
   hypotheses), which is already `Thm`'s job. The context-free part
   (typing) is better captured by `Typed`, and α-reuse (reading α off the
   `Eq(α)` node) already grabs most of the equational win without new TCB.

3. **Type cached on the term node (intrinsic). [end-state]** Every
   (interned) node caches its own type, so all `type_of` becomes O(1)
   transparently — this is `Typed` "inlined into the node". Strongest, but
   most invasive: the node representation grows and construction (or a lazy
   `OnceCell`) must maintain and *trust* the cache. Sound only when gated
   to **closed** subterms (a node's type is context-free only when no
   `Bound` escapes), which a bottom-up **free-variable counter / closed
   bit** provides cheaply (and which also accelerates `subst`/occurs
   checks). "Typecheck the moment a term is closed" = populate the cache
   when that bit flips true. Best done *after* hash-consing is threaded
   (interned nodes amortize the cache) and can reuse `Typed`'s checked
   constructors. A Bloom filter over free variables is a *separate,
   optional* occurs-check accelerator (approximate → a pre-filter only),
   not the type-cache enabler.

Direction: ship `Typed` (1) now; evolve toward per-node caching (3) once
hash-consing is threaded through the rules and a closed-bit/free-var
counter exists. (2) is recorded but not pursued.
