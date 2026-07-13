# covalence-core: HOL kernel design

> Authority on the **HOL/core TCB** (`crates/kernel/hol/core`) as of 2026-06.
> The *base* below core is now the closed-world relation-calculus kernel — see
> [`closed-world-kernel.md`](./closed-world-kernel.md) and
> [`base-relcalc-holomega-design.md`](./base-relcalc-holomega-design.md). The
> `defs/` re-home from `Spec` leaves to `define`/`new_type_definition` is in
> flight — see [`defs-rehome-design.md`](./defs-rehome-design.md). Kernel audit:
> [`tcb/soundness-audit.md`](./tcb/soundness-audit.md).

## 1. What it is

`covalence-core` is an LCF-style HOL Light kernel in safe Rust (TCB ~3 KLoC).
Its public interface is a single opaque `Thm` with rule methods; the only paths
to a `Thm` are the inference rules below. Soundness reduces to those rules plus
the kernel's commitment to its primitive types' denotational semantics.

Shape: **pure HOL Light** with a few well-justified additions:

- HOL Light's 10 inference rules are primitives.
- Well-known HOL Light derived rules (SYM, DISCH, MP, GEN, SPEC, MK_COMB/ABS
  congruence, ETA_AX) plus the propositional connective rules (CONJ /
  CONJUNCT1,2 / DISJ1,2 / DISJ_CASES / ¬-intro / ¬-elim) are also primitives —
  ergonomics + performance, soundness justified by the standard HOL Light
  derivation in each docstring (and, for the connectives, an executable witness
  in `covalence-hol::proofs::bool`).
- Four non-computational primitive **rules**: **Peano induction on `nat`**
  (`Thm::nat_induct`, connective-free sequent form), **ex falso**
  (`Thm::false_elim`: `⊢ F` ⟹ `⊢ p`), the **`unit` singleton rule**
  (`Thm::unit_eq`, since `unit := { b : bool | b = T }`), and **excluded middle**
  (`Thm::lem`: `⊢ p ∨ ¬p`, exposed directly rather than derived from ε).
- Spec **abs/rep coercions** (`Term::spec_abs` / `spec_rep`) for derived
  `TypeSpec`s, plus their **witness-free subtype bijection laws**
  (`spec_abs_rep`, `spec_rep_abs_fwd`, `spec_rep_abs_back` — the back direction
  weakened because no non-emptiness witness is supplied). These are the
  `TypeSpec` analogue of `new_type_definition`'s bijection theorems.
- Accelerated reduction: `unfold_term_spec` (definitional unfolding) + per-family
  computation certificate rules (`NatArithCert`/`IntArithCert`/`BytesCert`/…,
  dispatch in `thm/certs.rs`, computed in `covalence-pure-eval`) emitting
  `⊢ t = canonical_form` for closed-literal computations — sound by the literal's
  denotation, not a postulate.
- Conservative-extension primitives (`define`, `new_type_definition`).
- **No observer system** (deleted, toHOL purge 2026-07). External facts now enter
  as admits-gated base-language rules; typedef freshness survives as the
  `FreshId` token (`TermKind::FreshConst` / `TypeKind::FreshTyCon`).

The propositional layer (`∧`/`∨`/`¬`, ex falso, quantifier intro/elim) is fully
derived (`covalence-hol::{proofs,init}::bool`). The arithmetic tier (`pred`,
`natRec`, addition, multiplication, division, integer induction) is derivable
from `nat_induct` + the rule set + `define`, but until those derivations land
(slated for the WASM-based proof rewrite) consumers postulate them via
`Thm::assume(body)` — each carrying its body as a self-hyp so the audit chain is
visible in any final theorem.

## 2. Files (TCB scope)

```
crates/kernel/hol/core/src/
├── term/{fresh,term,spec,set}.rs   — FreshId, Term/TermKind (Eq/Select), Def, TypeEnv; TermSpec; TermSet
├── ty/{ty,spec,list}.rs            — Type/TypeKind; TypeSpec; TypeList
├── ctx.rs                          — Ctx (structurally-shared hyp set)
├── subst.rs                        — close/open/shift/subst_free/subst_tfree/match_types
├── hol.rs                          — HOL-connective constructors
├── thm/{mod,typedef}.rs            — the LCF API + define/new_type_definition
├── error.rs
└── defs/                           — TypeSpec/TermSpec catalogue (semi-trusted; §6)
```

## 3. Types

```
TypeKind                      Constructor              Notes
TFree(SmolStr)                Type::tfree(name)        type variable
Nat                           Type::nat()              kernel-primitive
Bool                          Type::bool()             HOL formula type
Fun(Type, Type)              Type::fun(d, c)           function type
Tycon(SmolStr, Vec<Type>)    Type::tycon(name, args)   named structural tycon
FreshTyCon(FreshId, …)                                 fresh-identity tycon (typedef result)
Spec(TypeSpec, Vec<Type>)    Type::spec(spec, args)    derived TypeSpec application
```

`Type::int()` = `Type::spec(int_ty_spec(), [])` (`int := (nat × nat) / ~`,
Grothendieck). `Type::bytes()` = `bytes := list u8`. `Type::unit()` =
`unit := { b : bool | b = T }` (a derived TypeSpec, not a builtin `TypeKind`).

There is **no `TypeKind::Prop`** — no Pure meta-prop type; every formula is `bool`.

## 4. Terms

```
TermKind                     Constructor            Notes
Bound(u32)                   Term::bound(i)         de Bruijn index
Free(Var)                    Term::free(name, ty)   Var = (name, type)
Const(SmolStr, Type)         Term::const_(name, ty)
App(Term, Term)              Term::app(f, x)
Abs(Type, Term)              Term::abs(ty, body)
Nat/Int/Bool/Blob(...)       literals               arbitrary-precision / byte-string
Eq(Type)                     Term::eq_op(alpha)     `=` at element type α
Select(Type)                 Term::select_op(alpha) `ε` (choice) at element type α
Spec(TermSpec, Vec<Type>)    Term::term_spec(...)   derived TermSpec
FreshConst(FreshId, Type)                           fresh typedef constant (abs/rep)
Def(Def)                     Term::def(d)           defined constant
```

**Free variables carry their type in their identity** (`Var = (name, type)`), so
`Var("x", nat)` and `Var("x", bool)` are distinct and may coexist. Equality /
hashing / substitution match on both fields; there is no cross-term name/type
consistency check in `type_of` (a type-mismatched `inst` is a no-op). Name-only
`subst::close` is a construction convenience; rules taking arbitrary theorem
terms (`abs`, `all_intro`, `inst`, `nat_induct`) use the type-aware `close_var`.

**`=` and `ε` are the only logical primitives.** `Eq(α) : α → α → bool`,
`Select(α) : (α → bool) → α`; each is an ordinary applicable operator (`a = b` is
`App(App(Eq(α), a), b)`). No Pure meta-layer — no `Imp/All`, no `Trueprop`, no
`Prop`. The connectives/quantifiers `∧ ∨ ¬ ⟹ ⟺ ∀ ∃` are ordinary let-style
definitions in `defs/logic.rs` over `=`/`ε`/`T`/`F` (the HOL Light `bool.ml`
bootstrap). `unfold_term_spec(op)` hands back the defining equation
`⊢ op = <body>` — the hook `covalence-hol` uses to *derive* the connectives'
intro/elim rules. `imp_intro`/`imp_elim`/`all_intro`/`all_elim` remain
kernel-provided derived rules. Since `Eq`/`Select` store α directly they are
well-shaped by construction (no instance-type validation).

## 5. Inference rules (the `Thm` API)

### 5.1 The HOL Light primitive ten

`refl` · `trans` · `mk_comb` · `abs` · `beta_conv` · `assume` · `eq_mp` ·
`deduct_antisym` · `inst` (INST) · `inst_tfree` (INST_TYPE).

### 5.2 Derived HOL-Light rules (primitives by the "easily auditable" rule)

Each has a `Soundness:` docstring citing the standard HOL Light derivation:
`sym` (SYM), `cong_app`/`cong_abs` (aliases of mk_comb/abs), `imp_intro` (DISCH),
`imp_elim` (MP), `all_intro` (GEN), `all_elim` (SPEC), `eta_conv` (ETA_AX). The
propositional connective rules `and_intro` (CONJ), `and_elim_l/r` (CONJUNCT1/2),
`or_intro_l/r` (DISJ1/2), `or_elim` (DISJ_CASES), `not_intro`, `not_elim` are
fast constructors; the *executable* derivation (soundness witness, and the basis
for a future "paranoid mode") lives in `covalence-hol::proofs::bool`.

### 5.3 Structural

`weaken(self, target)` — `Δ ⊢ φ` from `Γ ⊢ φ`, `Γ ⊆ Δ`.

### 5.4 Conservative-extension primitives

- `Thm::define(name, body)` — allocates a fresh `Def` (unique Arc identity),
  returns `⊢ Def(name, body) = body`. Phantom-tfree check: every tvar in body
  must reach `body_type`.
- `Thm::new_type_definition(hint, abs_hint, rep_hint, witness)` — witness
  `Γ ⊢ P x` (`x : α`, `P : α → bool`); returns a `TypeDef` bundle: fresh `tau`,
  `abs : α → τ`, `rep : τ → α`, and the three bijection theorems `abs_rep`,
  `rep_abs_fwd`, `rep_abs_back`. Standard HOL Light typedef; sound under
  conservative extension.

### 5.5 Accelerated reduction rules (sound one-shot computation, not axioms)

- Per-family certificate rules (applied via `covalence_pure::apply`, driven by
  untrusted `covalence-hol-eval::reduce`), each returning `⊢ t = canonical`:
  `LitEqCert`, `SuccCert`, `NatArithCert`, `IntArithCert`, `BytesCert`,
  `CoercionCert`, `FixedWidthCert`. Dispatch by `TermSpec` ptr_eq against
  catalogue handles; compute via the enumerable `covalence-pure-eval` CanonRules.
  `Err(NotReducible)` for shapes not in the table.
- `Thm::unfold_term_spec(t)` — for a let-style TermSpec, returns
  `⊢ Spec(spec, args) = subst_tfree(spec.tm, tvars, args)`. Each TermSpec is its
  own opaque atom; the unfolding equation is a let-binding for it, sound
  regardless of user content.

### 5.6 The non-computational primitive rules

- `nat_induct(base, step, p, x)` — sequent form: `base : Γ_b ⊢ p[0/x]`,
  `step : Γ_s ⊢ p[succ x/x]` with `p ∈ Γ_s` ⟹ `Γ_b ∪ (Γ_s \ {p}) ⊢ p`
  (`x : nat` free). Kernel computes `p[0/x]`/`p[succ x/x]` and matches
  syntactically. Side condition: `x` not free in `Γ_s \ {p}`. Sound because
  `Type::nat()` denotes the standard naturals. The formula form is a derivation
  over this rule (`covalence-init::init::ext::nat_induct`).
- `false_elim(self, p)` — `Γ ⊢ F` ⟹ `Γ ⊢ p`.
- `unit_eq(a, b)` — `a, b : unit` ⟹ `⊢ a = b`.
- `lem(p)` — `⊢ p ∨ ¬p` (classicality; a standing derivation target from ε).
- `succ_inj(m, n)` / `zero_ne_succ(n)` — Peano freeness (`0`/`succ` distinct,
  injective constructors of the freely-generated nat).
- `select_ax(p, x)` — `⊢ (p x) ⟹ p (ε p)` (Hilbert choice for `ε`).
- `spec_ax(t, w)` — per-def-spec choice: `⊢ (p w) ⟹ p(t)` where `t` is a
  def-style spec with predicate `p`. Sound unconditionally; does NOT equate `t`
  with `ε p`. See §9 for its coupling with certificate reduction on `nat.le`/`nat.lt`.

**That is the entire non-computational axiom surface.** The classic induction
*axiom* is a trivial theorem over `nat_induct`; every other arithmetic/logic fact
is derivable from these rules + the rule set + `define`.

## 6. `defs/` — the spec catalogue (semi-trusted)

`defs/` is the kernel's out-of-box TypeSpec/TermSpec catalogue. Users CAN
construct their own `TypeSpec::new` / `TermSpec::new`, which go through the same
kernel rules (`unfold_term_spec`, `Type::spec`) — no special trust needed.

| Module | Provides |
|--------|----------|
| `canonical.rs` | `Canonical` symbol enum (kernel-shipped names) |
| `spec.rs` / `symbol.rs` | handle types; `Symbol` trait + Opaque/Transparent opacity |
| `nat.rs` / `int.rs` / `blob.rs` | arithmetic + byte constants (`nat_add`, `int_add`, `bytes_cat`, …) |
| `set.rs` / `rel.rs` | `set 'a := 'a → bool`; `rel`, `preord`, `pord`, `per`, `part` |
| `coprod.rs` / `prod.rs` | `bit`…`u512`, `coprod`; `prod`, `signed1`, `signed2` |
| `list.rs` / `option.rs` / `result.rs` / `stream.rs` | container theories |
| `rat.rs` / `floats.rs` | `rat := fieldOfFractions int`; `f32`, `f64` |

(The reals — `real := { rat } close ratLe` — are a derived `close`-subtype in
`covalence-hol::init::real`, not the kernel catalogue.) Every TypeSpec resolves
into a content-addressable shape; every TermSpec has either a body (let-style) or
a selector predicate (def-style via Hilbert ε).

## 7. The hypothesis context (`Ctx`)

`Ctx` is an `Option<Arc<BTreeSet<Term>>>` carrying a `Thm`'s hypotheses. Empty
contexts don't allocate; non-empty contexts share `Arc`. Ops: `new`, `singleton`,
`union` (O(1) when either side empty / `Arc::ptr_eq`), `is_subset`, `remove`,
`insert`.

## 8. The trust boundary

- **INSIDE the TCB** (bugs = false theorems): `term/`, `ctx.rs`, `subst.rs`,
  `thm/certs.rs` (+ `covalence-pure-eval`'s enumerable `Builtins` CanonRules),
  `hol.rs`, `thm.rs`, `error.rs`.
- **SEMI-TRUSTED** (audit at user-call time): `defs/` — user-constructed specs go
  through the same rules; the catalogue is just the shipped starting set.
- **OUTSIDE the TCB**: `covalence-hol` (builder API, postulated downstream axioms,
  serialization), and every higher-level crate. A bug here cannot produce a false
  `Thm`.

## 9. Soundness notes

**Model commitments** (what makes the non-computational rules sound):
`Type::nat()` denotes the standard naturals; `Type::bool()` has exactly `T`/`F`;
`Type::unit()` has one inhabitant; distinct kernel literals at the same kind
denote distinct values; HOL `=` is model equality.

**Things the kernel does NOT do:** validate `TermSpec::new` bodies against any
canonical computation (two distinct TermSpecs may share a `Canonical` label — no
contradiction); enforce uniqueness of `define` names (two `Def` atoms, both
`= body` — no contradiction); provide rewriting/tactics/automation (downstream).

**Coupling the catalogue must respect.** When a spec is reachable by *both* the
cert rules and `unfold_term_spec` (let-style body *and* in a cert table, e.g.
`nat.add`, `nat.mod`, `bytes.cat`), the kernel commits to `spec lit… =
reduce(spec lit…)` **and** `spec = body`. Consistent only if the body denotes the
same function the certificate computes, on every input — a divergence makes the
theory inconsistent. Guarded by `covalence-hol-eval`'s
`tests/audit_reduce.rs::audit_reduce_matches_body`, which bites exactly when the
body reduces to a literal (`nat.mod`, `int.div`/`int.mod` — forcing the Euclidean
conventions `x/0=0`, `x mod 0 = x`). Grothendieck/`iter` ops bottom out at ε and
are stuck (sound by the model alone).

**Second coupling — `spec_ax` vs certificate reduction.** For a def-style spec
that is *also* cert-reducible (currently `nat.le`/`nat.lt`), the kernel commits to
both `(p w) ⟹ p(t)` and the certificate values — so every function satisfying `p`
must agree with the certificate on reducible inputs. `nat.le`/`nat.lt`'s
predicates are their defining recursion equations (unique solution = the real
`≤`/`<`), so they are safe. Guarded by
`audit_reduced_def_specs_satisfy_their_predicate`. **Any future def-style spec
added to a cert table must satisfy this.**

**Audit confidence.** Third pass (2026-06-14) found and fixed one real hole
(`nat.mod n 0` reduced to `0` while its body evaluates to `n` — derived `⊢ 0 = 5`;
now returns `n`) and added the reduce/`unfold` consistency guards. Fourth pass
audited `succ`-as-`TermKind::Succ` + `succ_inj`/`zero_ne_succ`, `select_ax`,
`spec_ax` — all standard, sound under the model commitments; surfaced the second
coupling and added its guard. No known soundness holes.

Remaining hardening (not gaps): property tests for substitution commutativity;
cross-validation against HOL Light proper; a formal Lean/Coq model of the rule
set; a doc-comment audit for stale Pure-meta references.

## Typedness caching — representation options (design note)

To avoid re-deriving a term's type on every kernel step (the `type_of` re-walk),
three representations were weighed. The enabling fact: **typing is context-free**
(free variables carry their type), so `term : ty` holds in any context.

1. **`Typed(term, ty)` — a context-free typing witness. [chosen]** Constructible
   only via LCF-style checked constructors (each O(1) by combining children's
   cached types) or `Typed::infer` (runs `type_of`). Small TCB cost; `Term`/`Thm`
   representation unchanged. `Thm::from_typed` skips the re-walk; legacy
   `build(.., concl)` delegates via `Typed::infer`.
2. **`Eq(Ctx, Lhs, Rhs, Ty)` — equality as a structured judgement. [rejected]**
   Would make refl/trans/cong O(1) but bifurcates `Thm`, re-privileges `=`
   (against the `=`/`ε`-only invariant), and its `Ctx` merely duplicates
   `Thm.hyps`. The context-free part is better captured by `Typed`; reading α off
   the `Eq(α)` node already grabs most of the equational win.
3. **Type cached on the term node (intrinsic). [end-state]** All `type_of`
   becomes O(1) transparently, but the node grows and construction must maintain
   and *trust* the cache. Sound only when gated to **closed** subterms (a
   free-variable counter / closed bit provides this cheaply, and also accelerates
   `subst`/occurs checks). Best done *after* hash-consing is threaded; can reuse
   `Typed`'s constructors. (A Bloom filter over free variables is a separate,
   optional occurs-check pre-filter — not the type-cache enabler.)

Direction: ship `Typed` (1) now; evolve toward per-node caching (3) once
hash-consing + a closed-bit exist. (2) is recorded but not pursued.
