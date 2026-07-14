# A structural (non-identity) `σ` for transport

*AI-authored design corpus. Status as of the `mm-metatheory` work: landed the
`Φ⟨bool⟩` slice; the `Φ=nat` MM-import slice remains open.*

## The blocker this addresses

`metalogic::relations::transport` proves, for the reified-propositional database
world (`Φ⟨bool⟩`):

```text
  ⊢ σ_hom σ ⟹ Interp DbA DbB σ ⟹ Derivable_DB DbA S ⟹ Derivable_DB DbB (σ S)
```

over a **free** translation `σ : Φ⟨bool⟩ → Φ⟨bool⟩`, carrying `σ_hom σ`
(`∀X Y. σ ⌜X ⟹ Y⌝ = ⌜σ X ⟹ σ Y⌝`) as an explicit hypothesis. The theorem is
fully general, but its *only* concrete discharge was the **identity** `σ := λx.x`
(where `σ_hom` holds by reflexivity through β). The metalogic `SKELETONS`
"Structural `σ` for transport" item asked for a genuinely structural, non-identity
`σ` — a constant/variable renaming that actually moves formulas — proved to satisfy
the same `σ_hom`, so transport is demonstrated at a non-trivial translation.

## Two carriers — do not conflate

There are two distinct "encoded-formula" carriers in `metalogic`:

1. **Reified-prop `Φ⟨bool⟩`** (`init::prop`): the Church/impredicative fold type
   `(nat→r)→(r→r)→(r→r→r)³→r` pinned at `r := bool`. This is the carrier
   `database.rs`'s `Derivable_DB` and `relations.rs`'s `transport`/`sigma_hom`
   actually range over. It is *not* a carved kernel inductive type (no kernel
   destructor / subtree recursor), but transport does **not** need a destructor —
   it needs only that `σ` commutes with the implication *constructor* `enc_imp`.

2. **MM-import `Φ = nat`** (`mm_database.rs`): `concat(a,b)` over `mm$c$<tok>` /
   `mm$v$<tok>` free-var leaves. This is a genuine recursor-free free algebra;
   what `replay_db`/`MmSession` produce. A structural `σ` here would descend
   `concat`-trees and needs the encoding reified as an inductive datatype first.

The landed slice targets carrier (1); carrier (2) stays open (below).

## What landed: `relations_sigma.rs`

A **variable-index renaming** on `Φ⟨bool⟩`. A formula is a Church fold
`λ var ¬ ∧ ∨ ⟹. body` consuming five handlers; the `var` handler `: nat → bool`
is applied to the propositional-variable index at every leaf. To rename every
index by `f : nat → nat`, re-plumb *only* the `var` handler (pre-compose with `f`)
and pass the other four handlers through untouched:

```text
  σ_f := λA:Φ⟨bool⟩. λ v ¬ ∧ ∨ ⟹.  A (λn. v (f n)) ¬ ∧ ∨ ⟹
```

`σ_f : Φ⟨bool⟩ → Φ⟨bool⟩` is exactly `relations::sigma_ty()`, so it plugs into
`transport()` with **no re-parameterisation**. Instantiated at `f := succ`
(`init::nat::nat_succ`, a genuine non-identity `nat → nat` term), `σ_succ` shifts
every variable index up by one.

### Why the homomorphism holds by pure β

`enc_imp X Y` folds by applying the `⟹` handler to the folds of `X` and `Y`, with
`X`, `Y` free `Φ⟨bool⟩` vars. `σ_f` only rewrites the `var` handler slot, so both

```text
  σ_f ⌜X ⟹ Y⌝   and   ⌜σ_f X ⟹ σ_f Y⌝
```

β-normalise to the **same** term. Hence the `σ_hom` proof is the *identical spine*
`relations::tests` used at `σ = id`, generalised off `id`: `beta_nf` both sides,
`trans`, two `all_intro`s. A `debug_assert_eq!` guards that the two normal forms
actually coincide (they do — verified in the debug test build).

### The three theorems proved (all hypothesis-free)

1. `sigma_hom_of_var_rename(succ)` : `⊢ ∀X Y. σ_succ ⌜X ⟹ Y⌝ = ⌜σ_succ X ⟹ σ_succ Y⌝`
   — the transport `σ_hom` premise, discharged at the structural `σ_succ`. Test
   asserts it equals `relations::sigma_hom(σ_succ)` verbatim.
2. `sigma_succ_moves_a_variable` (non-vacuity witness): `σ_succ ⌜var 0⌝`
   β-reduces to `⌜var (succ 0)⌝ ≠ ⌜var 0⌝`. So `σ_succ ≠ id` — not the identity in
   disguise.
3. `transport_at_var_rename` : `transport().inst("sigma", σ_succ).imp_elim(hom)`
   is a genuine hypothesis-free theorem
   `⊢ Interp DbA DbB σ_succ ⟹ Der_DbA S ⟹ Der_DbB (σ_succ S)` — the same
   `transport()` proof `relations::tests` fed only `σ = id`, now at its first
   non-identity structural translation. Test also asserts `σ_succ S ≠ S`.

### Bridge to transport

`transport()` is reused **unchanged**. The slice supplies `.inst("sigma", σ_succ)`
(discharges the free `σ`) and `.imp_elim(sigma_hom_of_var_rename(succ))` (discharges
the `σ_hom` premise transport is parameterised over). No new kernel rules, no
postulates, no TCB edit — every `Thm` comes from existing kernel/eval helpers
(`beta_nf`, `trans`, `sym`, `all_intro`, `inst`, `imp_elim`).

## Honest scope — what is *not* claimed

- This is **"transport demonstrated at a real structural σ"**, not "transport
  re-stated over an inductive encoding". `transport()` itself is unchanged; we
  feed it a genuine non-identity `σ_hom`.
- The renaming re-plumbs handler slots of the existing Church fold; it is not a
  catamorphism over a carved inductive `MmExpr`. That is fine for the `Φ⟨bool⟩`
  carrier (no destructor needed), but does not by itself reify the MM-import
  encoding.

## What remains (open)

- **MM-import `Φ = nat` structural `σ`.** Reify the `mm_database` encoding as an
  inductive `MmExpr := sym(code: nat) | app(MmExpr, MmExpr)` (structurally the
  current leaf/`concat` encoding) via the `church.rs` backend of
  `crates/lang/inductive`, define a catamorphic constant/var renaming through
  `rec_app`, and prove its concat-homomorphism from the `comp` laws + induction.
  This is the harder path the `SKELETONS` blocker also names.
- **Connective-mapping σ / per-rule simulations.** The same handler-passthrough β
  argument gives other structural translations for free — e.g. a connective-swap
  `σ` (swap the `∧`/`∨` handler slots, identity on `var`/`imp`) commutes with
  `enc_imp` identically. A fallback if variable-rename normalisation ever
  disagreed; also a template for genuine connective maps.
- **HOL→ZFC-scale transport** (`Derivable_HOL ⟹ Derivable_ZFC ∘ σ`) — the
  north-star instance; needs the MM-import structural `σ` plus concrete HOL/ZFC
  rule sets.
