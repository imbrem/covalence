+++
id = "N002L"
status = "draft"
review = "unreviewed"

[[contributions]]
role = "author"
actor = "agent:claude"
at = "2026-07-14T20:52:29+01:00"
source = "legacy"
agent = "claude"
harness = "claude"
+++

# A structural (non-identity) `σ` for transport — and induction-on-derivations to foreign systems

*AI-authored design corpus. Status as of the `mm-metatheory` work: landed the
`Φ⟨bool⟩` renaming slice (TIER 0) **and** the `Φ⟨bool⟩` propositional-SUBSTITUTION
slice (TIER 1); the `Φ=nat` MM-import cross-rule-set slice (TIER 2) and genuine
cross-system transport (TIER 3) remain open.*

## The larger program: induction-on-derivations, including to foreign systems

This note is one rung of a ladder whose long-run target is
**induction-on-derivations transporting to *unrelated, non-Metamath* systems**.
The shared substrate is already there: multiple foreign systems are reified as
derivability relations over ONE impredicative rule-induction engine
(`metalogic::RuleSet` + `derivable()` + `rule_induction`), including **K**
(`k/reduce.rs`: `Derivable_KStep` over KORE rewrite rules — a genuinely
non-Metamath rewrite system), **SpecTec/WASM** (`wasm/`), and CFG grammars
(`grammar/cfg`), all sharing the `Φ=nat` free-term-algebra encoding with Metamath
import.

A **cross-system homomorphism** = a *signature/rule morphism* `σ` (mapping one
system's syntax to another's) **plus a per-rule SIMULATION obligation**
(`transport_db.rs:139` `clause_sims[k]`: "`σ` simulates source rule `k` in the
target"), transported in one move by `rule_induction`. Two transport engines
realise this shape:

- `relations::transport` (reified-PROP `Φ⟨bool⟩`): carries ONE simulation
  obligation, `σ_hom` ("`σ` commutes with `⟹`", i.e. simulates the single
  structural rule — MP — that `Derivable_DB` has beyond axioms). This note's
  TIER 0/1 live here.
- `transport_db::transport` (free algebra `Φ=nat`): the generic CROSS-RULE-SET
  transport, `clause_sims[k]` per source rule. Currently exercised ONLY at `σ=id`
  (`id_clause_sims`) — the rule-inclusion case. An honest non-identity `σ` with
  proved `clause_sims` is the true cross-system bridge (TIER 2/3).

### The 4-tier ladder (only 0–1 are theorems today)

- **TIER 0 (done).** `σ=id` monotonicity (`relations.rs` identity test) +
  variable-index renaming `σ_f` (`relations_sigma::var_rename_sigma`). Every `σ_f`
  is depth- and shape-preserving: the image of any `⌜var k⌝` is again a single var
  LEAF `⌜var (f k)⌝`.
- **TIER 1 (done — THIS slice).** Intra-carrier propositional **SUBSTITUTION**
  homomorphism on `Φ⟨bool⟩`: atom ↦ arbitrary compound formula
  (`relations_sigma::var_subst_sigma`) — the FOL/HOL-signature-morphism shape in
  miniature, proving `σ` can restructure formulas while simulating the single
  structural rule (MP). Details below.
- **TIER 2 (OPEN — NOT demonstrated).** A cross-rule-set **non-identity `σ` on
  `transport_db`** over the `Φ=nat` free algebra where `mm_database`, **K**
  (`k/reduce.rs`), and WASM all live — a rule morphism between two DIFFERENT
  `RuleSet`s with honest per-rule `clause_sims`. A SUBTERM-rewriting `σ` there
  needs the encoding reified as an inductive `MmExpr := sym(nat) | app(Rec, Rec)`
  with a catamorphic recursor (the `church.rs` backend of `crates/lang/inductive`)
  — the named prerequisite and hard blocker. An OPAQUE whole-judgement `σ`
  (prefix-tag / retag / inject) could land on `Φ=nat` *now* without `MmExpr`, and
  is the right SECOND slice.
- **TIER 3 (north star).** A genuine CROSS-SYSTEM `σ`. K is already the first
  non-Metamath system on this engine, so the first concrete cross-system target is
  **K→Metamath** (both already `RuleSet`s on `Φ=nat`). Then **LF/Dedukti** as the
  UNIVERSAL target: Dedukti is the LF checker Lean/Coq export to, and every rule
  becomes a rewrite rule matching our `RuleSet` + `clause_sims` shape (dual to
  `covalence_k::fragment::rewrite_rules`, what `k/reduce` already lowers). A
  Dedukti signature morphism IS a `σ` + per-rewrite-rule simulation =
  `transport_db`'s interface, so Lean/Coq derivations arriving as rewrite systems
  transport by the identical `rule_induction` move.

Two things the ladder makes explicit: (a) TIER 1 generalises renaming to
propositional **theory-interpretation** (free-monad substitution); (b) the honest
`clause_sims` path on `transport_db` (`Φ=nat`) is the true cross-system bridge and
needs inductive `MmExpr`; (c) K→Metamath is the first concrete cross-system
target, Dedukti the eventual universal `σ`-target for Lean/Coq.

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

## TIER 1 — the propositional SUBSTITUTION `σ_g` (this slice)

Renaming (TIER 0) is depth- and shape-preserving: `σ_f ⌜var k⌝` is always a
single var LEAF. The escalation is **free-monad substitution** — atom ↦ arbitrary
formula. Where `var_rename_sigma` re-plumbs the var slot to `λn. __var (f n)`
(a `nat → nat` index map), `var_subst_sigma(g)` replaces the var slot with a
COMPOUND body that RE-FOLDS an arbitrary substitutee `g n : Φ⟨bool⟩` (for
`g : nat → Φ⟨bool⟩`) against the *other four bound handlers already in scope*:

```text
  σ_g := λA:Φ⟨bool⟩. λ v ¬ ∧ ∨ ⟹.  A (λn. (g n) v ¬ ∧ ∨ ⟹) ¬ ∧ ∨ ⟹
```

The inner `(g n) v ¬ ∧ ∨ ⟹` is `apply_handlers`-style folding of `g n` with the
five bound handler frees (returns `bool = r`, so it typechecks in the `nat → bool`
var slot). Passing the SAME five bound handlers means the substituted formula's
own constructors are interpreted by the outer translation — this is exactly the
free-monad *bind*. Same `__`-prefixed fresh-binder discipline avoids β-capture
between `g`'s handlers and the bound ones; `g` is built via `prop.rs`'s
`p_and_at`/`p_neg_at`/`p_var_at` at `bool` so the substitutee folds are hygienic
closed terms (a mistyped `g` fails `type_of`, not soundness).

### Why it is a genuine escalation, not a relabel

1. `σ_g` changes formula STRUCTURE and DEPTH: `var 0 ↦ var(succ 0) ∧ var 0`
   replaces a single var leaf with an `and`-rooted tree of strictly greater
   constructor depth; the atom-expansion instance `var n ↦ ¬(var n)` adds a `neg`
   former at the root. Every `σ_f` image is a var leaf, so `σ_g` lives strictly
   outside the ENTIRE renaming family. The non-vacuity test asserts
   `σ_g⌜var 0⌝ ≠ ⌜var 0⌝` AND `σ_g⌜var 0⌝ ≠ σ_succ⌜var 0⌝` (a var leaf) — a
   decidable term-shape fact (`and`/`neg` ROOT former vs `var` root former).
2. It is the genuine propositional shape of a **signature/theory-interpretation
   morphism** (atom ↦ arbitrary formula) — the FOL/HOL translation used in real
   metatheory, not a cosmetic relabel.
3. The simulation obligation `σ_hom` is HONESTLY proved, not `σ=id` and not
   reflexivity: `σ_g⌜X⟹Y⌝` and `⌜σ_g X ⟹ σ_g Y⌝` are two DISTINCT compound
   redexes that merely share a β-normal form; `trans(sym)` genuinely relates two
   different terms, and if `σ_g` ever touched the `⟹` slot the equation would be
   FALSE and `trans` would ERROR rather than fabricate (the kernel is the check,
   the `debug_assert_eq` the loud guard).
4. It does NOT secretly need a recursor: `σ_g` rides the same
   catamorphic re-fold-with-modified-handlers trick on carrier `Φ⟨bool⟩` (the
   Church fold has a re-foldable handler). The recursor wall only bites carrier
   `Φ=nat` (TIER 2).

### The three theorems proved (all hypothesis-free)

1. `sigma_hom_of_var_subst(g)` (T1): `⊢ ∀X Y. σ_g ⌜X ⟹ Y⌝ = ⌜σ_g X ⟹ σ_g Y⌝`,
   verbatim equal to `relations::sigma_hom(σ_g)`, for BOTH `g := λn. var(succ n) ∧
   var n` and `g := λn. ¬(var n)`. Same `beta_nf`/`trans`/`all_intro` spine.
2. `sigma_subst_moves_and_deepens` (T2, non-vacuity witness — a `beta_nf`
   equation, not a new axiom): `⊢ σ_g ⌜var 0⌝ = ⌜var(succ 0) ∧ var 0⌝`, with the
   normal form asserted `≠ ⌜var 0⌝` and `≠ σ_succ ⌜var 0⌝` — so `σ_g`
   restructures, not relabels.
3. `transport_at_var_subst` (T3): `transport().inst("sigma", σ_g).imp_elim(T1)` is
   `⊢ Interp DbA DbB σ_g ⟹ Der_DbA S ⟹ Der_DbB (σ_g S)`, hypothesis-free, over
   free `DbA,DbB:Database`, `S:Φ⟨bool⟩`, for both `g`s. `assert_ne` shows
   `derivable_db(DbB, σ_g S) ≠ derivable_db(DbB, S)` — derivability transports
   along an atom-level theory interpretation.

`transport()` is reused **unchanged** — the slice only supplies a richer
`.inst("sigma", …)` + `.imp_elim(…)`. No new kernel rules, no postulates, no TCB
edit.

## TIER 2a — inductive `MmExpr` reified (bundle + structural σ + app-hom, carrier not yet migrated)

*Landed in `crates/kernel/hol/init/src/metalogic/mm_algebra.rs`.* This is the
first genuine reification of the MM-import encoding as an **inductive datatype**
with a **catamorphic recursor**, and the first structural σ + app-homomorphism on
that carrier — but NOT yet transport firing across two real rule sets (the
carrier-migration blocker remains).

### The trait tower rung (L3), and the two impls

`MmAlgebra` is the L3 insulation boundary — "a reified Metamath-expression algebra
over an opaque HOL carrier Φ": `phi`/`sym`/`app`/`encode` +
`structural_sigma`/`sigma_app_hom` + `caps`. It is object-safe (returns bare core
`Term`/`Thm`; Φ is a runtime `fn phi()->Type` value, NOT an associated type — so
`&dyn MmAlgebra` works). The recursor surface (`rec_app`/`comp`/`induct`/`mem`/
`mem_ctor`) lives on a SEPARATE `MmRecursor: MmAlgebra` companion, because only the
inductive backend can honestly implement it. Two impls of the core trait:

- **`FreeAlgebra(&Database)`** — the recursor-free `Φ=nat` free algebra
  (`mm_database` `concat`/`leaf`/`Parser::encode_expr`). `structural_sigma` is an
  OPAQUE identity wrap (no recursor over `concat`), `sigma_app_hom` returns `Err`,
  `caps().structural = false`. The honest degenerate second impl.
- **`MmExprAlgebra`** — the genuine inductive `MmExpr := sym(nat) | app(Rec,Rec)`,
  realized by `ImpredicativeBackend::realize` (byte-identical in shape to the
  `btree` conformance spec that already passes). `caps().structural = true`.

Because BOTH implement the core trait with the same signature, the **insulation
acid-test** is real: one high-level op `encode_pair(alg, db, e1, e2) = alg.app(alg.
encode(db,e1), alg.encode(db,e2))` runs UNCHANGED on both backends, each returning
a well-typed Φ-term of its own carrier (`nat` vs the Church `MmExpr`). A swap of the
low-level encoding leaves the high-level code untouched.

### The reification: `MmExpr` bundle

`ImpredicativeBackend::realize(&NativeHol, &mmexpr_spec())` yields the opaque Church
carrier `MmExpr⟨'r⟩ = (nat→'r)→('r→'r→'r)→'r`, `mem` (= `Wf`), `ctors = [sym, app]`,
and `facts`: `rec_app`, `comp(steps,0/1)`, `induct`, `distinct`, `mem_ctor`,
`injective` at the external `sym`-code position. NOT available (rank-1 wall):
injectivity at `app`'s Rec positions, `prec_app`, decode. All hypothesis-free:
`sym : nat→MmExpr`, `app : MmExpr→MmExpr→MmExpr`, `distinct(0,1)` fires, both `comp`
laws fire.

### The structural σ and its app-homomorphism (the headline)

`structural_sigma(leaf_map)` is the catamorphism `λt. rec_app([λc. sym(leaf_map c),
app], t)`. **The rank-1 subtlety (important):** a catamorphism *to the carrier
itself* is NOT expressible — an endomorphism `C → C` would need `C = MmExpr⟨C⟩`
(infinite), and `comp`'s result type must not mention `'r`. So the fold targets a
**fixed observation instance** `Φ_obs := MmExpr⟨nat⟩`, giving `σ : Φ_dom → Φ_obs`
with `Φ_dom = MmExpr⟨Φ_obs⟩` (the domain at `'r := Φ_obs`, whose handler slots
`nat→Φ_obs` / `Φ_obs→Φ_obs→Φ_obs` match the steps). This is exactly the plan's
risk-1 fallback (state σ at a fixed observation `'r`, as `church.rs`'s
`injective`/`distinct` do).

The **app-homomorphism** `⊢ ∀X Y. σ(app_dom X Y) = app_obs (σ X)(σ Y)` is proved
DIRECTLY: `σ u ≡β rec steps u`, and `rec steps (app l r) ≡β step_app (rec l)(rec r)`
by pure β (this IS `comp(steps,1)`, since the church `app`'s fold applies the
`app`-handler to the folds of its children). Both sides `beta_nf` to the same term,
so the proof is `beta_nf` both sides + `trans` + two `all_intro`s — the identical
spine `relations_sigma` uses at `Φ⟨bool⟩`. **UNCONDITIONAL** (no `Wf` guard), hence
non-vacuous. `sigma_moves_a_term` witnesses `σ(sym_dom 0) = sym_obs(succ 0) ≠
sym_obs 0`, so σ ≠ id.

### What TIER 2a does NOT close

1. **σ is not an endomorphism** (`Φ_dom → Φ_obs`), so it does not plug into
   `transport_db::transport` (which wants `σ : Φ → Φ` on one carrier).
2. **Carrier migration.** The live `mm_database`/K encoders emit `Φ=nat`; `MmExpr`
   is the Church carrier. `MmExprAlgebra::encode` re-lifts a `Φ=nat` tree onto
   `MmExpr` host-side, but `replay_db` / the import hot path are untouched, and
   `check_same_carrier` rejects `nat` vs `MmExpr`. So transport actually firing
   with a structural `MmExpr` σ across two `RuleSet`s does NOT land.
3. **`Wf`-preservation-by-induction** is deferred: `induct`/`mem_ctor` are over the
   polymorphic carrier while σ is `Φ_dom → Φ_obs`, so `λt. Wf(σ t)` does not
   typecheck against the induction carrier without an observation-instance `induct`
   the church backend does not expose. The app-hom (needing only `comp`) lands; the
   induction (needing a matched carrier) does not.

So TIER 2a delivers: the trait tower rung + two impls + the `MmExpr` bundle + the
structural σ + the app-homomorphism-by-`comp` + the non-vacuity witness + the
insulation acid-test. It does NOT re-state transport over `MmExpr` or fire it
across rule sets. See also `notes/vibes/logics/derivation-system-interp.md`.

## Honest scope — what is *not* claimed

- This is **"transport demonstrated at real structural σ (renaming + intra-carrier
  substitution)"**, not "transport re-stated over an inductive encoding" and NOT
  "cross-system transport to Lean/Coq/Dedukti proved". `transport()` itself is
  unchanged; we feed it a genuine non-identity `σ_hom`.
- The substitution re-folds handler slots of the existing Church fold on
  `Φ⟨bool⟩`; it is not a catamorphism over a carved inductive `MmExpr`. That is
  fine for the `Φ⟨bool⟩` carrier (no destructor needed), but does not by itself
  reify the MM-import encoding or cross a `RuleSet` boundary.

## What remains (open)

- **Concrete satisfiable-`Interp` witness for `σ_g` (TIER-1 polish).** `transport_at_var_subst`
  is a genuine hypothesis-free implication *schema* over free `DbA,DbB,S`; unlike the
  `σ=id` case (where `A ⊑ B` gives a concrete `Interp A B id`), no concrete
  `DbA,DbB` with `⊢ Interp DbA DbB σ_g` and a transported nonempty derivation is
  exhibited yet. Straightforward via the `DbSession` singleton pattern
  (`DbA = {var 0}`, `DbB = {var(succ 0) ∧ var 0} = {σ_g(var 0)}`): the one axiom
  `var 0` maps under `σ_g` to `DbB`'s axiom, so `Interp` holds by membership +
  the `T2` β-equation — makes "the transport actually fires" tangible.
- **TIER 2 — MM-import `Φ = nat` cross-rule-set `σ`.** Reify the `mm_database`
  encoding as an inductive `MmExpr := sym(code: nat) | app(MmExpr, MmExpr)` via the
  `church.rs` backend of `crates/lang/inductive`, define a catamorphic
  constant/var/subterm rewrite through `rec_app`, prove its concat-homomorphism
  from the `comp` laws + induction, and feed `transport_db` honest non-identity
  `clause_sims`. (An OPAQUE whole-judgement `σ` — prefix-tag/retag/inject — could
  land on `Φ=nat` *now* without `MmExpr`, and is the right second slice.)
- **Connective-mapping σ.** The same handler-passthrough β argument gives more
  structural translations for free — a connective-swap `σ` (swap `∧`/`∨` handler
  slots, identity on `var`/`imp`) commutes with `enc_imp` identically. A fallback
  if a substitution normalisation ever disagreed; also a template for genuine
  connective maps.
- **TIER 3 — cross-system transport.** K→Metamath first (both `RuleSet`s on
  `Φ=nat`), then Dedukti/LF as the universal `σ`-target for Lean/Coq. Needs TIER 2
  (`transport_db` honest `clause_sims`) plus the concrete foreign rule sets.
- **HOL→ZFC-scale transport** (`Derivable_HOL ⟹ Derivable_ZFC ∘ σ`) — the
  north-star Metamath instance; needs the MM-import structural `σ` plus concrete
  HOL/ZFC rule sets.
