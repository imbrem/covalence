# ACL2 S7: the full definitional principle — concrete design (wf-recursion, measured defuns, merge-sort gate)

*Design for stage S7 of [`acl2-full-plan.md`](./acl2-full-plan.md) /
[`acl2-s7-s12-plan.md`](./acl2-s7-s12-plan.md) items 3–4, consuming the S5 seam
([`acl2-s5-design.md`](./acl2-s5-design.md) §7/§10, implementation reports
§15.2/§15.3). Agent-authored (vibes). Verified against the committed code on
branch `lisp-demo` @ 1022c58f (2026-07-17): `init/recursion.rs` (the graph
template), `init/acl2/{defun.rs, derivable.rs, ordinal.rs, hilbert.rs,
gate_s5d.rs}`. Everything below is untrusted userspace over existing kernel
rules — **no new axioms, no TCB edits**; every object clause's soundness is
discharged by a proved model theorem through the unchanged `discharge_def`
machinery. The crown proof (§4) is skeletoned at `subst_sema`/S6-§9 precision.*

## 0. Decision summary (the judgment calls, made)

1. **The model function for a measured defun is built by the
   `init/recursion.rs` graph recipe transplanted to the carrier**: a
   *single-clause* impredicative least graph relation `G x⃗ a` with
   **ruler-guarded premises** per recursive call site (§4.1); totality (§4.4)
   and determinacy (§4.6) both by **`wf_induct` at the measure-value motive**
   `λo. ∀x⃗. M x⃗ = o ⟹ …` — verbatim the committed `discharge_ind_ord`
   motive pattern. No new induction machinery, no fuel, no `cv_exists`.
2. **Single clause + a body-irrelevance lemma, not per-branch clauses.**
   Flattening the body's IF-tree into per-branch clauses (the literal
   `recursion.rs` shape) is exponential when IFs sit in argument positions;
   the single clause with guarded premises is linear, and the one price — the
   determinacy step needs "the body's value doesn't depend on `bᵢ` when
   site `i`'s rulers fail" — is the decision-free `body_irrel` lemma (§4.5),
   proved by the same body walk that extracts the sites.
3. **Function extraction by ε behind `Thm::define`** (§4.7):
   `F := λx⃗. ε a. G x⃗ a`, the committed `init/quotient.rs`/`rat.rs`
   `Term::select_op` + `select_ax` precedent and exactly `recursion.rs`'s
   assembly move (`natRec = ε`-selected). Foundation-invariant guardrail
   respected: existence/uniqueness are **construction-backed** (graph +
   `wf_induct`); ε only picks the already-unique value, is hidden behind the
   opaque defined constant, and never appears in any transported statement.
   The neutral theorem is `def_eq_model`. There is no ε-free extraction in
   HOL (description = ε); recorded, not fought.
4. **The admissible fragment** (§1): recursive call sites with **f-free
   arguments** (no nested/reflexive calls — this excludes textbook
   `ackermann` and `mc91`, see §1.2), **f-free IF tests**, f-free measure
   over already-admitted heads. Everything else the S4 template required is
   dropped: descent depth, which formals recurse, verbatim-formal passing,
   call-site count are all unconstrained (§8).
5. **Obligations are caller-supplied `Derivable` theorems, re-checked by
   exact statement** (§5): the admission *computes* the obligation encodings
   itself from the parsed body (never trusts the caller's claim of what must
   be proved), demands each supplied theorem be closed with conclusion
   exactly `derivable(env, enc)`, then projects + transports them itself. A
   library obligation kit (§6, the promoted `gate_s5d.rs` scripts) covers the
   `acl2-count` fragment; arbitrary termination automation is ACL2's prover
   and stays out of scope.
6. **Mutual recursion: deferred with a wall** (§7). The tagged-sum reduction
   is fully expressible with this stage's single-function machinery plus
   non-recursive wrappers, so deferring costs no metatheory — it is
   translation-layer work with zero current consumers.
7. **Gate: merge-sort, not ackermann** (§10). Standard ACL2 `ackermann` is
   *reflexive* (nested call `(ack (- m 1) (ack m (- n 1)))`) — outside the
   f-free-site-argument fragment by construction, independent of the `o<`
   fragment (full ε₀ is proved; the lex-pair *measure* is expressible — the
   nested *call* is the blocker). Merge-sort by `acl2-count` halves has no
   nested calls and exercises exactly what S7 adds: `cddr` descent (`EVENS`),
   two-formal measured recursion (`MERGE2`), and a decrease obligation that
   needs an **inductively proved object lemma** (`evens-le`, by IND-ORD on an
   S7-admitted function). Honesty ladder: G3 (EVENS) → G4 (evens-le) → G5
   (MSORT + ground sort demo), each rung a commit (§10.5).
8. **Two small library additions outside the new modules**:
   `transport_holds_open` in `derivable.rs` (the missing n = 0 open
   transport — required to consume the bare `(O-P m)` obligation as a model
   fact, §3.2) and `wf_induct_on` in `ordinal.rs` (the `acc_induct`-shaped
   Rust driver over the proved `wf_induct` theorem, §3.3).
9. **`UserRow` gains `measured: Option<Arc<MeasuredInfo>>`** (§3.4) so ground
   folding and future defthm heuristics can distinguish measured rows without
   a drift-prone side registry. `None` everywhere existing; the install pin
   and every discharge are unchanged.

## 1. The S7 fragment (what a measured defun may look like)

Surface (front-end normalization per S5 §1.1 unchanged):
`(defun f (x₁ … xₙ) (declare (xargs :measure m)) body)` arriving kernel-side
as encoded terms over the formal symbols. **Admissibility (all checked before
anything is minted):**

- `body` is in the committed head fragment (rows + `IF` + `QUOTE` + formals
  + self-calls); every self-call has arity n.
- **Sites**: the self-call occurrences, indexed in leftmost-innermost DFS
  order. Site `i`'s arguments must be **f-free** (a self-call inside another
  self-call's argument list = "nested/reflexive recursion" error, named with
  both sites). Duplicate `(args, rulers)` occurrences get separate sites but
  their obligation encodings are deduplicated (§5.1).
- **Rulers**: for each site, the polarized tests of every `IF` ancestor of
  which the site lies in the then/else branch (ACL2's governing tests):
  `(t, pos)` descending into the then-branch, `(t, neg)` into the else.
  **`f` may not occur in any IF test anywhere in the body** (else some
  ruler-expression would mention `f` before it exists — same chicken-and-egg
  as reflexive functions; walled).
- `m` (the measure encoding) is f-free, over the formals and already-admitted
  heads only.
- k ≥ 1 sites (k = 0 ⟹ "use plain `admit_defun`" error). Sites with zero
  rulers are *allowed* (uniform machinery; their unconditional decrease
  obligation is semantically unsatisfiable, so they simply never admit).
- Formal-name restrictions: the existing `check_new_row` set; S7 internals
  use the fresh prefix `__g*`.

### 1.2 Named exclusions (parse-time errors, gate-tested)

`ackermann` (site 3 nested), `mc91` (nested), any f-in-test body, f-in-
measure, `mutual-recursion` (§7), `lambda` pseudo-terms (unchanged S2
fragment — **not** trivially unlocked; eval/subst have no binder case),
`:well-founded-relation` other than `o<`-on-`o-p`s.

## 2. The body walker — single source of truth (`measured.rs`)

One deterministic translator `site_walk` (the `para_image` precedent —
mirrors `model_image`'s recursion with two extra cases), producing for a spec
over the env-g table (f absent):

- `sites: Vec<Site>` where `Site { args_enc: Vec<Term>, rulers: Vec<(Term,
  bool)> }` (encodings, over formal symbols);
- the **hole-body builder** `bhat(x⃗: &[Term], b⃗: &[Term]) -> Term` — the
  model image of the body with site `i` replaced by `b⃗[i]` (self-calls hit
  the site case; everything else is `model_image` compositional);
- per-site **model builders** `arg_img_i(x⃗)`, `ruler_img_ij(x⃗)` and the
  measure builder `m_img(x⃗)` (plain `model_image_of` at the formal
  bindings).

**Load-bearing invariants** (each asserted by Term equality in code; mismatch
= error, mints nothing):

- (I1) *Substitution coincidence*: `model_image(enc[Xᵣ ↦ argᵣ]) ==
  model_image(enc)[xᵣ := model_image(argᵣ)]` — `model_image` is
  compositional in the formal bindings, so the obligation encodings'
  images (§5.1) coincide syntactically with `m_img(arg_img_i(x⃗))` etc.
- (I2) *Hole-plugging*: `bhat(x⃗, [F(a⃗₁ x⃗), …, F(a⃗_k x⃗)]) ==
  model_image over the g+1 table (F installed) of the body` — makes §4.7's
  conclusion literally the `install_user_rows` pin statement.

## 3. Module layout & small library additions

| where | what |
|---|---|
| `init/acl2/wfrec.rs` (new) | §4: the graph construction W0–W6; input = the walker's builders + the transported model facts; output = `(model: Term, def_eq_model: Thm)`. Defines `"acl2.wfrec.<F>.graph"` and `"acl2.user.<F>"` (model-constant naming uniform with `admit_defun`). |
| `init/acl2/measured.rs` (new) | §1 checks, §2 walker, §5 obligation encodings + `admit_defun_measured`, `measured_fold` ground chase (§9). |
| `init/acl2/oblig.rs` (new) | §6: library-grade obligation scripts — the promoted `gate_s5d.rs` helpers + the `acl2-count` kit. Depends only on `hilbert.rs`'s **public** surface (`Fact`, `derive_under`, `axiom_inst`, `def_inst`, `cong_impl`, `mp`, `eq_*`); re-implements the ~40-line `B` line-builder locally because `hilbert::scripts` is `#[cfg(test)]` and `hilbert.rs` is owned by a concurrent agent (coordination note: fold into one builder when that settles; do NOT edit hilbert.rs in S7). |
| `derivable.rs` | **`transport_holds_open(env, projected, binds)`** — the `transport_implies_open` skeleton with `n_hyps == 0` *required* (reject a spine, mirror-image of the existing n = 0 rejection; entry points stay disjoint per precedent), no `equal_holds` finish: from `⊢ ∀σ. ¬(eval ⌜c⌝ σ = anil)` to `⊢ ∀x⃗:A. ¬(⟦c⟧(x⃗) = anil)`. Plus **`with_ind_ord_shape(env, k)`** (push `k` into `ind_ord` if absent — explicit opt-in, §8.2; admission does **not** auto-register). |
| `ordinal.rs` | **`pub(crate) fn wf_induct_on(&self, motive, zname, yname, prove_case)`** — the `acc_induct` driver shape routed through the `wf_induct` theorem: `prove_case(z, ih)` gets `ih : {…} ⊢ ∀y. below y z ⟹ motive y` and returns the β-contraction of `motive z`; result `⊢ ∀x. ¬(op x = anil) ⟹ (motive x)` (applied form). Plus tiny `neg_ruler_intro`/`neg_ruler_elim` helpers (§5.3). |
| `defun.rs` | `fold_ground` head extensions (§9): `aif` guard-deciding, `CAR`/`CDR`/`CONSP` on values, `<` via `lt_lit`; measured-row dispatch through `def_eq_model` with a visit budget. |
| `derivable.rs` (`UserRow`) | `measured: Option<Arc<MeasuredInfo>>`, `MeasuredInfo { measure_enc, sites }`; `None` in `admit_defun` / ordinal rows / tests. No discharge or pin change. |

`admit_defun_measured` consumes an `Acl2Session` (it needs the *current
generation's* cached soundness to project obligations) and returns the next
generation's session, mirroring `Acl2Session::admit_defun`.

## 4. THE CROWN — the wf-recursion model theorem (`wfrec.rs`)

Fixed data for one candidate (all HOL-side, over env generation g):
carrier `A`; arity n with frees `x⃗ = x₁…xₙ` (internal names `__gx0…`);
measure image `M x⃗`; k sites with argument images
`A⃗ᵢ x⃗ = (aᵢ₁ x⃗, …, aᵢₙ x⃗)`, ruler propositions
`ρᵢⱼ(x⃗) := ¬(⟦tᵢⱼ⟧ x⃗ = anil)` (pos) or `⟦tᵢⱼ⟧ x⃗ = anil` (neg);
hole body `B̂ x⃗ b⃗`. Transported inputs (§5.3):

```text
OP_M  : ⊢ ∀x⃗. ¬(op (M x⃗) = anil)
DECᵢ  : ⊢ ∀x⃗. ρᵢ₁ ⟹ … ⟹ ρᵢ_{rᵢ} ⟹ ¬(olt (M (A⃗ᵢ x⃗)) (M x⃗) = anil)
```

### 4.1 W0 — the graph

With `β := A → … → A → bool` (n+1 arrows) and, for `S : β`,

```text
chainᵢ(S; x⃗, b) := ρᵢ₁(x⃗) ⟹ … ⟹ ρᵢ_{rᵢ}(x⃗) ⟹ S (A⃗ᵢ x⃗) b
Cl(S) := ∀x⃗ b₁…b_k. chain₁(S; x⃗, b₁) ⟹ … ⟹ chain_k(S; x⃗, b_k)
                       ⟹ S x⃗ (B̂ x⃗ b⃗)
G := Thm::define("acl2.wfrec.<F>.graph",
                 λx⃗ a. ∀S:β. Cl(S) ⟹ S x⃗ a)
```

— the impredicative least-predicate shape of `ordinal.rs`'s `acc`
(single-clause, no `RuleSet`), generalized to n+1 arguments and guarded
premises. All quantifiers/implications are ordinary HOL connectives; the
rulers are *b-free and f-free by §1*, which is what every proof below leans
on.

### 4.2 W1 — introduction: `⊢ Cl(G)`

The `acc_intro` pattern: assume the k chains at `G`; fix `S`, assume
`Cl(S)`; per site `i` turn `chainᵢ(G)` into `chainᵢ(S)` (assume `ρᵢ⃗`,
fire the chain → `G (A⃗ᵢ x⃗) bᵢ`, `apply_def(G)` + `eq_mp`, `all_elim S`,
`imp_elim Cl(S)` → `S (A⃗ᵢ x⃗) bᵢ`, `imp_intro` the `ρ`s back); fire
`Cl(S)` at `x⃗ b⃗`; `imp_intro Cl(S)`, `all_intro S`, fold by
`apply_def(G).sym().eq_mp` → `G x⃗ (B̂ x⃗ b⃗)`; `imp_intro` the chains,
`all_intro b⃗, x⃗`.

### 4.3 W2 — inversion (continuation-passing, the S5-deviation-1 style)

Not a packaged ∃-theorem: a Rust opener

```rust
fn graph_open(&self, hg: Thm /* Γ ⊢ G x⃗ a */, tag: &str,
              cont: &dyn Fn(&[Term] /*b⃗ frees*/, &[Thm] /*chainᵢ(G)*/,
                            &Thm /*Γ' ⊢ a = B̂ x⃗ b⃗*/) -> Result<Thm>)
    -> Result<Thm>
```

built the standard conjunction-trick way: apply the definition of `G` at

```text
S₀ := λx⃗ a. G x⃗ a ∧ ∃b₁…b_k. chain₁(G) ∧ (… ∧ (chain_k(G) ∧ a = B̂ x⃗ b⃗))
```

(right-nested ∧/∃). Closure of `S₀`: given the clause premises
`chainᵢ(S₀)`, project each to `chainᵢ(G)` (compose under the `ρ`s with
`and_elim_l`) — the left component closes by **W1**, the right by
`exists_intro` at the clause's own `b⃗` with the projected chains + `refl`.
Then `G x⃗ a → S₀ x⃗ a → and_elim_r`, k nested `exists_elim`s at fresh
`__gb<tag>ᵢ`, β-clean, hand the pieces to `cont`. First-order throughout —
no choice needed (this is *why* the premises carry one `bᵢ` each instead of
a function, dodging the higher-order-functional formulation's AC step).

### 4.4 W3 — totality: `⊢ ∀x⃗. ∃a. G x⃗ a`

By `wf_induct_on` at the **measure-value motive** (the committed
`discharge_ind_ord` §7.3 pattern, verbatim):

```text
P_tot := λo:A. ∀x⃗. (M x⃗ = o) ⟹ ∃a. G x⃗ a
```

Closure at `o` with `IH : ∀y. below y o ⟹ P_tot y`; fix `x⃗`,
`HM : M x⃗ = o`. **Per site i, derive `Eᵢ : ⊢ctx ∃b. chainᵢ(G; x⃗, b)`**
by a *sequential* ruler split (rᵢ+1 leaves, linear — not 2^rᵢ):

- Walk `j = 1..rᵢ`; at ruler j, boolean `lem` on `⟦tᵢⱼ⟧ x⃗ = anil`:
  - the branch **contradicting** `ρᵢⱼ`'s polarity closes immediately with
    witness `b := anil`: assume the chain's antecedents, `not_elim` the
    contradiction (`ρᵢⱼ` vs the split hypothesis), `false_elim` to
    `G (A⃗ᵢ x⃗) anil`, `imp_intro` the `ρ`s, `exists_intro`;
  - the agreeing branch records `ρᵢⱼ` and continues.
- **All-rulers-hold leaf**: `DECᵢ` at `x⃗` + the recorded `ρ`s →
  `¬(olt (M (A⃗ᵢ x⃗)) (M x⃗) = anil)`; rewrite by `HM` → `… o …`;
  `OP_M` at `A⃗ᵢ x⃗`; `Ordinals::below_intro` →
  `below (M (A⃗ᵢ x⃗)) o`; `IH` → `P_tot (M (A⃗ᵢ x⃗))`, applied at
  `A⃗ᵢ x⃗` with `refl` → `∃a. G (A⃗ᵢ x⃗) a`; `exists_elim` (witness
  `__gw`) → `chainᵢ` holds at `b := __gw` (weaken by `imp_intro` of the
  `ρ`s — they are already hypotheses), `exists_intro`.
- Combine the `lem` branches by `disj_cases` back up the walk (all leaves
  state the same `∃b. chainᵢ`).

Then k nested `exists_elim`s over `E₁…E_k` around: **W1** at `x⃗, b⃗` →
`G x⃗ (B̂ x⃗ b⃗)` → `exists_intro` → `∃a. G x⃗ a`. `imp_intro HM`,
`all_intro x⃗` closes the motive case. Final assembly: `wf_induct_on`
output at `o := M x⃗`, its `¬(op (M x⃗) = anil)` hypothesis = `OP_M x⃗`,
apply at `x⃗` with `refl`, `all_intro x⃗`. ∎

### 4.5 W4 — body irrelevance

```text
body_irrel : ⊢ ∀x⃗ b⃗ b⃗'. Π₁ ⟹ … ⟹ Π_k ⟹ B̂ x⃗ b⃗ = B̂ x⃗ b⃗'
   where Πᵢ := ρᵢ₁ ⟹ … ⟹ ρᵢ_{rᵢ} ⟹ bᵢ = bᵢ'
```

By Rust recursion over the body encoding — the **same traversal as
`site_walk`** (shared code path; drift impossible), carrying the polarized
test facts of the path as hypotheses and returning `Γ_path ⊢ ⟦node⟧ b⃗ =
⟦node⟧ b⃗'`:

- **b-free subtree** (no site below): `Thm::refl` — the fast path, so `lem`
  splits happen only above sites.
- **Site i leaf**: the path context holds exactly `ρᵢ⃗` (rulers *are* the
  branch-ancestor tests, by definition); fire premise `Πᵢ` → `bᵢ = bᵢ'`.
- **IF node** `aif ⟦T⟧ y z` (T is b-free by the f-free-tests wall): `lem`
  on `⟦T⟧ x⃗ = anil`.
  - ≠-branch: `if_t` (`imp_elim` the ≠) rewrites both sides to the
    y-images; recurse into y with the context extended by `pos(T)`;
    `trans`/`sym` composition.
  - =-branch: `cong` the test to `anil` + `if_nil` on both sides; recurse
    into z with `neg(T)`.
  - `disj_cases` the two branches.
- **Other compound node** `h ⟦u₁⟧ … ⟦u_m⟧`: recurse each argument,
  compose by the `cong_arg`/`cong_fn` chain (the `fold_ground` argument
  loop shape).

`imp_intro` the `Π`s in site order, `all_intro b⃗', b⃗, x⃗`. Linear in
body size; decision-free. Budget as this stage's mechanical hotspot #1.

### 4.6 W5 — determinacy: `⊢ ∀x⃗ a a'. G x⃗ a ⟹ G x⃗ a' ⟹ a = a'`

`wf_induct_on` at

```text
P_det := λo. ∀x⃗ a a'. (M x⃗ = o) ⟹ G x⃗ a ⟹ G x⃗ a' ⟹ a = a'
```

Closure at `o`, `IH`; fix `x⃗, a, a'`, `HM`, `Hg, Hg'`. `graph_open` on
both (tags `"l"`/`"r"`, frees `__gbl*`/`__gbr*`) → chains + `Ea : a = B̂
x⃗ b⃗`, `Ea' : a' = B̂ x⃗ b⃗'`. **Per site i, derive `Πᵢ`** (no case
split needed — the splits live inside W4): assume `ρᵢ⃗`; fire both chains
→ `G (A⃗ᵢ x⃗) bᵢ`, `G (A⃗ᵢ x⃗) bᵢ'`; `DECᵢ` + `HM`-rewrite + `OP_M` +
`below_intro` + `IH` (at `A⃗ᵢ x⃗`, `refl`) → `bᵢ = bᵢ'`; `imp_intro`
the `ρ`s. **W4** at `x⃗ b⃗ b⃗'` fired with the `Π`s →
`B̂ x⃗ b⃗ = B̂ x⃗ b⃗'`; `Ea.trans(·).trans(Ea'.sym())` → `a = a'`.
Close as in W3 (`o := M x⃗`, `OP_M`, `refl`), `all_intro`. ∎

### 4.7 W6 — the function and its defining equation

```text
F := Thm::define("acl2.user.<F>", λx⃗. App(select_op(A), λa. G x⃗ a))
def_eq_model : ⊢ ∀x⃗. F x⃗ = B̂ x⃗ (F (A⃗₁ x⃗), …, F (A⃗_k x⃗))
```

(by invariant I2 the RHS **is** `model_image` of the body over the g+1
table — the exact `install_user_rows` pin statement). Proof:

1. `sel : ⊢ ∀x⃗. G x⃗ (F x⃗)` — W3 at `x⃗` → `∃a. G x⃗ a`;
   `exists_elim` with step `∀a. G x⃗ a ⟹ G x⃗ (ε(λa. G x⃗ a))` =
   `Thm::select_ax(λa. G x⃗ a, __ga)` + `beta_reduce`/`beta_expand`
   plumbing (the `quotient.rs` moves); rewrite the ε-term to `F x⃗` by
   `apply_def(F, x⃗).sym()`.
2. Per site i: `chainᵢ(G; x⃗, F (A⃗ᵢ x⃗))` — from `sel` at `A⃗ᵢ x⃗`,
   weakened under the `ρ`s (no split needed: it holds unconditionally).
3. **W1** → `G x⃗ (B̂ x⃗ ⟨F (A⃗ᵢ x⃗)⟩)`.
4. **W5** at `(a := F x⃗ (by sel), a' := step 3)` → the equation;
   `all_intro x⃗` (formal-named frees for the pin, i.e. the driver renames
   `__gx*` to the formals before closing — the `prove_def_eq_model`
   convention). ∎

Uniqueness of `F` *as a function* (fun_ext) is neither needed nor stated;
W5 is the only uniqueness consumer.

## 5. Measured defun admission (`measured.rs`)

### 5.1 Obligation encodings (computed, never trusted)

For the parsed spec (walker output §2), with `m[X⃗ ↦ A⃗ᵢ]` the
Rust-level syntactic substitution of formal symbols by site-argument
encodings:

```text
enc_op    := ⌜(O-P m)⌝
enc_decᵢ  := ⌜(IMPLIES r_{i1} (… (IMPLIES r_{i rᵢ} (O< m[X⃗ ↦ A⃗ᵢ] m))))⌝
   where r_{ij} := t_{ij} (pos)  |  (EQUAL t_{ij} 'NIL) (neg)
```

zero-ruler sites give a bare `⌜(O< … m)⌝`. Identical `enc_dec`s are
deduplicated (site → obligation-slot map retained).

### 5.2 `admit_defun_measured(sess, spec, d_op: Thm, d_decs: Vec<Thm>)`

1. `check_new_row` + §1 admissibility; walker runs (dry, over the g table).
2. Recompute §5.1; check `d_op`/each `d_decs[slot]` is **closed** with
   conclusion exactly `derivable(env, enc)` — mismatch errors *naming the
   slot and the expected encoding* (the §10 negative controls hang here).
3. Project through `sess.soundness()` (`Acl2Session::project`).
4. Transport: `enc_op` via **`transport_holds_open`**; each `enc_dec` via
   `transport_implies_open` (holds-form conclusion — `O<` is not
   EQUAL-headed, so the existing code path already leaves
   `¬(olt … = anil)`), zero-ruler ones via `transport_holds_open`. Binds =
   the formals as HOL frees (coverage check is the existing one).
5. **Normalize** (§5.3) → `OP_M`, `DECᵢ` in the §4 shapes; assert (I1) the
   conclusions' subterms equal the walker's `m_img`/`arg_img` compositions.
6. `wfrec::construct` (§4) → `(model, def_eq_model)`.
7. Assemble `UserRow { rec_formal: None, measured: Some(info), def_enc =
   ⌜(EQUAL (f X⃗) body)⌝, … }`; `install_user_rows` (ONE rebuild; the
   fail-safe pin re-checks `def_enc` and `def_eq_model` against
   `model_image` over the extended table — respected, not bypassed).
8. Return the new generation's session. Steps 1–5 mint nothing; 6 mints
   only inert defined constants before the pin.

Also check up front that the env's `O-P`/`O<` rows carry THE ordinal model
constants (`ordinals().op/olt` pointer equality — the `discharge_ind_ord`
precedent), i.e. the env descends from `with_ordinals`.

### 5.3 Transport normalization

`transport_implies_open` assumes each antecedent's *image* ≠ `anil`, so a
neg ruler `(EQUAL t 'NIL)` arrives as `¬(aequal ⟦t⟧ anil = anil)` while §4
wants the clean `⟦t⟧ = anil`. `normalize_dec` re-derives the clean form
once per obligation: assume the clean `ρ`s; for a neg ruler produce the
transported antecedent by `neg_ruler_intro` (from `⟦t⟧ = anil`, rewrite in
the S1 `equal_refl` model law `aequal anil anil = t`, `t_ne_nil`); fire the
transported theorem; `imp_intro`/`all_intro` back. (`neg_ruler_elim` =
`aequal_holds`, the inverse, for §6 scripts.)

## 6. The obligation library (`oblig.rs`) — the `gate_s5d.rs` prototype, generalized

Promoted to library surface (per the recorded S5d deviation 4; gate_s5d.rs
keeps its tests, now importing from here):

- **Script utilities**: local `B` line-builder, `under`, `by_cases`,
  `fact_inst`, `detach`, `eq_mp_u`, `contra_u`, `cong1_u`, `if_true_u`,
  `if_false_u`, `natp_intro_u`, `transfer_natp`, plus new `and_intro_u`/
  `and_elim_u` for the `(IF a b 'NIL)` AND-encoding (needed to move
  between a single governing `q` and per-site ruler lists) and
  `lt_to_olt` (the promoted №15 tail: lines `(< u v)`, `(NATP u)`,
  `(NATP v)` → `(O< u v)` via `not_consp_of_natp` + the O< Def's
  finite-finite branch).
- **Object lemmas** (promoted verbatim): `natp_nonneg_fact`,
  `natp_integerp_fact`, `not_consp_of_natp`, `natp_op_fact`.
- **The count kit** `count_kit(env) -> Result<CountKit>`: requires
  `ACL2-COUNT` admitted with the canonical body (`count_spec` promoted
  here; checked by `def_enc` Term equality, else error). Provides `Fact`s:
  `natp_count` (`D ⌜(NATP (ACL2-COUNT X))⌝`, the №15 derivation),
  `op_count`, `count_cdr_lt` / `count_car_lt`
  (`D ⌜(IMPLIES (CONSP X) (< (ACL2-COUNT (CDR|CAR X)) (ACL2-COUNT X)))⌝`),
  their `O<` forms `count_cdr_dec` / `count_car_dec` (№15 + `lt_to_olt`),
  and `count_cdr_le` (unconditional
  `D ⌜(EQUAL (< (ACL2-COUNT X) (ACL2-COUNT (CDR X))) 'NIL)⌝` — consp arm
  strict, atom arm via `default-cdr` + ground `(ACL2-COUNT 'NIL) = '0` +
  `natp_nonneg`).
- **S7 pack rows** (added in `with_ordinals`'s pack, same kinds as S5 §8 —
  Schema/ModelImplies only, each a one-line discharge from the committed
  int-order helper layer + `alt_iff`/`intval` completion; ±2 additions of
  the same kinds pre-authorized, record in §12):

| row | statement |
|---|---|
| `lt-trans` | `(IMPLIES (< A B) (IMPLIES (< B C) (< A C)))` |
| `le-trans` | `(IMPLIES (EQUAL (< B A) 'NIL) (IMPLIES (EQUAL (< C B) 'NIL) (EQUAL (< C A) 'NIL)))` |
| `lt-le-trans` | `(IMPLIES (< A B) (IMPLIES (EQUAL (< C B) 'NIL) (< A C)))` |
| `le-lt-trans` | `(IMPLIES (EQUAL (< B A) 'NIL) (IMPLIES (< B C) (< A C)))` |
| `plus-lt-mono` | `(IMPLIES (< A B) (< (BINARY-+ C A) (BINARY-+ C B)))` |
| `plus-lt-mono-r` | `(IMPLIES (< A B) (< (BINARY-+ A C) (BINARY-+ B C)))` |
| `plus-le-mono` | `(IMPLIES (EQUAL (< B A) 'NIL) (EQUAL (< (BINARY-+ C B) (BINARY-+ C A)) 'NIL))` |
| `plus-le-l` | `(IMPLIES (EQUAL (< A '0) 'NIL) (EQUAL (< (BINARY-+ A B) B) 'NIL))` |
| `default-car` | `(IMPLIES (EQUAL (CONSP X) 'NIL) (EQUAL (CAR X) 'NIL))` |
| `default-cdr` | `(IMPLIES (EQUAL (CONSP X) 'NIL) (EQUAL (CDR X) 'NIL))` |

(`default-car/cdr` discharge from the committed `car_atom`/`car_nil`-family
model laws; the order/mono rows through `alt_iff_at` + `intval_plus` + the
S5c int-order helper layer, valid for **all** carrier values via the
`intval` completion, exactly like `plus-nonneg`.) Env layout/count gates
(S5 G3 №9-style) update accordingly — pack goes into `with_ordinals`, so
the ordinal env's clause count moves from 87 to 87 + 10 = 97 and gate
constants are re-pinned (record exact numbers in §12 at landing).

**Scope honesty**: `oblig.rs` + the pack cover the merge-sort ladder's
scripts. It is *not* a termination prover; measured defuns outside the
count fragment supply their own obligation `Fact`s through the same
checked API.

## 7. Mutual recursion — DEFERRED (decision + justification)

Walled with a precise SKELETONS entry, because:

1. **No metatheory is missing.** The standard tagged-sum reduction — one
   packed function `F` on `(cons 'fᵢ (list x⃗))` with body
   `(IF (EQUAL (CAR P) 'f₁) body₁' …)`, each original `fᵢ` a
   *non-recursive* wrapper `(fᵢ x⃗) := (F (CONS 'fᵢ (LIST x⃗)))` admitted
   by plain `admit_defun` — is entirely inside this stage's fragment
   (`F`'s sites are f-free-argumented, tests are `EQUAL`-on-quoted-symbols;
   the combined measure is the user's per-function measures dispatched on
   the tag). When demand arrives it is walker/front-end work only.
2. **Zero current consumers**: neither the merge-sort gate nor the S11
   book candidates (`std/lists`-tier) use `mutual-recursion`.
3. Doing it now roughly doubles the walker/obligation surface (per-function
   rulers across bodies, tag plumbing in `def_enc`s) with no gate to keep
   it honest.

## 8. What the measured principle subsumes for free / what stays walled

**Free** (no code beyond §1–§5; G3/G5 exercise the starred ones):

- deeper structural descent* (`cddr`, `caar`, any f-free composition);
- multi-formal recursion* (several changing formals, e.g. `MERGE2`);
- non-verbatim arguments at *any* position — accumulators, swapped
  formals (S4 demanded verbatim non-recursive formals; the graph doesn't);
- multiple call sites per branch*, tree recursion beyond the S4 template;
- arbitrary f-free governing tests (not just `(CONSP xr)`);
- arbitrary f-free measures into `o-p`s — the full ε₀ order is already
  proved, so lexicographic/`make-ord` measures cost nothing extra.

**Walled** (each a named parse error or SKELETONS entry): nested/reflexive
calls (`ackermann`, `mc91`), f in IF tests, mutual recursion (§7), `lambda`
(unchanged S2 fragment), multi-case IND-ORD schemes (§8.2), guards (S12).

### 8.2 IND-ORD shape growth

The clause family is already generic in `k` (S5 §7.3 discharge; recorded in
§15.3). S7 adds only the explicit `with_ind_ord_shape(env, k)` helper —
**no auto-registration at admission** (every registered shape costs a
clause + discharge in each generation's soundness; register on demand).
The single-`q`, k-IH template covers defthms by the induction scheme of any
measured defun **whose sites share one ruler set** (the AND-encoded `q` —
`EVENS` with k = 1, `MSORT`/`MERGE2` at k = 2 if ever needed). Schemes with
*different* rulers per site (true multi-case) are a new clause template —
walled, same family, no new soundness idea.

## 9. Ground folding for measured rows (the demo path)

`fold_ground` extensions (all at the single head-dispatch site, each an
existing-law dispatch, per the standing SKELETONS pre-authorization):
`aif` (fold the guard to a value; `anil` → `if_nil`, non-nil value →
value-≠-nil via the `int_ne`/`sym_ne`/`consp`-family laws `ord_fold`
already uses, then `if_t`), `CAR`/`CDR`/`CONSP` on values
(`proj_scons`, `consp_atom/nil/cons`, `car_atom/car_nil`-family),
`<` via `lt_lit`. Measured user rows dispatch through **`def_eq_model`
instances** (`all_elim` at the argument values — never `apply_def(def_eq)`,
which would unfold the ε body), then recurse on the RHS; this loop is the
one non-structural recursion in the folder, so it carries a visit budget
(exhaustion = error, fails safe). `UNARY--`/`*` folds remain absent
(SKELETONS minor stands; the gate bodies don't need them).

## 10. Gates (each `check()`-style: `hyps().is_empty()` + exact statements; negative controls mint nothing)

Session: `with_ordinals(s6_env)` (now incl. the §6 pack) + `ACL2-COUNT`
(plain S4) — the `g4_session` pattern, extended per rung.

**G1 — walker (pure syntax, `measured.rs` tests):**
1. `t_walker_sites` — exact sites/rulers/obligation encodings for the
   `EVENS`, `MERGE2`, `MSORT` bodies (hand-pinned terms).
2. `t_walker_rejects` — ackermann body (nested, error names both sites),
   f-in-test, f-in-measure, k = 0, unknown head, arity mismatch.

**G2 — transports:**
3. `t_transport_holds_open` — on the projected `⌜(O-P (ACL2-COUNT X))⌝`
   (via the kit): exact `⊢ ∀x. ¬(op (count_model x) = anil)`; negative:
   IMPLIES-spine formula rejected here AND bare-holds rejected by
   `transport_implies_open` (the disjoint-entry cross-controls).

**G3 — EVENS admits (the first rung; commit alone):**
4. `t_evens_admits` — `EVENS` (`(IF (CONSP L) (IF (CONSP (CDR L)) (CONS
   (CAR L) (EVENS (CDR (CDR L)))) (CONS (CAR L) 'NIL)) 'NIL)`, measure
   `(ACL2-COUNT L)`; obligations from the kit: `op_count` +
   `count_cdr_dec` composed at `(CDR L)`/`L` through `lt-trans` +
   `lt_to_olt`) — exact `def_enc`; `def_eq_model` asserted equal to the
   recomputed `model_image` equation (the pin, re-asserted in-test); env
   layout numbers; `derive_def` exact; the new generation's `soundness()`
   proves (closed, exact ∀A statement — this exercises the measured row's
   `discharge_def` end-to-end).
5. `t_evens_ground` — `⊢ D ⌜(EQUAL (EVENS '(1 2 3 4 5)) '(1 3 5))⌝` via
   the computation clause + `measured_fold`, transported (`transport_equal`)
   to `⊢ evens_model ⌜(1 2 3 4 5)⌝ = ⌜(1 3 5)⌝`; an odd-length and an
   atom input as second/third cases.
6. `t_measured_negative_controls` — (a) **non-decreasing measure**:
   `EVENS-BAD` (site argument `L` instead of `(CDR (CDR L))`) with the
   *genuine* EVENS decrease theorem supplied → error naming decrease slot
   0 and the expected encoding
   `⌜(IMPLIES (CONSP L) (IMPLIES (CONSP (CDR L)) (O< (ACL2-COUNT L)
   (ACL2-COUNT L))))⌝`; env unchanged, nothing installed. (b) measure `X`
   with `op_count` supplied → `O-P`-slot mismatch named. (c) `d_op` with
   hypotheses → rejected. (d) admission on a non-ordinal env (`s6_env`) →
   ordinal-rows check error.

**G4 — the inductive defthm (second rung):**
7. `t_evens_le_by_ind_ord` — `evens-le :=
   ⌜(EQUAL (< (ACL2-COUNT X) (ACL2-COUNT (EVENS X))) 'NIL)⌝` by
   `derive_ind_ord` (k = 1, `v := X`, `m := (ACL2-COUNT X)`,
   `q := (IF (CONSP X) (CONSP (CDR X)) 'NIL)`, `t₁ := (CDR (CDR X))`;
   base = `cases` on `(CONSP X)` — atom arm via count-of-`'NIL` ground +
   `natp_nonneg`, cons-singleton arm via count unfolds + `consp-cons`/
   `car-cons`/`cdr-cons` + `plus-le-mono`/`plus-le-l`; step = IH +
   `count_cdr_le`-family + the mono/trans rows; decrease premise = the
   EVENS admission obligation reshaped to single-`q` form via
   `and_elim_u`); exact `Derivable` statement; transported
   (`transport_equal_open`) to
   `⊢ ∀x. alt (count_model x) (count_model (evens_model x)) = anil`.
8. `t_evens_lt` — the strict corollary
   `⌜(IMPLIES (CONSP X) (IMPLIES (CONSP (CDR X)) (< (ACL2-COUNT (EVENS X))
   (ACL2-COUNT X))))⌝`, **non-inductively** from №7 INSTed at
   `(CDR (CDR X))` + count unfolds + `lt-le-trans`/`plus-lt-mono`;
   transported via `transport_implies_open` (exact guarded model
   statement).

**G5 — merge-sort (THE S7 gate):**
9. `t_merge_msort_admit` — `ODDS := (EVENS (CDR L))` (plain
   `admit_defun`); `MERGE2` (2-formal, measure
   `(BINARY-+ (ACL2-COUNT X) (ACL2-COUNT Y))`, sites
   `((CDR X), Y)` / `(X, (CDR Y))` under rulers
   `[(CONSP X)⁺, (CONSP Y)⁺, (< (CAR X) (CAR Y))^{±}]`; obligations:
   `natp`-of-sum via `integerp-plus`/`plus-nonneg` + `natp_op`, decreases
   via `count_cdr_lt` + `plus-lt-mono-r`/`plus-lt-mono` + `lt_to_olt` over
   `consp-plus`); `MSORT` (`(IF (CONSP X) (IF (CONSP (CDR X)) (MERGE2
   (MSORT (EVENS X)) (MSORT (ODDS X))) X) X)`, k = 2, decreases from
   №8 + `evens-le`@`(CDR X)` + `count_cdr_lt` + `le-lt-trans`). Exact
   def-eqs, layouts, generation soundness proves.
10. `t_msort_ground` — **the demo**:
    `⊢ D ⌜(EQUAL (MSORT '(3 1 2)) '(1 2 3))⌝` and a duplicates case
    `'(2 1 2 1)` → `'(1 1 2 2)`, derived (`measured_fold` through all
    three functions incl. `<` deciding) and transported:
    `⊢ msort_model ⌜(3 1 2)⌝ = ⌜(1 2 3)⌝` (exact).
11. `t_msort_negative` — `MSORT-BAD` (site 1 argument `X` instead of
    `(EVENS X)`) with the genuine msort obligations → decrease-slot
    mismatch named; nothing installed.

**G6 — shape growth (minor):**
12. `t_ind_ord_shape2` — `with_ind_ord_shape(env, 2)`: clause count +1,
    soundness proves (the generic-in-k discharge exercised at k = 2);
    `derive_ind_ord` at an unregistered k = 3 still errors.

### 10.5 Honesty ladder

G3 commits alone (*"the measured definitional principle is live"* — a
genuinely non-S4 defun admitted through wf-recursion). G4 next (first
inductive defthm about an S7 function, IND-ORD end-to-end on the new
tier). G5 is the stage gate. If G5's script volume walls, G3+G4 land as
true rungs and the wall becomes a precise SKELETONS entry naming the
remaining obligation scripts — gates only ever assert what is proved.

## 11. Risk register

| risk | mitigation |
|---|---|
| W4/W3 skeletons hide a β/fresh-name trap under k nested ∃-elims + nested drivers | the `__g*` prefix discipline + per-call tags (the S5 `__c<tag>`/`__w*` precedent); drivers re-close eagerly; motive instances kept applied, single-top β only (`n2i_mk` lesson) |
| walker/model-image drift (I1/I2) | one shared traversal (`site_walk` also drives W4); invariants asserted by Term equality at admission; the install pin + `discharge_def` catch anything that slips — kernel error, never unsoundness |
| script volume for G4/G5 (deduction-compiler quadratic-ish, recorded S5 minor) | per-branch lemmas composed via `cases` (`Fact` imports — the №15 structure); count kit derived once per generation and reused; ladder rungs commit independently |
| soundness cost growth (pack +10 axioms; each measured defun +4 clauses; G5 env ≈ 111 clauses) | measure per rung; one shared LazyLock session per gate group; `family_soundness` remains the recorded escape hatch |
| `transport_implies_open` antecedent-form mismatch for neg rulers | `normalize_dec` (§5.3) is a total, checked re-derivation; a wrong form fails `imp_elim`, mints nothing |
| ε objection (foundation-invariance) | construction-backed existence/uniqueness; ε hidden behind `Thm::define` (quotient.rs/rat.rs/natRec precedents); `def_eq_model` is the neutral theorem; note kept in `acl2-fidelity.md` at landing |
| `measured_fold` divergence on a buggy chase | visit budget, error = fails safe; ground gates keep it honest |
| `UserRow` field ripple across constructors/tests | additive `Option` field, `None` default at every existing site; pin/discharges untouched |
| concurrent-agent overlap (`hilbert.rs`/`simplify.rs` owned elsewhere) | S7 edits none of the owned files; `oblig.rs` uses only `hilbert.rs`'s existing pub surface + a local line-builder; fold-in deferred |
| pack-row model proofs fight the int kit | same kinds as the landed S5c rows (`plus-nonneg` recipe); ±2 substitutions of the same kinds pre-authorized, recorded in §12 |

## 12. Out of scope (SKELETONS entries on landing) + implementation report

Out of scope: mutual recursion (§7, with the tagged-sum recipe recorded);
nested/reflexive defuns (`ackermann`, `mc91` — named); f in tests;
multi-case IND-ORD templates (§8.2); `lambda`; guard verification (S12);
termination automation beyond the count kit; `UNARY--`/`*` ground folds;
defthms by `MSORT`'s own induction scheme (needs k = 2 shape + the §8.2
same-ruler `q` packing — G6 proves the clause side only); promoting
`oblig.rs`'s line-builder into `hilbert.rs` (owned elsewhere).

On landing: delete the S7 half of the SKELETONS severe entry (replace with
the walls above), update the ordinal-env clause-count constants (§6), and
append the implementation report here.

### 12.1 Implementation report

*(append at landing; record deviations from §4's skeletons, the exact pack
row list, gate timings, and any ladder walls, per the running discipline.)*

## 13. Order of work (commit per slice)

1. **S7a** — `transport_holds_open` + `wf_induct_on` + walker + G1/G2.
2. **S7b** — `wfrec.rs` W0–W6 + `admit_defun_measured` + `UserRow.measured`
   + fold extensions + the §6 pack rows + kit + **G3** (commit: the
   principle is live).
3. **S7c** — `evens-le`/`evens-lt` scripts + **G4**.
4. **S7d** — `MERGE2`/`ODDS`/`MSORT` + **G5** (THE gate) + **G6**; SKELETONS
   + fidelity notes + §12.1 report.

Each slice: full `cargo test -p covalence-init` + `-p covalence-lisp
--features hol` + fmt + deps gate; adversarial audit before commit.
