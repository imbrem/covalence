# ACL2 generic premise builder — the object-level simplifier + IH splicer

*(AI-generated design note, 2026-07-17. Fills the single highest-value
follow-up named in [`acl2-book-frontend.md`](./acl2-book-frontend.md) §5 and
the `crates/kernel/hol/init/src/init/acl2/SKELETONS.md` severe entry
"`lang/lisp` is not on the S6 kernel path". Companions:
[`acl2-s4-s6-design.md`](./acl2-s4-s6-design.md) (IND + the Hilbert
compiler), [`acl2-s5-design.md`](./acl2-s5-design.md) (§3 env rows, §7–§9
IND-ORD + `transport_implies_open`, §8 axiom pack — the S5c/S5d agent's
in-flight scope, which phases P1/P2 below consume),
[`acl2-s7-s12-plan.md`](./acl2-s7-s12-plan.md) (S7/S11 context),
[`acl2-fidelity.md`](./acl2-fidelity.md).)*

## 0. Problem + decision summary

The S6 gate proves `app-assoc` end-to-end
(`hilbert.rs::t_app_assoc_gate`), but its base/step premises are ~150
hand-built `hilbert::Step`s (`app_assoc_base` / `app_assoc_step` /
`app_cons_lemma` / `app_unfold_at` + the test-local `B` builder). Surface
`defthm`s with free variables are therefore honestly rejected
("needs induction") by `crates/lang/lisp` and the `#book` pipeline. This
note designs the **generic premise builder**: goal + induction variable →
the exact base/step premise theorems the IND (and later IND-ORD) clause
consumes, produced by an object-level, derivation-emitting simplifier.

Decisions, made here so implementation has none left:

1. **Plan-then-emit, two phases.** The simplifier first builds an
   *untrusted syntactic rewrite plan* (pure Rust, no kernel calls, budget-
   bounded), then *emits* kernel derivations for exactly the plan nodes
   used. Every emitted step is a committed constructor
   (`axiom_inst`/`def_inst`/`cong_impl`/`mp`/`eq_trans`/`derive_under`
   etc.) — the kernel re-checks everything; a wrong plan errors, it never
   mints. This kills two birds: speculative unfolds cost nothing when
   rolled back, and no unused `Fact` lines ride the quadratic
   deduction-compiler discharge.
2. **Guard-resolution discipline for unfolding.** A user-row `Def` unfold
   is *committed* only if the unfolded body's governing `IF` guard
   resolves (by a context hypothesis, a value fact like `consp-cons`, or
   ground computation) or the unfolded form enables a hypothesis/IH
   rewrite. Otherwise the unfold is rolled back. This is the termination
   argument (§5.4) and reproduces the hand scripts' shape exactly (§12).
3. **No congruence into `IF`.** `IF` is a special form (not a table row —
   no `CongImpl(IF)`); the builder never rewrites inside an unresolved
   `IF`. `if-true`/`if-false` are always fired on the guard *as written*,
   with the guard's own (dis)equality obtained via `equal-mp`/`eq_trans`
   from the simplified guard when needed (§5.2 rule R3).
4. **Hyp-free lemmas are `Fact`s, not lines.** Any sub-derivation whose
   proof touches no `Hyp` line is compiled hypothesis-free (direct
   `mp`/`eq_trans` on `Fact`s, the `app_cons_lemma` pattern) and enters
   the under-hypothesis script as a single `Step::Fact`. This bounds the
   discharge blowup (§10).
5. **Phasing.** P0 = structural IND premises, app-assoc automated,
   kernel-side only — depends on **nothing in flight**. P1 = the
   arithmetic slice (len2-app) + lang/lisp + book wiring — depends on the
   S5c pack (`cases`/`equal-mp`/`truth` + `ModelImplies` +
   `transport_implies_open`) plus two new arithmetic rows (§8). P2 =
   IND-ORD premise shapes — depends on S5d (`derive_ind_ord`).
6. **Home**: new module `crates/kernel/hol/init/src/init/acl2/simplify.rs`
   (registered in `mod.rs`); the test-local `B` builder is promoted into
   `hilbert.rs` as `pub struct Script` (§4). Lang-side wiring lives in
   `crates/lang/lisp/src/acl2.rs` as `IndEngine` next to `CertEngine`
   (§9). No TCB surface anywhere; everything is untrusted userspace over
   the committed constructors.
7. **Honesty**: the builder *never* asserts; failures are structured
   `IndFailure` values naming the candidate variable, the failed premise,
   and the stuck term pair / undischarged side condition, rendered into
   the surface rejection text (§7.3). Negative controls in every gate.

## 1. The artifact being generalized (what the ~150 steps do)

Reading `hilbert.rs::app_assoc_base`/`app_assoc_step`, the hand proof is
four reusable moves, applied in a fixed discipline:

| move | hand form | generalization |
|---|---|---|
| defun unfold + `IF` fire | `app_unfold_at` (Def instance + `if-true`/`if-false` + MP on the guard hyp + `eq_trans`) | §5.2 R2+R3 |
| congruence chaining | `cong_impl("APP", …)` + MP per argument (+ `eq_refl` for unchanged args) | §5.2 R1 |
| hyp-free composite lemma | `app_cons_lemma` (Def + `consp-cons` + `if-true` + `car-cons`/`cdr-cons` + `CongImpl`, all `Fact`-level) | decision 4; falls out of the plan/emit split |
| IH splice | `Hyp(2)` + `CongImpl(CONS)` rewrite of the tail | §5.2 R4 (hypothesis rewrites) |

and the goal is closed by simplifying both sides to a syntactic common
form and joining with `equal-symm`/`equal-trans` (`trans_u`/`symm_u`).
The builder is exactly this: a both-sides normalizer over those move
classes, with the IH formulas computed in `derive_ind`'s own shapes.

## 2. Architecture

```text
                       crates/lang/lisp (P1)
  defthm goal ──► IndEngine (surface→deep encode, shadow Acl2Session)
                       │ encoded φ, candidates
                       ▼
        init/acl2/simplify.rs  prove_by_induction (§7)
          │ per candidate v:
          │   ih shapes (§6.1) ─► base/step contexts
          │   Planner (§5): rewrite plans for both sides + join
          │   Emitter (§4): plans → Script steps/Facts → derive_under
          ▼
        base : ⊢ D ⌜(IMPLIES (EQUAL (CONSP v) 'NIL) φ)⌝
        step : ⊢ D ⌜(IMPLIES (CONSP v) (IMPLIES ihcar (IMPLIES ihcdr φ)))⌝
          │ derive_ind (committed)          ──► ⊢ D ⌜φ⌝
          │ Acl2Session::project (committed) ──► ⊢ ∀σ. ¬(eval ⌜φ⌝ σ = anil)
          ▼ transport_equal_open / transport_implies_open (committed)
        the closed base-HOL model theorem
```

Layers, bottom-up:

- **Script** (§4): the promoted `B` builder — hypothesis list, step list,
  per-line formulas, plus a `Fact` cache. Owns all emission.
- **Matcher + rule table** (§5.1–5.2): first-order matching over encoded
  pseudo-terms; rewrite-rule sources = env axioms (oriented), Def
  unfolding, `IF` firing, hypothesis/IH rules, computation folding.
- **Planner** (§5.3–5.4): innermost-out normalization of a term under a
  context, producing a `Plan` DAG; join procedure for `(EQUAL L R)`
  goals; the holds-prover (§5.5) for holds-form goals and side
  conditions.
- **Premise builder** (§6): IH-shape computation + `derive_under`
  assembly for IND; the IND-ORD variant.
- **Driver** (§7): induction-variable heuristics, candidate loop,
  failure reporting, and the full `prove_by_induction` pipeline.

## 3. Preliminaries pinned from the committed code

Facts the design leans on (verified against the sources; implementers
re-verify at the call sites):

- `mk_implies p q` encodes as `(IF p (IF q 'T 'NIL) 'T)`
  (`hilbert::implies_parts` is its inverse). `IMPLIES`-form goals are
  legal pseudo-terms; `subst_ground` handles them (literal `IF` head).
- `derive_ind(env, φ, v, base, step)` computes the step's IH formulas
  *itself* via `finite_sigma(tm, &[(v, (CAR|CDR v))])` + `subst_ground`
  and rewrites the folds backwards; the builder must state
  `ihcar`/`ihcdr` with **exactly** `subst_ground(tm, φ, s).concl()`'s
  RHS (the `hilbert.rs::app_assoc_terms::ih_at` recipe) or `fire` fails.
- `derive_under(env, hyps, steps, goal)` requires the *last* step to
  prove `goal` and yields
  `⊢ D ⌜(IMPLIES h₁ (… (IMPLIES hₖ goal)))⌝`, hypotheses discharged
  innermost-out. Unused hypotheses are fine (the committed
  weakening test) — the car IH may go unused (list induction as the
  degenerate tree induction).
- `axiom_inst`/`def_inst` fold their INST images through `subst_ground`,
  so all builder-emitted formulas stay in the ground pseudo-term
  fragment: **object variables must be literal symbols** and every head
  a literal symbol ≠ `QUOTE`. The builder never leaves this fragment.
- The 11 primitive rows are `CAR CDR CONS CONSP INTEGERP SYMBOLP EQUAL
  BINARY-+ BINARY-* UNARY-- <`; user rows append. `CongImpl(k)` exists
  for every row in S6 envs.
- S4 template bounds kernel-admissible defuns: consp-guarded
  single-formal depth-1 `(IF (CONSP xr) STEP BASE)`; formals not named
  `b`/`h`/`t`/`sg`, not `__`-prefixed.
- `transport_equal_open(env, projected, binds)` needs `binds` to cover
  the object variables exactly once each; `object_vars(tm, enc)` gives
  them in first-occurrence order — the driver computes `binds`
  automatically (§7.2), lowercasing names for the HOL frees.

## 4. The Script layer (promote `B`; the emission surface)

Move the test-local `B` into `hilbert.rs` as:

```rust
/// A step-list builder tracking line formulas (the object-proof tape).
pub struct Script<'e> {
    env: &'e Acl2Env,
    hyps: Vec<Term>,           // fixed at construction (premise shape)
    steps: Vec<Step>,
    phis: Vec<Term>,           // line formulas, parallel to steps
    cache: FactCache,          // §10 — shared per engine, by &mut/&RefCell
}

impl<'e> Script<'e> {
    pub fn new(env: &'e Acl2Env, hyps: &[Term], cache: …) -> Self;
    pub fn hyp(&mut self, i: usize) -> Result<usize>;        // phi from self.hyps[i]
    pub fn fact(&mut self, f: Fact) -> usize;
    pub fn mp(&mut self, j: usize, k: usize) -> Result<usize>;
    pub fn trans(&mut self, jab: usize, jbc: usize) -> Result<usize>; // trans_u
    pub fn symm(&mut self, jab: usize) -> Result<usize>;             // symm_u
    pub fn close(self, goal: &Term) -> Result<Thm>;   // derive_under(env, hyps, steps, goal)
}
```

`trans`/`symm` are the committed `trans_u`/`symm_u` verbatim (compute
`equal-trans`/`equal-symm` instances from the tracked `phis`, push
`Fact` + `Mp`s). `hyp`/`mp` re-check shapes eagerly (`implies_parts`)
so plan bugs surface at emission with line context, not inside
`derive_under`.

Alongside, in `simplify.rs`, `Fact`-level combinators that mirror the
under-hypothesis ones but stay hypothesis-free (for decision-4 lemmas):
these already exist as `hilbert::mp`/`eq_trans`/`eq_symm`/`eq_refl` on
`Fact`s — reuse them unchanged.

## 5. The simplifier

### 5.1 The matcher (untrusted, syntactic)

First-order matching over encoded pseudo-terms.
`match_enc(pat, t, σ) -> Option<σ>`:

- `pat = asym ⌜V⌝` (a literal object variable): bind `V ↦ t` (must agree
  with any existing binding; **σ maps names to arbitrary encoded terms**).
- `pat = anil` / `aint ⌜i⌝` / `(QUOTE v)`: exact term equality with `t`.
- `pat = (F p₁ … pₙ)` (literal-symbol head, incl. `IF`): `t` must be an
  application with the same head and arity; match args pointwise.
- anything else: no match.

Axiom encodings double as patterns (their object variables are the
pattern variables) — no separate pattern language. Matching is Rust-only
and unverified: the emitted `axiom_inst(name, σ)` + `mp` chain is what
the kernel checks.

### 5.2 Rule sources (the complete list; nothing else fires)

Given a context `Γ` (the premise's hypothesis list, as terms with their
`Hyp` indices), the planner rewrites with, in priority order at each
position:

- **R4 — hypothesis/IH rewrite.** For each `Γᵢ` of shape
  `(EQUAL l r)`: rewrite instances *syntactically equal to `l`* to `r`
  (left-to-right only, no matching-with-variables — hypotheses are
  ground in the object sense; this is exactly IH use). Emission:
  `Hyp(i)` (+ congruence steps from R1 to position it).
- **R2 — Def unfold.** `t = (F a⃗)`, `F` a user row `j`: candidate
  rewrite to `body[formals ↦ a⃗]` (computed syntactically; emission =
  `def_inst(env, F, binds)`, whose `subst_ground` fold produces the same
  term — assert equality at emission). Committed only under the §0.2
  discipline, checked in the plan: after unfolding, the body's leading
  `IF` guard must resolve by R3, or an R4 rule must fire inside the
  unfolded form within the remaining budget; else roll back.
- **R3 — `IF` resolution.** `t = (IF c y z)`:
  1. Plan-simplify `c → c*` (proof `e_c : (EQUAL c c*)` if changed).
  2. **False**: if `c* = 'NIL`, or some `Γᵢ = (EQUAL c* 'NIL)`, or the
     holds-prover (§5.5) refutes… — no: *only* the two syntactic cases
     (plus ground computation making `c*` `'NIL`-quoted). Emission:
     `if-false` at `(X↦c, Y↦y, Z↦z)`, MP'd with `(EQUAL c 'NIL)` built
     as `e_c` trans `(EQUAL c* 'NIL)` (the latter a `Hyp` or
     `eq_refl`-degenerate). Result `(EQUAL t z)`; continue with `z`.
  3. **True**: if `c*` is `'T`/`(QUOTE v)` with `v ≠ anil`-decidable
     (quoted non-nil value), or some `Γᵢ = c*` (holds-form hypothesis,
     e.g. the step's `(CONSP X)`), or the holds-prover proves `c*`
     within budget (§5.5 — this is how `consp-cons` fires on
     `(CONSP (CONS h d))`). Emission: `if-true` at `(X↦c, Y↦y, Z↦z)`
     MP'd with `c` holds, where `c` holds is transported from `c*` holds
     across `e_c` by `equal-mp` (P1; in P0, `c* = c` always — see the
     note below). Result `(EQUAL t y)`.
  4. Neither: the `IF` is **stuck**; `t` is in normal form (record the
     guard as a stuck point for failure reporting).

  *P0 restriction:* without the S5c `equal-mp` row, case 3's transport
  across `e_c` is unavailable; P0 fires `if-true`/`if-false` only when
  the guard resolves **as written** (`c* = c`), which suffices for the
  whole structural fragment (guards are `(CONSP v)` / `(CONSP (CONS h d))`
  / `(CONSP (CDR v))`-shaped, matched directly by hyps or `consp-cons`).
- **R1 — congruence descent.** `t = (F a⃗)`, `F` any table row: simplify
  each `aᵢ → aᵢ*`; if any changed, emission =
  `cong_impl(env, F, pairs)` MP'd per argument (changed → the argument's
  proof line/Fact; unchanged → `eq_refl`). Then retry R2–R5 on
  `(F a⃗*)`. (`IF` is *not* a row: R1 never descends into `IF` branches
  — only R3 handles `IF`, and only via its guard.)
- **R5 — computation fold.** `t = (F v⃗)` with every `vᵢ` a carrier
  value (the `defun::is_value` test on the *encodings*' quoted
  payloads): fire `Comp(k)` folded by a model law —
  `comp_fact(env, k, vals) -> Result<Option<Fact>>`, a `simplify.rs`
  helper generalizing `CertEngine::comp_cert` to arbitrary envs: prim
  heads via the same `Prims` law dispatch (`car_cons`/`cdr_cons`/
  `car_nil`/`consp_*`/`equal_refl`/`equal_ne`+`int_ne`/`plus_lit`,
  extended by `lt_lit` post-S5), user heads via
  `defun_ground`/`fold_ground` (extend `fold_ground`'s head set on
  demand — the recorded SKELETONS seam). `None` = no law → not a
  rewrite (fail-safe, mirrors `comp_cert`).
- **R6 — oriented axiom rewrite.** For each env axiom registered in
  the builder's `RwTable` with an orientation: match the axiom's
  conclusion-LHS pattern against `t`; on match σ, side conditions
  (the axiom's `IMPLIES` antecedents at σ) go to the holds-prover
  (§5.5) with a **strictly smaller budget**; emission =
  `axiom_inst(name, σ)` + MP per discharged antecedent, yielding the
  `(EQUAL tσ rhsσ)` fact. Only axioms *explicitly listed* in the
  `RwTable` fire this way (the five ground schemas, `prop-k/s`,
  `cases`, `equal-mp`, `contra`, `truth` are **never** rewrite rules).
  **P0 table**: `car-cons` (`(CAR (CONS A B)) → A`) and `cdr-cons`
  (`(CDR (CONS A B)) → B`), both unconditional — exactly the hand
  proof's uses. **P1 adds** §8's two arithmetic rows.

### 5.3 The planner: `norm(t, Γ, budget) -> (t*, Plan)`

Innermost-out, one pass with retry-on-change:

```text
norm(t):
  if t is a variable / value / quote: return t (nf)
  if t = (IF c y z): apply R3; if resolved to branch b, return norm(b)
                     else return t with c* recorded stuck   [no descent]
  if t = (F a⃗):
    a⃗* := map norm a⃗                                        [R1]
    loop (bounded by budget.head_steps):
      if R4 fires on (F a⃗*): rewrite, re-norm the result, continue
      if R5 fires: rewrite to the value, return it (values are nf)
      if R6 fires (P1): rewrite, re-norm, continue
      if F is a user row and R2's discipline admits: unfold, norm the
        body instance (this consumes one unit of budget.unfolds for
        this position), continue with the result
      break
    return current term
```

`Plan` is a DAG of nodes `{Refl, Cong{row, kids}, Def{j, binds},
IfTrue/IfFalse{guard-just}, HypRw{i}, Comp{k, vals}, AxRw{name, σ,
conds}, Trans[..]}` — each node knows its `(EQUAL from to)` and whether
its justification subtree touches any `Hyp` (the **hyp-tainted** bit,
computed bottom-up; untainted subtrees are emitted as `Fact`s, decision
4).

### 5.4 Termination + budgets

`Limits { unfolds_per_position: 1 (default), head_steps: 8,
plan_nodes: 2_000, holds_depth: 3 }`. Termination argument: R4/R6 fire
only on syntactic matches and each iteration either strictly reduces by
the head-steps counter or produces a value (R5); R2 is bounded by
`unfolds_per_position` (an unfold whose guard doesn't resolve is rolled
back, so committed unfolds always make `IF` progress via R3, and R3
strictly descends into a branch). No rule re-introduces a committed
unfold at the same position (positions are tracked by the plan node,
not by term paths — the DAG hash-consing makes revisits cache hits).
Budget exhaustion = a stuck report, never a wrong answer.

### 5.5 The holds-prover: `holds(φ, Γ, budget) -> Plan` (goal `D ⌜φ⌝`-shaped, under Γ)

Used for R3-true guards, R6 side conditions, and holds-form defthm goals
(P1). In order:

1. `Γᵢ = φ` → `Hyp(i)`.
2. `φ = (CONSP (CONS a b))` → `consp-cons` INST (P0's only holds axiom).
3. `φ = 'T` → `truth` (P1).
4. `norm(φ, Γ)` → `φ*`; if `φ* = (QUOTE v)`, `v ≠ anil` decidable →
   value-holds: from `(EQUAL φ 'v)` by `equal-mp` transport off `truth`…
   — precisely: `e : (EQUAL φ φ*)`; `φ*` holds by rule 2/3/ground
   (`(EQUAL x x)`-shaped `φ*` closes by `equal-refl`); then
   `equal-mp` INST`(P↦φ*, Q↦φ)` MP'd with `symm(e)` and `φ*`-holds.
   (P1 only — P0 never needs it.)
5. **Cases split** (P1, `budget.holds_depth > 0`): pick the leftmost
   stuck `IF` guard `q` recorded by `norm`. **Try `Γ = ∅` first** (side
   conditions usually don't need the outer hypotheses — cacheable,
   hyp-free): build `b₁ = D ⌜(IMPLIES q φ)⌝` and
   `b₂ = D ⌜(IMPLIES (EQUAL q 'NIL) φ)⌝` as two fresh `derive_under`
   sub-scripts at `hyps = [q]` / `[(EQUAL q 'NIL)]` (depth − 1), then
   `cases` INST`(Q↦q, P↦φ)` + MP + MP — a hyp-free `Fact`. If `φ`
   genuinely needs `Γ`: the sub-scripts run at `hyps = Γ ++ [q]` (resp.
   `[(EQUAL q 'NIL)]`), concluding `D ⌜(IMPLIES γ₁ (… (IMPLIES q φ)))⌝`;
   in the **outer** script, push that as a `Fact` line and strip the
   `Γ`-prefix by `Mp` against the outer `Hyp` lines (object-level MP —
   legal since the nested implication is the `Fact`'s formula), landing
   the `(IMPLIES q φ)` line for the `cases` composition.
6. Else: stuck report.

### 5.6 Goal closure: `close_equal(goal, Γ)`

For `goal = (EQUAL L R)`: `L* := norm(L, Γ)`, `R* := norm(R, Γ)`.
If `L* == R*` syntactically: emit L's chain, emit R's chain, join —
`trans(L-chain, symm(R-chain))` (degenerate cases: only one side
changed → single `trans`/`symm`; neither changed → `eq_refl` requires
`L == R`). The final line's formula is asserted `== goal` before
`Script::close` (the committed `assert_eq!(b.phis[l_phi], t.phi)`
becomes a checked error). If `L* != R*`: stuck report carrying both
normal forms. For holds-form goals (P1): §5.5 directly.

## 6. Premise assembly

### 6.1 IND shapes (P0) — `build_ind_premises(env, cache, φ, v) -> Result<IndPremises>`

Exactly `derive_ind`'s expectations:

```text
g     := (EQUAL (CONSP v) 'NIL)                    [ind_encs' base guard]
c     := (CONSP v)
ihcar := subst_ground(tm, φ, finite_sigma[(v, (CAR v))]).concl().rhs
ihcdr := ditto at (CDR v)
base  := Script(env, [g]);            close_equal(φ, {g:0});          close(φ)
step  := Script(env, [c, ihcar, ihcdr]); close_equal(φ, {c:0, ihcar:1, ihcdr:2}); close(φ)
```

yielding `base : ⊢ D ⌜(IMPLIES g φ)⌝` and
`step : ⊢ D ⌜(IMPLIES c (IMPLIES ihcar (IMPLIES ihcdr φ)))⌝` — the
literal premise statements of `derive_ind` (asserted by construction;
`derive_ind` re-checks). IHs enter the context as R4 rules whether or
not they fire (unused-hyp weakening is committed behavior). `φ` must be
in the ground pseudo-term fragment over literal object variables — the
encoder guarantees it (§9.1); assert early with a clean error.

For `IMPLIES`-form goals `φ = (IMPLIES h₁ (… c))` (P1): peel the
antecedents syntactically (`implies_parts`), push them onto **both**
premise contexts *after* the IND-specific hypotheses, prove the bare
conclusion, and let `derive_under` re-fold them — i.e. `hyps = [g, h₁…hₙ]`
/ `[c, ihcar', ihcdr', h₁…hₙ]` with goal `c`… **No.** That changes the
premise statement (`(IMPLIES g (IMPLIES h₁ … c))` ≠ `(IMPLIES g φ)`
only by association — they are the *same* encoded term, since
`φ = (IMPLIES h₁ (… c))` and `derive_under` nests right). Pin it: with
`hyps = [g] ++ [h₁…hₙ]` and goal `c`, `derive_under` yields exactly
`⊢ D ⌜(IMPLIES g (IMPLIES h₁ (… (IMPLIES hₙ c))))⌝ = ⊢ D ⌜(IMPLIES g φ)⌝`
— the required base premise, verbatim. Same for the step with
`hyps = [cg, ihcar, ihcdr, h₁…hₙ]`. The IHs are the *full* `φ`-instances
(implications), usable via R4 only after their own antecedent instances
are discharged — the planner treats an implication-shaped hypothesis as
a **conditional R4 rule**: match its conclusion's `EQUAL`-LHS; side
conditions = its antecedents, to the holds-prover; emission = `Hyp(i)`
+ MPs. (Deferred to P1; P0 rejects `IMPLIES` goals with an honest
message — the fixture's open goals are both bare `EQUAL`s.)

### 6.2 IND-ORD shapes (P2; coordinates with `acl2-s5-design.md` §7)

`build_ind_ord_premises(env, cache, φ, v, m, q, ts) -> Result<IndOrdPremises>`
produces, for the §7.2 clause at shape `k = ts.len()`:

- `d_op : ⊢ D ⌜(O-P m)⌝` — holds-prover under `Γ = ∅` (for
  `m = (ACL2-COUNT v)` this is the §11 №15 script; the builder routes it
  through §5.5's cases machinery — if it walls, the caller may supply
  `d_op` explicitly: the API takes `ObligationSource::Auto | Given(Thm)`).
- `d_decᵢ : ⊢ D ⌜(IMPLIES q (O< φᵢᵐ m))⌝` with
  `φᵢᵐ = subst_ground(tm, m, finite_sigma[(v, tᵢ)]).concl().rhs` —
  Script at `hyps = [q]`, holds-prover goal.
- `d_base : ⊢ D ⌜(IMPLIES (EQUAL q 'NIL) φ)⌝` — Script at
  `hyps = [(EQUAL q 'NIL)]`, `close_equal(φ)`.
- `d_step : ⊢ D ⌜(IMPLIES q (IMPLIES φ₁ (… (IMPLIES φ_k φ))))⌝` with
  `φᵢ = subst_ground(tm, φ, finite_sigma[(v, tᵢ)]).concl().rhs` —
  Script at `hyps = [q, φ₁…φ_k]`.

then `derive_ind_ord(env, k, φ, v, m, q, ts, d_op, d_decs, d_base,
d_step)` (S5d's constructor — it re-folds via `subst_ground` exactly as
`derive_ind` does; the builder's reduced statements are the ones it
expects). Defaults for the structural-measure route
(`m = (ACL2-COUNT v)`, `q = (CONSP v)`, `ts = [(CDR v)]`): the driver
offers `IndScheme::Structural | Measured { m, q, ts }`; P2's gate re-runs
app-assoc through `Measured` with the S5 §11 №16 parameters and asserts
agreement with the P0 result (instantiated, β-reduced — the committed
cross-check pattern).

## 7. The driver

### 7.1 Candidate variables + ranking

`candidates(env, φ) -> Vec<Vec<u8>>`: the object variables of `φ`
(`object_vars`), ranked by **recursion votes**: walk `φ`; each
application `(F a⃗)` with `F` a user row having `rec_formal = Some(r)`
and `a_r = asym ⌜V⌝` casts one vote for `V` (nested applications all
vote). Sort by votes descending, ties by first occurrence. Variables
with zero votes stay in the list (last) — induction on them is legal,
just unlikely to close. Rationale check against the gates: app-assoc →
`X`:2 (`(APP X Y)`, `(APP X …)`), `Y`:1, `Z`:0 → `X` first ✓; len2-app
→ `X`:2 (`(APP X Y)`, `(LEN2 X)`), `Y`:1 → `X` ✓.

### 7.2 `prove_by_induction`

```rust
pub struct IndConfig { pub limits: Limits, pub scheme: IndScheme,
                       pub var: Option<Vec<u8>> /* force a candidate */ }
pub struct IndProof {
    pub var: Vec<u8>,
    pub derivation: Thm,   // ⊢ D ⌜φ⌝
    pub projected: Thm,    // ⊢ ∀σ. ¬(eval ⌜φ⌝ σ = anil)
    pub transported: Thm,  // the closed base-HOL theorem
}
pub fn prove_by_induction(sess: &Acl2Session, cache: &FactCache,
                          phi: &Term, cfg: &IndConfig)
    -> Result<IndProof, IndFailure>
```

Per candidate (or the forced one): try §5.6 with `Γ = ∅` **first**
(simplifier-only, no induction — closes goals that need only unfolding
/ computation / R6 rules); then build premises (§6), `derive_ind`,
`sess.project`, then transport: `EQUAL`-headed φ →
`transport_equal_open` with `binds` = `object_vars(tm, φ)` mapped to
their ASCII-lowercase HOL names (collision → error);
`IMPLIES`-headed → `transport_implies_open` (P1). Closed φ (no object
vars) → the committed ground `transport_equal`. First candidate that
closes wins; every failure is recorded.

### 7.3 Failure reporting (the honest rejection text)

```rust
pub struct IndFailure { pub attempts: Vec<Attempt> }
pub struct Attempt { pub var: Vec<u8>, pub premise: PremiseId,  // Base | Step | Obligation(i) | NoInduction
                     pub stuck: Stuck }
pub enum Stuck {
    Join { lhs_nf: Term, rhs_nf: Term },        // both sides' normal forms differ
    Guard { guard: Term },                       // unresolved IF guard
    SideCondition { axiom: SmolStr, cond: Term },// R6 condition the holds-prover missed
    Budget { what: &'static str },
    OutOfFragment { term: Term, why: String },
}
```

Rendered (lang-side) as e.g. `defthm len2-app rejected: induction on X:
base premise stuck: sides normalize to (LEN2 Y) vs (BINARY-+ '0 (LEN2
Y)) — no rule closes the gap; also tried Y (step premise stuck: …)`.
Nothing is stored on failure; the tally records the rejection with this
reason. **The old rejection text ("needs induction, not implemented")
is replaced only when the new path is wired; a failed new path must
still name itself** — the honesty bar is that the message describes
what was actually attempted.

## 8. Env additions (P1) — the arithmetic rewrite rows

The len2-app gate needs, beyond the S5c pack
(`cases`/`equal-mp`/`truth`/`contra`, `ModelImplies`,
`transport_implies_open`, `integerp-plus` — all in the in-flight S5c/S5d
scope), exactly **two new axiom rows**, added by a
`with_arith_rules(env) -> Result<Acl2Env>` builder in `simplify.rs`
(same pre-authorized "±2 rows of the recorded kinds" pattern as S5 §8;
record actual additions in §14):

| row | encoding | discharge | RwTable orientation |
|---|---|---|---|
| `plus-assoc` | `(EQUAL (BINARY-+ (BINARY-+ A B) C) (BINARY-+ A (BINARY-+ B C)))` | `ModelEq(pr.plus_assoc())` — its ∀-order `x,y,z` = first-occurrence order `A,B,C` ✓ | L→R (right-associate), unconditional |
| `plus-zero-int` | `(IMPLIES (INTEGERP A) (EQUAL (BINARY-+ '0 A) A))` | `ModelImplies(thm)` with `thm : ⊢ ∀a. ¬(aintp a = anil) ⟹ aplus (aint 0) a = a` — model proof: intp inversion (`a = aint i`; the S5c `intp_inv` kit) + `plus_eq` unfold + `intval_int` + `int` `add_zero`/`zero_add` | `(BINARY-+ '0 A) → A`, condition `(INTEGERP A)` |

RwTable entries carry `{ axiom name, lhs pattern (the conclusion's
`EQUAL`-LHS), conds (antecedent list), orientation }` — derived
automatically from the row's encoding by `implies_parts`/`equal_parts`
peeling, so the table is data (a list of names + orientations), not
code. `plus-comm` is **not** registered (unoriented AC commutation loops
a naive rewriter); if a later book needs commutativity the design
extension is an AC-normal-form sorter for `BINARY-+` spines (flatten,
sort operands by a canonical term order, reassociate via
`plus-assoc`/`plus-comm` instances) — out of scope, SKELETONS on demand.

## 9. Lang-side + book wiring (P1)

### 9.1 Surface→deep encoding (`IndEngine::encode`)

In `crates/lang/lisp/src/acl2.rs`, next to `CertEngine`:

- **Heads**: `row_spelling` extended over the full table
  (`* ↦ BINARY-*`, unary `- ↦ UNARY--`, `< ↦ <`, `integerp`, `symbolp`)
  plus user defuns (uppercased name must match a shadow-session row).
  `if` → `mk_if`. **Guard normalization**: `(if (endp x) B S)` and
  `(if (atom x) B S)` → `(IF (CONSP X) S B)` (ACL2's
  `endp`/`atom` = `not∘consp` on the S4 template's guard position; the
  swap is recorded per-defun and is a *pre-encoding* rewrite — the deep
  body is the template shape). `zp`/`natp`/`<=`/binary-`-` remain
  outside the deep fragment (reduction fallback) until rows/laws exist.
- **Variables**: surface formals and free goal variables → object
  variables `asym ⌜UPPERCASE⌝`; reject on case collision, on the S4
  reserved names (`b h t sg`, `__*` — surfaced with the S4 restriction's
  message), and on `t`/`nil` (already parameters-invalid).
- **Literals**: numerals → `aint ⌜n⌝` (self-evaluating, per
  `model_image`/`subst_ground`); `(quote d)` → `tm.quote(datum)` with
  `CertEngine::datum`'s exact representation contract (`nil`→`anil`,
  `t`→`pr.t`); bare `t`/`nil` in operand position → `(QUOTE t)`/
  `(QUOTE anil)`.

### 9.2 The shadow session + generations

`IndEngine` holds a kernel-side `Acl2Session` **shadow** of the surface
defun dictionary: on each surface `defun` admission (after the existing
untrusted install), *attempt* `DefunSpec` encoding + template fit; on
success remember the spec (don't admit yet). The shadow session is
materialized **lazily** at the first inductive `defthm`: start from
`s6_env()` (+ `with_arith_rules`), `admit_defun` all remembered specs in
order (one generation each — the committed consuming API; a batched
`install_user_rows` upgrade can come with S5c, not required),
`soundness()` once (cached per generation by `Acl2Session`). A later
surface defun invalidates the shadow (rebuild lazily at next use);
`Session::reset`/`#lang` switch drops it. Surface defuns that don't fit
the S4 template simply aren't shadowed — goals mentioning them fail
`encode` with `OutOfFragment` naming the function.

### 9.3 `defthm` + book flow

`admit_defthm` order becomes: `prove_certified` (unchanged) →
**`prove_inductive`** (new: goal has free variables or is
`EQUAL`/`IMPLIES`-headed over the deep fragment; encode → 
`prove_by_induction` on the shadow session) → `prove_ground` (unchanged
fallback + its honest free-variable rejection, now carrying the rendered
`IndFailure` when the inductive path was attempted). Success stores

```rust
Acl2Proof::Inductive { derivation: Thm /* ⊢ D ⌜φ⌝ */, var: String }
```

with `thm` = the transported closed model theorem
(`hyps().is_empty()` asserted at the boundary, as for `Certificate`).
`book.rs`: the transported check (`EventOutcome::Transported`) extends
its provenance match to `Certificate | Inductive` — no other pipeline
change; the fixture tallies flip (§11.3). Derived open facts
(`⊢ D ⌜φ⌝`) are additionally kept in a per-generation
**lemma store** keyed by name: later goals may use them via R4-style
conditional rules *through INST* (`derive_inst_ground` at the use-site
σ) — this is what lets one book defthm feed the next without env-row
feedback or soundness re-proof (the SKELETONS "defthm-as-new-axiom"
minor stays deferred; the lemma store is strictly within-generation).

## 10. Cost model + caching (fills the SKELETONS "deduction-compiler blowup" minor)

Where the time goes today: every `axiom_inst`/`derive_axiom`/`derive_def`
re-runs `derive_mixed` (a walk of the ~50-clause conjunction) and the
discharge passes of `derive_under` mint O(lines × hyps) fresh
`prop-k`/`prop-s` instances (~40 s for the hand app-assoc premises).
Measures, in order of expected win (measure before adding more):

1. **`FactCache`** (in `simplify.rs`, shared per engine/generation):
   memoize (a) `derive_axiom(name)` and `derive_def(j)` — the raw
   clause firings, one per axiom/row per generation; (b) `axiom_inst`
   by `(name, binds)` and `imp_identity` by `h`; (c) `comp_fact` by
   `(k, vals)`. Keying: kernel `Term` is structurally `Eq`; use a
   `HashMap` if `Term: Hash`, else a `BTreeMap` over a stable render or
   a small `Vec` scan (gate-scale key counts are hundreds — scan is
   fine; leave a comment, measure). Invalidation: the cache is
   per-`Acl2Env` generation (derivations don't transport across
   generations — committed rule), so it lives beside the session and
   drops with it.
2. **Hyp-taint factoring** (decision 4): untainted plan subtrees emit as
   `Fact`s; only tainted lines enter `derive_under`. The discharge cost
   is then O((tainted lines)² × hyps) with tainted lines ≈ the number of
   rewrites that *use* a hypothesis (app-assoc step: ~10, vs ~60 raw
   lines hand-built today).
3. **Single-`Fact` weakening** *(only if 1+2 measure short)*: a `Fact`
   line referenced exactly once could be K-weakened at its unique use
   instead of per discharge pass — recorded option, not designed.
4. Soundness stays the dominant per-generation constant (~20 s at 50
   clauses); unchanged here (cached by `Acl2Session`; `family_soundness`
   remains the recorded escape hatch).

Budget targets (gate assertions are correctness-only; these are
watch-items, not test assertions): automated app-assoc premises ≤ the
hand version's wall time; len2-app end-to-end (excl. soundness) within
2× of app-assoc.

## 11. Acceptance gates (each: `hyps().is_empty()` + exact statements, the shared `check()` style; negative controls mint nothing)

### 11.1 P0 (kernel-side, `simplify.rs` tests over the committed `s6_app_session` pattern)

1. `t_simplify_reproduces_unfold` — `norm((APP X Y), {g})` and
   `norm((APP X Y), {c})` land `Y` / the step form with derivations whose
   emitted conclusions equal the committed `app_unfold_at` lines'.
2. `t_auto_app_assoc_premises` — `build_ind_premises(env, φ, "X")`
   returns base/step with **exactly** the `t_app_assoc_premises`
   statements (`derivable(env, mk_implies(g, φ))` etc.).
3. **`t_auto_app_assoc_gate`** — `prove_by_induction` (candidates
   auto-ranked, no forced var) yields `var == "X"` and a transported
   theorem whose conclusion `==` the committed `t_app_assoc_gate`
   final statement (`⊢ ∀x y z. app (app x y) z = app x (app y z)` over
   the session's `APP` model).
4. Negative controls: (a) the false open goal
   `(EQUAL (APP X Y) X)` → `IndFailure` with a `Join` stuck pair on
   every candidate, nothing stored/minted; (b) forced wrong variable
   `Z` → `Step`-premise failure; (c) budget 0 unfolds → `Budget`; (d) a
   goal containing an unknown head → `OutOfFragment`.

### 11.2 P1 (kernel-side, after S5c lands)

5. `t_integerp_len_cases` — the holds-prover closes
   `D ⌜(INTEGERP (LEN2 Y))⌝` hyp-free via `cases`
   (exact statement; uses the §12.2 trace).
6. **`t_auto_len_app_gate`** — with `LEN2`+`APP` admitted and
   `with_arith_rules`,
   `φ = (EQUAL (LEN2 (APP X Y)) (BINARY-+ (LEN2 X) (LEN2 Y)))`
   transports to
   `⊢ ∀x y. len2 (app x y) = aplus (len2 x) (len2 y)` (exact, model
   constants of this env). Negative control: without the two §8 rows the
   same call fails with `Stuck::Join`/`SideCondition` naming
   `plus-zero-int` — pinning that the rows are load-bearing.

### 11.3 P1 (lang/lisp + book)

7. REPL: `(defthm app-assoc (equal (app (app x y) z) (app x (app y z))))`
   succeeds; `theorem_entry` provenance is `Inductive { var: "X" }`;
   the stored theorem is closed and equals the kernel gate statement.
8. **Book flip**: in `app-basics.lisp`, `app-assoc` and `len2-app` flip
   **rejected → transported** (provenance `Inductive`, closed theorems
   in hand — the required gate). Today's tally is 3 transported
   (`four`/`car-app`/`app-ab-c`) + 2 admitted-by-reduction
   (`rev-rev-ab`/`len2-abc`, whose heads are outside `cert_fragment`);
   with the §7.2 *simplifier-only* path those two ground goals may
   *also* flip to transported (unfold + quoted-value guard resolution +
   R5 computation — requires the P1 `truth`/`equal-mp` rows), making the
   best case `7/7 transported`; **pin whichever the landed slice
   actually achieves, honestly** — the assertion is the exact per-event
   table either way. `mixed.lisp` re-pins accordingly (included
   app-basics rows flip; `consp-implies` flips only if the §6.1
   `IMPLIES`-goal path + `transport_implies_open` wiring land in the
   same slice — else it stays rejected with the new `IndFailure` text;
   `bogus`, `defmacro`, `encapsulate`, `mutual-recursion` stay
   rejected).
9. Negative: a book defthm over a non-template defun (e.g. one using
   `zp`-recursion) stays rejected with an `OutOfFragment` reason naming
   the function — no silent fallback claim.

### 11.4 P2 (after S5d)

10. `t_auto_app_assoc_by_measure` — `IndScheme::Measured` with the S5
    §11 №16 parameters reproduces the P0 result (instantiated,
    β-reduced agreement); obligations built by the §6.2 route (or
    `Given` from the S5d gate's derivations if the auto route walls —
    record which).

## 12. Worked skeletons (the crown traces, at `subst_sema` precision)

### 12.1 app-assoc via the algorithm (must reproduce §1's hand scripts)

`φ = (EQUAL (APP (APP X Y) Z) (APP X (APP Y Z)))`, `v = X`.

**Base**, `Γ = {0: g = (EQUAL (CONSP X) 'NIL)}`:

- `norm(L = (APP (APP X Y) Z))`: R1 descends; `norm((APP X Y))`: args
  nf; R2 unfold `Def(APP)[X↦X, Y↦Y]` (identity binds — `def_inst` with
  `binds = []`) → `(IF (CONSP X) (CONS (CAR X) (APP (CDR X) Y)) Y)`;
  R3: guard `(CONSP X)`, case false via `Γ₀` (`c* = c`) → branch `Y`.
  Commit (guard resolved). Emission ≡ `app_unfold_at(w=Y, base)`. So
  `(APP X Y) → Y` [tainted]. Back at L: R1 congruence
  `cong_impl(APP, [(APP X Y, Y), (Z, Z)])` + MP(line) + MP(`eq_refl Z`)
  → `(APP Y Z)`; R2 on `(APP Y Z)`: unfold guard `(CONSP Y)` — no Γ
  match, no value fact, no R4 enabled → **rollback**. `L* = (APP Y Z)`.
- `norm(R = (APP X (APP Y Z)))`: inner `(APP Y Z)` rolls back as above
  (nf); head R2 unfold `Def(APP)[Y↦(APP Y Z)]` → `IF` fires false via
  `Γ₀` → `(APP Y Z)`. `R* = (APP Y Z)` [tainted].
- Join: `L* == R*` → `trans(L-chain, symm(R-chain))`; final formula
  `== φ`; `close(φ)` → `⊢ D ⌜(IMPLIES g φ)⌝`. ✓ (= `app_assoc_base`,
  minus the hand proof's incidental ordering.)

**Step**, `Γ = {0: c = (CONSP X), 1: ihcar, 2: ihcdr}` with
`ihcdr = (EQUAL (APP (APP (CDR X) Y) Z) (APP (CDR X) (APP Y Z)))`:

- `norm(L)`: `(APP X Y)` → R2+R3-true via `Γ₀` →
  `S_Y = (CONS (CAR X) (APP (CDR X) Y))` (inner `(APP (CDR X) Y)`:
  guard `(CONSP (CDR X))` unresolved, ihcdr's LHS is
  `(APP (APP (CDR X) Y) Z)` ≠ it → nf). L → R1 →
  `(APP S_Y Z)`; R2 unfold `Def(APP)[X↦S_Y, Y↦Z]`: guard
  `(CONSP (CONS (CAR X) (APP (CDR X) Y)))` → holds-prover rule 2
  (`consp-cons` INST — hyp-free Fact) → R3-true → branch
  the branch
  `(CONS (CAR S_Y) (APP (CDR S_Y) Z))`; `norm`: `(CAR S_Y)` — not R5
  (`S_Y`'s args are not values) but **R6 `car-cons`** (the P0 RwTable,
  §5.2): `(CAR S_Y) → (CAR X)`,
  `(CDR S_Y) → (APP (CDR X) Y)`, giving
  `(CONS (CAR X) (APP (APP (CDR X) Y) Z))` after R1; the inner
  `(APP (APP (CDR X) Y) Z)` now **matches ihcdr's LHS** → R4 `Hyp(2)`
  → `(APP (CDR X) (APP Y Z))`. All of the unfold-and-project chain
  except the `Hyp` uses is untainted → emitted as one Fact
  (≡ `app_cons_lemma`). `L* = (CONS (CAR X) (APP (CDR X) (APP Y Z)))`.
- `norm(R)`: R2 unfold at `Y↦(APP Y Z)`, R3-true via `Γ₀` →
  `(CONS (CAR X) (APP (CDR X) (APP Y Z)))`; inner `(APP (CDR X) …)`
  guard unresolved, no R4 match → nf. `R* == L*`. Join → `close(φ)` at
  `hyps = [c, ihcar, ihcdr]` → the exact `t_app_assoc_premises` step
  statement (ihcar unused — weakening ✓).

`derive_ind(env, φ, b"X", base, step)` → project → 
`transport_equal_open(env, projected, [(b"X","x"),(b"Y","y"),(b"Z","z")])`
(binds auto from `object_vars` = X,Y,Z first-occurrence) → the S6 gate
statement. ∎

### 12.2 len2-app (P1) — including the side-condition discharge

`LEN2` (encoded, post guard-normalization):
`(EQUAL (LEN2 X) (IF (CONSP X) (BINARY-+ '1 (LEN2 (CDR X))) '0))`.
`ψ = (EQUAL (LEN2 (APP X Y)) (BINARY-+ (LEN2 X) (LEN2 Y)))`, `v = X`
(votes §7.1). `ihcdr = (EQUAL (LEN2 (APP (CDR X) Y))
(BINARY-+ (LEN2 (CDR X)) (LEN2 Y)))`.

**Base**, `Γ = {0: g}`:
`norm(L)`: `(APP X Y) → Y` (12.1); R1 → `(LEN2 Y)`; R2 unfold: guard
`(CONSP Y)` unresolved → rollback. `L* = (LEN2 Y)`.
`norm(R)`: `(LEN2 X)` → R2+R3-false via `Γ₀` → `'0`; R1 →
`(BINARY-+ '0 (LEN2 Y))`; R6 `plus-zero-int` matches
(`A ↦ (LEN2 Y)`), condition `(INTEGERP (LEN2 Y))` → holds-prover,
`Γ = ∅`, depth 2:

- rule 5 cases on the stuck guard `q = (CONSP Y)` (recorded while
  norm'ing `(LEN2 Y)`):
  - branch `Γ' = {0: (CONSP Y)}`: `(LEN2 Y)` → unfold+R3-true →
    `S = (BINARY-+ '1 (LEN2 (CDR Y)))`, proof
    `e : (EQUAL (LEN2 Y) S)` [tainted by Γ'₀]. Goal
    `(INTEGERP (LEN2 Y))`: holds rule 4 — `norm` gives `e`;
    `(INTEGERP S)` holds by `integerp-plus` INST`(A↦'1,
    B↦(LEN2 (CDR Y)))` (S5c row, unconditional, hyp-free Fact);
    transport: `cong_impl(INTEGERP, [((LEN2 Y), S)])` + MP(e) →
    `(EQUAL (INTEGERP (LEN2 Y)) (INTEGERP S))` → `symm` →
    `equal-mp` INST + MP + MP(`integerp-plus` fact) →
    `(INTEGERP (LEN2 Y))`. `derive_under([(CONSP Y)], …)` →
    `b₁ : ⊢ D ⌜(IMPLIES (CONSP Y) (INTEGERP (LEN2 Y)))⌝`.
  - branch `Γ' = {0: (EQUAL (CONSP Y) 'NIL)}`: `(LEN2 Y)` →
    unfold+R3-false → `'0`; `(INTEGERP '0)` holds: R5
    `comp_fact(INTEGERP, [aint 0])` folded by `intp_int` →
    `(EQUAL (INTEGERP '0) 'T)` Fact; holds rule 4:
    `symm` + `equal-mp` + MP(`truth` Fact) → `(INTEGERP '0)`;
    transport across the unfold equality as in b₁ →
    `b₂ : ⊢ D ⌜(IMPLIES (EQUAL (CONSP Y) 'NIL) (INTEGERP (LEN2 Y)))⌝`.
  - `cases` INST`(Q↦(CONSP Y), P↦(INTEGERP (LEN2 Y)))` + MP(b₁) +
    MP(b₂) → the hyp-free side-condition Fact (this is gate №5).

R6 emits `plus-zero-int` INST`(A↦(LEN2 Y))` + MP(side Fact) →
`(EQUAL (BINARY-+ '0 (LEN2 Y)) (LEN2 Y))` → `R* = (LEN2 Y) = L*`.
Join → base premise. ✓

**Step**, `Γ = {0: c, 1: ihcar, 2: ihcdr}`:
`norm(L)`: `(APP X Y)` → `S_Y` (12.1); `(LEN2 S_Y)` → R2 unfold at
`X↦S_Y`: guard `(CONSP S_Y)` → `consp-cons` → R3-true →
`(BINARY-+ '1 (LEN2 (CDR S_Y)))` → `cdr-cons` (RwTable) + R1 →
`(BINARY-+ '1 (LEN2 (APP (CDR X) Y)))` → R4 ihcdr on the inner
`(LEN2 (APP (CDR X) Y))` → 
`L* = (BINARY-+ '1 (BINARY-+ (LEN2 (CDR X)) (LEN2 Y)))`.
`norm(R)`: `(LEN2 X)` → unfold+R3-true via `Γ₀` →
`(BINARY-+ '1 (LEN2 (CDR X)))` (inner guard unresolved → nf); R1 →
`(BINARY-+ (BINARY-+ '1 (LEN2 (CDR X))) (LEN2 Y))` → R6 `plus-assoc`
(unconditional) → `(BINARY-+ '1 (BINARY-+ (LEN2 (CDR X)) (LEN2 Y)))`
`= L*`. Join → step premise. ✓ Then `derive_ind` /
`project` / `transport_equal_open([(X,"x"),(Y,"y")])` → gate №6. ∎

## 13. Risk register

| risk | mitigation |
|---|---|
| planner/emitter drift (plan claims a rewrite the emitter can't derive) | every emission re-checks the plan node's `(from, to)` against the derived Fact's `equal_parts`; mismatch = clean error naming the node; gates 1–2 pin the two known-good traces |
| rollback discipline misses a needed unfold (goal closable only by unfolding an unresolved-guard call) | recorded limitation: such goals report `Stuck::Join` with both nfs — the honest text names the folded call; `unfolds_per_position`/case-split growth is a P2+ extension, not silently attempted |
| R6 loops (a rule rewrites into another's redex cyclically) | P0/P1 tables are tiny and hand-audited (car-cons/cdr-cons/plus-assoc/plus-zero-int — jointly terminating: each strictly reduces IF-count, term size, or `+`-left-depth); table additions must state their measure in the row comment; `head_steps` is the hard stop |
| `derive_under` blowup at book scale despite §10.1–.2 | measure at gate 3/6; §10.3 as the recorded next lever; worst case: the builder still lands, slower — no correctness exposure |
| S5c slippage blocks P1 | P0 is fully independent (no pack rows used — §5.2's P0 restriction + P0 RwTable); land P0 + SKELETONS the P1 gates |
| shadow-session generation churn in books (defthm between defuns → soundness re-proofs) | lazy materialization (§9.2) makes the common prefix (all defuns first — both fixtures) a single generation; worst case is per-generation soundness, the committed cost model; batch `install_user_rows` (S5c seam) is the recorded upgrade |
| surface/deep encoding mismatch (a surface defthm proved about a *different* deep function than the surface one evaluates) | the shadow spec is encoded from the *same* surface AST as the untrusted install, via total syntactic translation; the stored theorem is about the kernel model constants and says so (provenance `Inductive`); the S4/S6 cross-check (direct-vs-transported) already pins model agreement for APP — add the analogous check for LEN2 in gate 6 if cheap, else record |
| `Term` lacks `Hash` making `FactCache` awkward | fallback keying is specified (§10.1) — no design dependency |

## 14. Out of scope (SKELETONS entries on landing) + implementation report

Out of scope, recorded as SKELETONS entries when P0 lands (in
`init/acl2/SKELETONS.md` unless noted):

- `IMPLIES`-form goals + conditional-IH discharge (§6.1's P1 paragraph)
  until `transport_implies_open` lands; `consp-implies` in the fixture
  stays rejected until then.
- AC normalization for `BINARY-+` (`plus-comm` unregistered, §8);
  `BINARY-*`/`UNARY--`/`<` R6 rules (no rows/laws yet).
- Multi-variable / simultaneous induction; nested-induction lemma
  *synthesis* (the lemma store (§9.3) only reuses what a book states).
- Generalization / cross-fertilization (ACL2's waterfall heuristics) —
  the builder is a simplifier + one induction, deliberately.
- `zp`-recursion and other non-CONSP guards (S7's measured tier; the
  builder's IND-ORD shapes are ready for it, §6.2).
- lang/lisp `:hints (:induct …)` — surface hints parse-recorded today;
  wiring `cfg.var`/`cfg.scheme` from them is a P1 nicety, do last.

**Implementation reports** (append here, per the running discipline —
deviations, actual row lists, cache-win measurements, gate timings):

*(none yet)*
