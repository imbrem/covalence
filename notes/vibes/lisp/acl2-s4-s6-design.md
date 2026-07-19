+++
id = "N001O"
status = "draft"
review = "unreviewed"

[[contributions]]
role = "author"
actor = "agent:claude"
at = "2026-07-16T04:51:47+01:00"
source = "legacy"
agent = "claude"
harness = "claude"
+++

# ACL2 S4 + S6-structural: concrete design (defun, induction, open transport)

*Design for stages S4 (definitional principle, conservative tier) and
S6-structural (induction rule) of [`acl2-full-plan.md`](./acl2-full-plan.md),
continuing [`acl2-s0-s3-design.md`](./acl2-s0-s3-design.md) (whose §10 is its
order-of-work, hence the sibling note). Agent-authored (vibes). Verified
against the committed S0–S3 code (`crates/kernel/hol/init/src/init/acl2/`,
branch `lisp-demo`, 2026-07-16), including the §9.5 implementation reports.
Everything below stays in userspace over existing kernel rules — no new
axioms, no TCB edits; every "axiom" named here is an env *clause* whose
soundness is discharged by a proved model theorem.*

## 0. Corrections/deviations (to the plan and the S3 design, verified)

1. **The propositional calculus lands at S6, not S3.** The plan's S3 said
   "propositional calculus (if-form)", but the committed `ground_env()` has
   only the five equality/if schemas. That is enough for the ground gates but
   **not** for using an induction clause: deriving the step premise
   `(IMPLIES … φ)` requires reasoning *under object hypotheses*, i.e. a
   Hilbert basis (`prop-k`, `prop-s`) plus **implication-form congruence**
   and the **structural axiom pack** (`car-cons`, `cdr-cons`, `consp-cons`).
   All are S6 env additions (§7) with semantic discharges.
2. **S6 needs no `eval_ext` induction lemma.** The valuation-identification
   steps in the induction discharge close with the existing
   `init/cat.rs::fun_ext` (abs + `Thm::eta_conv`) over a pointwise proof —
   function extensionality is already derivable (cat.rs:101). The
   carrier-induction `eval_ext` mirror of `subst_sema` is only the recorded
   fallback (§9.1).
3. **`eval_open`'s variable case is literal-only** (`sym_lit_of` gates on a
   blob literal, derivable.rs:540). The S6 discharge evaluates encodings
   containing `asym v` at a *free* `v : bytes`; the var case must generalize
   to any `asym`-headed term (the `eval_var` law is already ∀-quantified).
   Benign for all committed callers (§7.1).
4. **`eval_open`/`evlis_open` and the S2 dispatch read `tm.pr.table()`**
   (derivable.rs:574, term.rs). S4's user functions must enter that table, so
   the row source becomes the env's row vector (§1). This is the one place
   the committed code hard-wires "primitives only".
5. **`Acl2Env.axioms: Vec<(SmolStr, Term)>` cannot carry S4 discharges** —
   exactly the SKELETONS "S4+ axiom-discharge gap". It becomes
   `Vec<AxiomRow>` with a `Discharge` field (§2.2); `t_axioms_derive`'s
   iteration is the only committed consumer to touch (mechanical).
6. **Kernel-side S4 admissibility is deliberately *stricter* than
   `lang/lisp/acl2.rs`'s syntactic check** (which allows arbitrary-depth
   `car`/`cdr` chains, any call position). The kernel tier accepts the
   consp-guarded single-formal depth-1 template (§4); everything else errors,
   nothing minted. Deeper descent/multiple measures are S7.
7. **The S6 induction clause carries BOTH the car and the cdr IH**
   (tree induction; list induction is the special case of not using the car
   conjunct). Rationale in §8. Premises are *curried* `IMPLIES` chains — no
   `AND` macro enters the clause language — and the base guard is
   `(EQUAL (CONSP v) 'NIL)`, not `NOT`, matching `if-false`'s committed style.
8. **`ENDP`/`ATOM` are not primitive rows** (the table is the 11 rows + `IF`).
   The S4 recursion template is stated with `(CONSP xr)`; `endp`-guarded
   sources are normalized by the untrusted front end (or `endp` is itself
   admitted as a non-recursive defun first). `aendp` the *model* constant
   exists (S1) but is not the template guard.

## 1. The wall S4 must break: `eval`'s fixed dispatch — per-env evaluator

A defun must make `(APP x y)` *mean* something: the committed `ev` dispatch
spine knows only the 11 primitive rows; unknown heads evaluate to `anil`, so a
defining-equation clause for `APP` would be **unsound** against the S3
evaluator. Two options considered:

- **(chosen) per-env evaluator rebuild** — `Terms::build()` becomes
  `Terms::build_with(rows: Vec<PrimRow>)`; an env whose table is
  `prims ++ users` gets its own `ev`/`eval`/`evlis`/`sev`/`subst`/`lsubst`
  defines and re-derived laws (incl. `subst_sema`). All of S2 is already
  data-driven from the row table (per the §9.5 S2 report: `eval_app(k)` is
  one function over rows, `fire_dispatch` is generic, `subst_sema`'s cons
  case is spine-shape-independent), so the rebuild is a *re-run*, not new
  proof work. `Thm::define` re-minting under the same display names is fine
  (uniqueness is minted inside the rule). The user-function dispatch arm is
  `f_model (car vs) (car (cdr vs)) …` — `f_model` is a previously-defined
  *total* constant, so `ev` stays a plain paramorphism (the recursion lives
  in the model function, not the evaluator).
- **(rejected, recorded escape hatch)** a Δ-parameterized evaluator
  (`ev : A → (bytes→A) → (bytes→A→A) → …`, unknown-head arm `Δ h vs`) would
  make env extension proof-free, but changes every committed S2/S3 signature
  and statement. Switch only if per-env rebuild cost ever dominates
  (measure first; the S3 report clocks the whole soundness run in seconds).

**Key invariant that makes per-env rebuild composable:** formula *encodings*
are constructor-only carrier values (env-independent), and **model constants
are minted once at admission** (stored in the `UserRow`, never re-defined by
later extensions). So transported theorems (§10) mention only carrier + model
constants and compose across envs; only `Derivable`/`eval`/`subst` and
*derivations* are env-scoped. Consequence: `Acl2Env.tm` changes from
`&'static Terms` to `Arc<Terms>` (a `static ARC_TERMS: LazyLock<Arc<Terms>>`
keeps `ground_env()` allocation-free; `terms()` stays for S0–S3 consumers).
LazyLock discipline unchanged: per-env `Terms` are plain values built from
the static carrier/prims — one-way, no re-entrancy.

## 2. S4 env shape

### 2.1 `UserRow` + clause layout

```rust
pub struct UserRow {
    pub name: SmolStr,           // surface symbol, e.g. "APP" (must differ from
                                 // every primitive, QUOTE, IF, and earlier user)
    pub formals: Vec<SmolStr>,   // distinct formal names (object vars `asym ⌜Xᵢ⌝`)
    pub body: Term,              // the encoded body ⌜body⌝ : A (closed carrier value)
    pub rec_formal: Option<usize>, // None = non-recursive
    pub model: Term,             // f_model : A → … → A, minted once at admission
    pub def_eq_model: Thm,       // ⊢ ∀x⃗. f_model x⃗ = ⟦body⟧(x⃗)   (§3.3 — PROVED)
}
```

Each user row contributes: **its `PrimRow`** (`sym`/`arity`/`model` — appended
to the env's `rows`, so the rebuilt dispatch, `eval_app(k)`, `eval_open`,
congruence and computation clauses all pick it up generically) **plus one new
clause**, the defining equation:

```text
Def(j):   d ⌜(EQUAL (f X₁ … Xₙ) body)⌝
```

a closed formula over the row's formal names as object variables — instances
flow through INST exactly like the S3 axioms (foldable by `subst_ground`).
Congruence and computation clauses for `f` come for free from the row (their
committed discharges are generic in `row.model`).

Clause layout (deterministic, extends `Acl2Env::clause_index`; `na` axioms,
`nr = rows.len()` = prims + users, `nu` users, `s6 ∈ {0,1}` the §7 flag):

```text
Axiom(i) = i          Mp = na          Inst = na+1
Ind      = na+2                        (present iff s6)
Cong(k)  = na+2+s6+k                   Comp(k)     = na+2+s6+nr+k
CongImpl(k) = na+2+s6+2nr+k            (family present iff s6)
Def(j)   = na+2+s6+(2+s6)·nr+j
n_clauses = na + 2 + s6 + (2+s6)·nr + nu
```

`ground_env()` has `s6 = 0`, `nu = 0` → the committed 29-clause layout and
`t_clause_set_builds`'s index assertions are unchanged (regression-gated).

### 2.2 `AxiomRow` + `Discharge` — the per-row discharge hook API

This fills the SKELETONS "S4+ axiom-schema discharges" entry:

```rust
pub struct AxiomRow { pub name: SmolStr, pub enc: Term, pub discharge: Discharge }

pub enum Discharge {
    /// The five committed S3 ground schemas + S6's prop-k/prop-s
    /// (name-dispatched built-in arms, as today).
    Schema,
    /// EQUAL-form axiom over object vars, discharged from a model equation
    /// `⊢ ∀x⃗. ⟦lhs⟧(x⃗) = ⟦rhs⟧(x⃗)` (statement shape per §5.2).
    ModelEq(Thm),
    /// Holds-form axiom (e.g. `consp-cons`), from `⊢ ∀x⃗. ¬(⟦form⟧(x⃗) = anil)`.
    ModelHolds(Thm),
    /// Anything else: must return `⊢ ∀σ. ¬(eval ⌜enc⌝ σ = anil)` for this
    /// env's eval; the engine does the `expand_to_pred` β-plumbing.
    Hook(Arc<dyn Fn(&Acl2Env, &Term) -> Result<Thm> + Send + Sync>),
}
```

`discharge_axiom` dispatches on `row.discharge` instead of erroring on
unknown names; a wrong/unprovable hook still *fails safe* (kernel error, no
theorem). Every hook output is kernel-checked by the `rule_induction`
conjunction build. `Def(j)` clauses are **not** `AxiomRow`s — their discharge
is the uniform `discharge_def` (§5.1) driven by `UserRow.def_eq_model`.

## 3. S4 model side: `defun_model` (init/acl2/defun.rs)

New module `defun.rs`. Input is the *encoded* body (a closed carrier value —
surface parsing SExpr → encoding stays untrusted lang-side, per S11); the
kernel side re-checks everything syntactically on the encoding (the
`subst_ground`-style `uncons`/`sym_lit_of` matching machinery exists).

```rust
pub struct DefunSpec {
    pub name: SmolStr, pub formals: Vec<SmolStr>,
    pub body: Term,                 // encoded pseudo-term over the formals
    pub rec_formal: Option<usize>,  // designated structural formal, if recursive
}
pub fn admit_defun(env: &Acl2Env, spec: &DefunSpec) -> Result<Acl2Env>
```

### 3.1 The model-image translation (single source of truth)

`model_image(env, enc, args: &[Term]) -> Result<Term>` — the compositional
model translation of a pseudo-term with formal `Xᵢ ↦ args[i]`:
symbols→the matching arg (error if not a formal), `aint`/`anil` literal→itself,
`(QUOTE v)`→`v`, `(IF a b c)`→`aif ⟦a⟧ ⟦b⟧ ⟦c⟧`, table head (prim or earlier
user or `f` itself)→`row.model ⟦a₁⟧ … ⟦aₙ⟧`. **This same function defines both
the `def_eq_model` statement's RHS and (through `eval_open`) the `discharge_def`
image** — by construction `eval_open`'s image of `enc` at σ is exactly
`model_image(enc, [σ⌜X₁⌝, …])`, so the two chains in §5.1 meet syntactically.
Any drift is a kernel error, never an unsound theorem.

### 3.2 Non-recursive defun

`f_model := Thm::define("acl2.user.<name>", λx₁…xₙ. model_image(body, x⃗))`;
`def_eq_model` = `apply_def` at free formals + `all_intro` — trivially proved.

### 3.3 Structurally recursive defun — promote the `aappend` pattern

**Promotion, not duplication:** the test-local `Append` machinery in
`carrier.rs` (`build`/`steps`/`leaf`/`scons`/`assoc`, carrier.rs:604–736) moves
into `defun.rs` as the generalized recursion engine (n formals, designated
position `r`); `carrier.rs::t_induct_instance` then drives the promoted engine
with the same exact assertions (its test-local struct is deleted).

For an accepted template body `(IF (CONSP xr) STEP BASE)` (§4):

1. **Steps** (paramorphic, other formals free and λ-closed outside, the
   `Append::steps` shape): atom `λb. ⟦BASE⟧`, nil `⟦BASE⟧`, cons
   `λh t bh bt. ⟦STEP⟧` where the translation maps `(CAR xr) ↦ h`,
   `(CDR xr) ↦ t`, `(f … (CAR xr) …) ↦ bh`, `(f … (CDR xr) …) ↦ bt`, and
   other formals to their free variables.
2. **Define** `f_model := λx₁…λxₙ. prec(steps, A) x_r` (`Append::build` shape).
3. **Per-constructor computation laws** = `Append::leaf`/`Append::scons`
   generalized: `apply_def` + `prec_eq(i)` + fold the recursor images back to
   `f_model` (`rw_all(apply_def(..).sym())`, the lisp.rs:301 trick) before
   `reduce_rhs`.
4. **`def_eq_model`** — `⊢ ∀x⃗. f_model x⃗ = aif (aconsp x_r) ⟦STEP⟧(x⃗) ⟦BASE⟧(x⃗)`
   by carrier `induct` at motive `λxr. f_model …x⃗… = aif (aconsp xr) … …`
   (other formals free in the motive, IHs *unused*):
   - atom `b`: LHS = `⟦BASE⟧` (leaf law); RHS: `consp_atom` → guard `anil`,
     cong into `aif`, `if_nil` → `⟦BASE⟧`. Nil case: same via `consp_nil`.
   - cons `h t`: LHS = folded step value (scons law); RHS: `consp_cons` →
     guard `t`, `if_t` (+`t_ne_nil`) → `⟦STEP⟧[xr := acons h t]`, then
     `proj_scons` rewrites `car/cdr (acons h t) → h/t` everywhere (including
     inside the recursive-call arguments), landing the same step value.
   - `induct` concludes the η-expanded `∀xr. (λ…) xr` (S0 contract) — do the
     assume/`all_elim`/`beta_conv`/re-close cleanup (the `soundness` pattern)
     so the stored statement is clean; `all_intro` the other formals in
     declaration order.
5. **Ground folding engine** `defun_ground(env, j, args) -> Thm`
   (`⊢ f_model v⃗ = w` for constructor-literal `v⃗`): recursively chain the
   per-constructor laws + `reduce` on payload guards — the `plus_lit` analogue
   feeding `derive_comp_folded` for user rows.

## 4. Admissibility — what is accepted, how rejection works

`admit_defun` errors (env unchanged, nothing minted, no partial defines
observable — run all checks *before* the first `Thm::define`) unless:

1. `name` is a symbol distinct from all primitive syms, `QUOTE`, `IF`, and
   every earlier user row; formals distinct.
2. `body` is a well-formed encoding whose every application head is a table
   row, an earlier user row, or (if recursive) `f` itself at the declared
   arity; every symbol atom is a formal; quote payloads arbitrary values.
3. Non-recursive (`rec_formal = None`): no occurrence of `f` in `body`.
4. Recursive: `body = (IF (CONSP xr) STEP BASE)` (or the `(IF (CONSP xr)
   BASE' STEP')`-flipped orientation is *not* accepted — the front end
   normalizes; one template, no ambiguity) with:
   - `BASE` contains no call to `f`;
   - every call to `f` in `STEP` passes, in position `r`, **exactly**
     `(CAR xr)` or `(CDR xr)` (depth 1), and passes every other formal
     verbatim;
   - `xr` occurs in `STEP` only as `(CAR xr)`, `(CDR xr)`, or inside those
     recursive calls (no raw `xr` — the paramorphism never rebuilds it);
   - nested `IF`s and arbitrary fragment terms inside `STEP`/`BASE` are fine
     (`aif` is strict/total, semantically exact).

This covers `app`, `len`, `rev`, `member`-style bodies (tree recursion too —
both `CAR` and `CDR` descent, since `prec` provides both images). Deeper
`car`/`cdr` chains, multiple recursive formals, mutual recursion, and measures
are S7 (record per-rejection in the error message).

## 5. S4 discharges + the extensibility story

### 5.1 `discharge_def(env, pred, j)` — uniform, no per-row proof

For `enc := ⌜(EQUAL (f X⃗) body)⌝` (formals as *literal* symbols — S3's
literal-only `eval_open` suffices here):

1. `chain := eval_open(tm, enc, σ)` (σ free) —
   `⊢ eval ⌜enc⌝ σ = aequal (f_model (σ⌜X₁⌝)…) B` with
   `B = model_image(body, [σ⌜X₁⌝,…])` (§3.1 syntactic agreement; the
   recursive call's image is `f_model (car (σ⌜Xr⌝)) …` — `f`'s own row is in
   the table at discharge time).
2. `def_eq_model` `all_elim`'d at the σ-images: `⊢ f_model (σX⃗) = B`.
3. Finish exactly like `discharge_cong`'s ending: `cong_arg`/`cong_fn` through
   `aequal`, `equal_refl`, `t_ne_nil`, `ne_from_eq(chain, ·)`,
   `all_intro sg`, `expand_to_pred`. Zero premises, zero clause quantifiers.

### 5.2 `ModelEq`/`ModelHolds` discharge engine

For an EQUAL-form axiom over object vars `V⃗`: `eval_open` at free σ gives
`aequal L(σV⃗) R(σV⃗)`; the supplied theorem must be
`⊢ ∀v⃗. L(v⃗) = R(v⃗)` **with body exactly the eval-images** — provide
`model_eq_target(env, enc) -> Result<Term>` computing the required statement
(callers prove *that* term, e.g. `plus_comm` lifts from `init/int.rs`);
mismatch = kernel error. `ModelHolds` is the same with `ne_transport` instead
of the `equal_refl` ending. This is how the §7 structural pack and any future
book axiom enters.

### 5.3 Env extensibility vs the soundness proof — decision

**Chosen: per-env re-proof, cached per env generation** (the S3 report's
`project_with` amortization, promoted to an API):

```rust
pub struct Acl2Session {
    env: Acl2Env,
    snd: OnceCell<Thm>,   // soundness(env), proved on first projection
}
impl Acl2Session {
    pub fn admit_defun(self, spec: &DefunSpec) -> Result<Acl2Session>; // new gen, cache cleared
    pub fn project(&self, phi: &Term, der: Thm) -> Result<Thm>;       // soundness once, then project_with
}
```

Derivations are **per-env values** (the clause set, `eval`, and `subst`
constants differ per generation): the workflow is *admit defuns first, derive
and project within the current generation*; a book replay re-derives per
generation (constructors are cheap; the expensive part — soundness — is
cached). Monotonicity ("every E-derivation is an E′-derivation") is provable
but not needed and not built. cfg-style `family_soundness` packaging stays the
recorded escape hatch if clause-count growth makes per-generation soundness
hot; **not taken now** (measured baseline: 29 clauses ≈ seconds).
Defthm-as-new-axiom (feeding a transported theorem back in as a `ModelEq`/
`ModelHolds` row for later derivations) falls out of §5.2 for equational
conclusions — flagged optional, not gate-blocking (SKELETONS).

## 6. S4 gate tests (defun.rs / derivable.rs)

All via the modules' shared `check()` style — `hyps().is_empty()` + exact
statements:

1. `t_env_layout_regression` — ground_env still 29 clauses, committed index
   assertions unchanged; an env with 1 user + s6 off has `29 + 2 + 1` clauses
   (user Cong + Comp + Def) at the §2.1 indices.
2. `t_defun_app_admitted` — admit
   `(defun app (x y) (if (consp x) (cons (car x) (app (cdr x) y)) y))`;
   assert `def_eq_model` closed + exact
   `⊢ ∀x y. app (aapp… x y) = aif (aconsp x) (acons (car x) (app (cdr x) y)) y`
   shape, plus the three per-constructor laws.
3. `t_defun_len` — `(defun len2 (x) (if (consp x) (binary-+ '1 (len2 (cdr x))) '0))`
   (int-valued list recursion); ground instance `⊢ len2 ⌜(7 7)⌝ = aint 2` via
   `defun_ground`.
4. `t_defun_nonrec` — `(defun endp2 (x) (if (consp x) 'nil 't))`; defining
   equation exact.
5. `t_defun_rejects` — `(bad x) := (bad x)` (no descent), raw-`xr`-in-STEP,
   name collision with `CAR`, unknown head: all error; env unchanged
   (clause count identical before/after).
6. `t_defun_soundness_extended` — `soundness` for the app-extended env:
   closed, exact ∀A statement (with *that env's* eval).
7. `t_defun_ground_transport` — **the S4 gate**: derive
   `⊢ Derivable ⌜(EQUAL (APP '(1) '(2)) '(1 2))⌝` (user Comp clause +
   `defun_ground` fold), project through the session, `transport_equal` →
   `⊢ app ⌜(1)⌝ ⌜(2)⌝ = ⌜(1 2)⌝` as a closed model equation; negative
   control: projecting a mismatched φ errors.

## 7. S6 prerequisites (all in the s6 env flag / constructor `s6_env`)

### 7.1 Engine generalizations

- **`eval_open` var case**: accept any `asym`-headed argument (free or
  literal name) — return `eval_var` `all_elim`'d at the name term. Heads
  (table dispatch, `QUOTE`, `IF`) stay literal-matched. Committed callers
  unaffected (they never pass `asym` of a non-literal).
- **`fire_implies` helper**: factor `discharge_mp`'s d1/d2 core into
  `fire_implies(tm, chain_ne: Thm, guard_holds: Thm) -> Result<Thm>` — from
  `¬(aif Eg B t = anil)` and `¬(Eg = anil)` conclude `¬(B' = anil)` for the
  fired body; iterated three deep by the IND discharge.
- **`val_eq_by_ext(lhs_val, rhs_val, pointwise) -> Thm`**: from a pointwise
  `⊢ lhs_val n = rhs_val n` at fresh free `n` (n not free in hyps —
  guaranteed by construction), `beta_expand` both sides, `cat::fun_ext` →
  `⊢ lhs_val = rhs_val`. This is the S6 valuation-identification workhorse.

### 7.2 New axiom rows (Discharge::Schema arms, discharged like the five)

- `prop-k`: `(IMPLIES X (IMPLIES Y X))`
- `prop-s`: `(IMPLIES (IMPLIES X (IMPLIES Y Z)) (IMPLIES (IMPLIES X Y) (IMPLIES X Z)))`

Discharges: `implies_holds` nests + bool splits on the `= anil` guards —
exactly the `equal-trans` discharge pattern, no new machinery. **No classical
axiom** (transposition/NOT-elimination) is added: the deduction compiler
(§11) emits only K/S/MP, and the gate's object proofs are positive. Deferred
with a SKELETONS entry until a book needs it.

### 7.3 Structural axiom pack (Discharge::ModelEq / ModelHolds)

- `car-cons`: `(EQUAL (CAR (CONS X Y)) X)` — ModelEq(S1 `car_cons`)
- `cdr-cons`: `(EQUAL (CDR (CONS X Y)) Y)` — ModelEq(S1 `cdr_cons`)
- `consp-cons`: `(CONSP (CONS X Y))` — ModelHolds(from S1 `consp_cons` +
  `t_ne_nil`)

(The S1 theorems must be re-stated in `model_eq_target` shape — one
`all_elim`/`all_intro` reorder each.)

### 7.4 Implication-form congruence family — `CongImpl(k)`, one per row

```text
∀x⃗ y⃗. d ⌜(IMPLIES (EQUAL x₁ y₁) (… (IMPLIES (EQUAL xₙ yₙ) (EQUAL (F x⃗) (F y⃗)))))⌝
```

Needed because the rule-form `Cong` clause cannot be applied *under object
hypotheses* (no deduction theorem for rules). Discharge: `implies_holds`
nesting around the committed `discharge_cong` core (`equal_holds` per
argument under its `ng` assumption, `cong_args`, `equal_refl`, `t_ne_nil`).
Rule-form `Cong` stays (committed tests + cheaper when hyp-free).

## 8. The induction clause — exact term

Terms are data, so the clause quantifies over the formula and the designated
variable *name*. With `s_upd(v, e) := λn:bytes. cond (n = v) e (asym n)`
(the `finite_sigma` cond shape at a *variable* guard `v`) and
`⌜(CAR v)⌝ := acons ⌜CAR⌝ (acons (asym v) anil)` (ditto `CDR`):

```text
IND: ∀f:A. ∀v:bytes.
       d (mk_implies ⌜(EQUAL (CONSP v) 'NIL)⌝ f)                     -- base
     ⟹ d (mk_implies ⌜(CONSP v)⌝
            (mk_implies (subst f (s_upd v ⌜(CAR v)⌝))
              (mk_implies (subst f (s_upd v ⌜(CDR v)⌝)) f)))          -- step
     ⟹ d f
```

quantifier order `∀f` outermost, then `∀v`; premises base-then-step. Notes:

- **Both IHs (tree induction).** The model discharge is carrier induction,
  which yields both images for free at identical cost; list induction is the
  degenerate use (the object proof ignores the car conjunct — trivial for the
  K/S compiler). This unlocks tree books, not just list books.
- **Curried IMPLIES, no AND macro; EQUAL-'NIL base guard, no NOT macro** —
  keeps the clause language exactly the committed encoder set (`mk_implies`,
  `mk_equal`, `mk_if`, `app`) + `mk_consp` (one-liner `app(b"CONSP", [asym v])`).
- The `subst f (s_upd …)` subterms appear **unreduced** in the clause (like
  INST). `derive_ind(env, f, v, d_base, d_step)` therefore rewrites the
  caller's step derivation backward: at concrete `f`/`v` the guards are
  literal, `subst_ground` computes `⊢ subst f (s_upd v ⌜(CAR v)⌝) = ⌜f[v↦(CAR v)]⌝`,
  and the constructor `rw_all`s the *sym* of that fold into the supplied
  `d_step` before `imp_elim` (the `derive_comp_folded` safety argument: the
  folded term is closed and occurs only inside the `d ⌜…⌝` head). A wrong
  fold fails `imp_elim`, never mis-derives.
- No freshness side conditions on `v` — the discharge below is sound for
  *any* `f`, `v` (if `v` does not occur in `f`, the clause instance is just
  weak, not wrong).

## 9. IND soundness discharge — proof skeleton (subst_sema precision)

At `d := pred` (`sound_pred` unchanged). Free `f:A`, `v:bytes`. Premises
assumed applied (`pred ⌜base⌝`, `pred ⌜step⌝`), opened via `ladder::br` to
`Hb : ∀σ. ¬(eval ⌜base⌝ σ = anil)` and `Hs : ∀σ. ¬(eval ⌜step⌝ σ = anil)`.

Define `upd a σ := λn. cond (n = v) a (σ n)` (inline term) and the motive

```text
M := λa:A. ∀σ. ¬(eval f (upd a σ) = anil)      (f, v, free params — allowed,
                                                the aappend motive precedent)
```

**Case atom** (free `b`; σ free; `σ′ := upd (aatom b) σ`):

1. `Hb` at σ′; `eval_open(⌜base⌝, σ′)` (needs the §7.1 var case at `asym v`):
   image `aif (aequal (aconsp (σ′ v)) anil) (aif (eval f σ′) t anil) t`.
2. `σ′ v` fires by β + `eqt_intro(refl v)` + `cond_true` → `aatom b`;
   `consp_atom` → `anil`; `equal_refl` at `anil` → guard `= t`, holds by
   `t_ne_nil`.
3. `fire_implies` → `¬(eval f σ′ = anil)` = `M(aatom b)` at σ; `all_intro sg`.

**Case nil**: identical via `consp_nil`.

**Case cons** (free `h`,`t`; IHs `M h`, `M t` as β-applied motive hypotheses,
`beta_reduce`d; σ free; `σ′ := upd (acons h t) σ`):

1. `Hs` at σ′; `eval_open(⌜step⌝, σ′)`: the two `subst f (s_upd …)` arguments
   hit the `refl` fallback and stay symbolic (by design); guard
   `aconsp (σ′ v) = aconsp (acons h t) = t` (`consp_cons`) — holds.
2. **IH transport for the car conjunct** (cdr identical with `t`):
   `subst_sema` (this env's) at `(f, s_upd v ⌜(CAR v)⌝, σ′)`, first conjunct:
   `⊢ eval (subst f s_car) σ′ = eval f σc`, `σc := λn. eval (s_car n) σ′`.
   Pointwise at fresh free `n`, `lem` split on `(n = v)`:
   - true: `cond_true` → `eval ⌜(CAR v)⌝ σ′` = `car (σ′ v)` (eval_app CAR +
     evlis chain + var case) = `car (acons h t)` = `h` (`proj_scons`); RHS
     `upd h σ` at `n` fires `cond_true` → `h`. (The `n = v` hypothesis also
     rewrites the σ-side via `cong` where needed.)
   - false: `eqf_intro` + `cond_false` both sides → `σ′ n = σ n` (inner
     `cond_false` again) vs `σ n`. Equal.
   `all`-free pointwise theorem → `val_eq_by_ext` → `⊢ σc = upd h σ` →
   `cong_arg (eval f)` → `eval f σc = eval f (upd h σ)`; IH `M h` at σ +
   `ne_transport` → `¬(eval (subst f s_car) σ′ = anil)`.
3. `fire_implies` three deep (guard, car conjunct, cdr conjunct) →
   `¬(eval f σ′ = anil)` = `M(acons h t)` at σ; `all_intro sg`;
   `beta_expand` + `imp_intro` the two motive-applied IH terms (the
   `Append::assoc` case-cons contract).

**Close**: `induct(M, cases)` → `⊢ ∀a. (λ…) a`; then for free σ:
`all_elim (σ v)` → `¬(eval f (upd (σ v) σ) = anil)`; pointwise
`∀n. upd (σ v) σ n = σ n` (lem split: true branch `cond_true` + `cong σ` on
`n = v`; false branch `cond_false`) → `val_eq_by_ext` → `upd (σ v) σ = σ` —
wait, direction: `cong_arg (eval f)` + `ne_transport` → `¬(eval f σ = anil)`;
`all_intro sg` → the `pred f` denotation; `expand_to_pred`; `imp_intro` the
two premise terms (step then base); `all_intro v` then `f`. ∎

**Fallback** (only if `fun_ext`'s abs-side hypothesis constraint bites, which
the fresh-`n` discipline prevents): prove `eval_ext`
(`⊢ ∀φ σ σ′. (∀n. σ n = σ′ n) ⟹ eval φ σ = eval φ σ′ ∧ evlis …`) by carrier
induction with exactly the `subst_sema` case structure (atom: coprod split,
var arm = hypothesis at the name; cons: one QUOTE split, F-branch = tail-IH
rewrite of the shared dispatch spine). Budget it only if needed.

## 10. Open-EQUAL transport — `transport_equal_open`

```rust
pub fn transport_equal_open(env: &Acl2Env, projected: &Thm,
                            binds: &[(&[u8], &str)]) -> Result<Thm>
// from ⊢ ∀σ. ¬(eval ⌜(EQUAL lhs rhs)⌝ σ = anil)
// to   ⊢ ∀x⃗:A. ⟦lhs⟧(x⃗) = ⟦rhs⟧(x⃗)
```

1. Parse `⌜φ⌝` off `projected` exactly as the committed `transport_equal`
   (same `bad()` guards, requires the `aequal` image head).
2. **Coverage check (honesty-critical):** syntactically collect the free
   object variables of `⌜φ⌝` (non-`QUOTE`-payload `asym` literals in
   argument/guard positions, skipping heads); every one must appear in
   `binds` (distinct names), else error — otherwise uncovered variables would
   be *silently specialized to `anil`* by the default arm.
3. `σ* := λn. cond (n = ⌜V₁⌝) x₁ (… anil)` — the `finite_sigma` shape with
   fresh HOL frees `xᵢ : A` (named per `binds`) and default `anil`.
4. `inst := projected.all_elim(σ*)`; `chain := eval_open(tm, ⌜φ⌝, σ*)`, then
   one `rhs_conv(reduce)` + `rhs_conv(collapse_conds)` pass to β-fire the
   `σ* ⌜Vᵢ⌝` redexes and decide the literal guards, landing
   `⊢ eval ⌜φ⌝ σ* = aequal L(x⃗) R(x⃗)` with `L`,`R` pure model expressions.
5. `ne_transport` + `equal_holds` → `⊢ L(x⃗) = R(x⃗)` (free `xᵢ`);
   `all_intro` in `binds` order → the ∀-quantified model equation.

The committed ground `transport_equal` becomes the `binds = []` case (keep
both entry points; ground callers unchanged). Non-`EQUAL` conclusions still
error (IMPLIES-form open transport deferred, SKELETONS).

## 11. Derivation side: the deduction compiler (init/acl2/hilbert.rs)

Untrusted derivation *builder* (all outputs kernel-checked): compiles
hypothesis-style object proofs into K/S/MP chains, so users of IND can state
the step premise.

```rust
pub enum Step {
    Hyp(usize),          // the i-th hypothesis
    Fact(Thm),           // ⊢ Derivable ⌜ψ⌝, hypothesis-free (K-weakened in)
    Mp(usize, usize),    // step j applied to step k under the hypotheses
}
pub fn derive_under(env: &Acl2Env, hyps: &[Term], steps: &[Step], goal: &Term)
    -> Result<Thm>      // ⊢ Derivable ⌜(IMPLIES h₁ (… (IMPLIES hₖ goal)))⌝
```

Standard deduction-theorem compilation (per hypothesis, innermost-out):
`Hyp(i)` → `⊢ D ⌜(IMPLIES hᵢ hᵢ)⌝` via S·K·K; `Fact` → K-chain weakening;
`Mp` → the S axiom distributing the hypothesis. Quadratic blowup in proof
length — fine at gate scale (risk register). On top, a small equational-chain
convenience (`eq_chain_under`) issuing `equal-symm`/`equal-trans`/
`CongImpl`/`if-true`/`if-false`/Def-clause instances (all INST'd hyp-free
first, then `Fact`-imported).

**The app-assoc object proofs** (`φ := (EQUAL (APP (APP X Y) Z) (APP X (APP Y Z)))`,
`v := "X"`, all moves verified against the §7 axiom set):

- *base* (hyp `g := (EQUAL (CONSP X) 'NIL)`): Def(app)+INST gives
  `(EQUAL (APP X w) (IF (CONSP X) … w))`; `if-false`+INST, MP-under-`g` →
  `(EQUAL (APP X w) w)` for `w ∈ {Y, (APP Y Z)}`; CongImpl(APP) with
  `equal-refl Z` lifts the first through `(… Z)`; `equal-symm`/`equal-trans`
  close φ.
- *step* (hyps `c := (CONSP X)`, `ihcar` (unused), `ihcdr`):
  `e₁ := (EQUAL (APP X Y) (CONS (CAR X) (APP (CDR X) Y)))` from Def+INST,
  `if-true`+INST, MP-under-`c`, `equal-trans`. Then
  `(EQUAL (APP (CONS a d) Z) (CONS a (APP d Z)))` hyp-free from Def+INST,
  `consp-cons` (ModelHolds axiom!) + `if-true` + MP, `car-cons`/`cdr-cons`
  rewrites via CongImpl chains. LHS chain + `ihcdr` under CongImpl(CONS) +
  the RHS `e₁`-instance at `Y ↦ (APP Y Z)`; symm/trans close φ.

## 12. THE S6 GATE

`(defthm app-assoc (equal (app (app x y) z) (app x (app y z))))`:

1. S4: `admit_defun` app (§6.2's spec) — session generation `E₁`.
2. Derive base and step premises in `E₁` via `derive_under` (§11).
3. `derive_ind(E₁, ⌜φ⌝, ⌜"X"⌝, d_base, d_step)` → `⊢ Derivable_{E₁} ⌜φ⌝`.
4. `session.project` (soundness for `E₁`, cached) →
   `⊢ ∀σ. ¬(eval ⌜φ⌝ σ = anil)`.
5. `transport_equal_open(E₁, projected, [("X","x"),("Y","y"),("Z","z")])` →
   **`⊢ ∀x y z. app (app x y) z = app x (app y z)`** — a closed base-HOL
   model equation about the S4-minted `app` model constant.

**Model-side target promotion:** the direct proof of exactly this statement
already exists as `carrier.rs`'s test-local `aappend` + `t_induct_instance`;
§3.3 promotes that machinery into `defun.rs`, and the S4-admitted `app` *is*
its output (same `prec` steps modulo formal order). The gate adds a
cross-check control: prove the associativity *directly* through the promoted
engine (the `Append::assoc` route) and assert the transported and direct
theorems agree on `all_elim`'d instances at shared free variables (quantifier
order may differ; compare instantiated, β-reduced conclusions).

## 13. S6 gate test list (derivable.rs / hilbert.rs / defun.rs)

1. `t_s6_env_layout` — s6 env clause count per §2.1 formula; ground_env
   regression (29, committed indices).
2. `t_prop_axioms_derive` — prop-k/prop-s derivable, exact encodings.
3. `t_structural_pack` — car-cons/cdr-cons/consp-cons derivable; their
   `ModelEq`/`ModelHolds` targets match `model_eq_target` exactly.
4. `t_cong_impl_instance` — one CongImpl firing (hyp-free control).
5. `t_deduction_compiler` — `⊢ D ⌜(IMPLIES p p)⌝`, an unused-hypothesis
   weakening, and one 2-hyp MP chain; exact statements.
6. `t_transport_open_car_cons` — **control with a known answer**: axiom
   `car-cons` derived → projected → `transport_equal_open` at
   `[("X","x"),("Y","y")]` → assert the result *instantiates to the same
   conclusion as S1's `car_cons`* (β-reduced instance comparison).
7. `t_transport_open_coverage` — uncovered-variable and duplicate-name
   transports error; nothing minted.
8. `t_ind_soundness_s6` — soundness for the s6+app env: closed, exact.
9. `t_app_assoc_premises` — base and step premise derivations, exact
   `Derivable` statements (including the unreduced-`subst` clause forms after
   `derive_ind`'s internal fold — asserted via the constructor's inputs).
10. `t_app_assoc_gate` — **THE GATE** (§12), every intermediate asserted
    exactly; plus the direct-vs-transported cross-check control.

## 14. Risk register

| risk | mitigation |
|---|---|
| per-env `Terms` rebuild cost (defines + laws + `subst_sema` per generation) | data-driven re-run, no new proofs; session caches soundness per generation; Δ-evaluator (§1) is the recorded escape hatch — measure before switching |
| env/generation value mixing (derivation from `E₀` fed to `E₁` machinery) | kernel `imp_elim`/type checks fail safe; API keeps `Terms` inside `Acl2Env`, sessions consume `self` on admit |
| `model_image` vs `eval_open` image drift (the §3.1/§5.1 syntactic-agreement contract) | single source of truth function; drift = kernel error in `discharge_def`, never unsoundness; `t_defun_soundness_extended` gates it |
| user symbol collisions poisoning `sym_ne` guard firing | admission rejects collisions up front; `sym_ne` errors on equal literals anyway (fails safe) |
| deduction-compiler blowup (quadratic in proof length) | gate-scale proofs only; measured before book-scale; derived-rule caching later |
| `fun_ext`/abs hypothesis constraint in `val_eq_by_ext` (bound var free in hyps) | fresh-`n` discipline; `eval_ext`-by-induction fallback fully sketched (§9) |
| IND premise/clause mismatch (unreduced `subst` forms) | `derive_ind` folds internally via `subst_ground`; kernel re-checks; wrong fold fails |
| `eval_open` var-case generalization regressing committed callers | committed call sites never pass non-literal `asym`; existing S3 tests gate |
| motive/case shape errors in the IND discharge (`beta_expand` contracts) | same fail-safe as all rule_induction work: conjunction build errors, no theorem |
| soundness cost growth with clause families (CongImpl doubles the per-row count) | s6 flag keeps ground env small; session cache; `family_soundness` escape hatch (recorded, not taken) |
| silently-specialized variables in open transport | §10.2 coverage check is mandatory, tested (`t_transport_open_coverage`) |

## 15. Out of scope (stays out, with SKELETONS entries)

- **Ordinal measures, non-structural recursion, mutual recursion** — S5/S7.
- **`lambda` pseudo-terms** — still outside eval/subst (unchanged fragment).
- **Classical propositional axioms** (NOT-elimination etc.) — until a book
  proof needs them (§7.2).
- **IMPLIES-form open transport** (conditional model theorems) — EQUAL-only
  for now (§10).
- **Defthm-as-new-axiom feedback** (§5.3) — optional, not gate-blocking.
- **Derivation monotonicity across env generations** — re-derive instead.
- Deeper `car`/`cdr` descent + multi-formal structural recursion — S7.

## 16. Order of work (implementation agents, commit per slice)

1. **S4a — env plumbing**: `AxiomRow`+`Discharge`, `Arc<Terms>`,
   `Terms::build_with(rows)`, env-sourced rows in `eval_open`/S2 dispatch,
   `ClauseKind::Def` + layout, regression tests (`t_env_layout_regression`).
2. **S4b — defun.rs**: `model_image`, template check, `Append` promotion
   (carrier.rs test rewired), non-rec + recursive model builds,
   `def_eq_model`, `defun_ground`.
3. **S4c — discharge_def + Acl2Session + S4 gates** (§6). Commit.
4. **S6a — prerequisites**: `eval_open` var case, `fire_implies`,
   `val_eq_by_ext`, prop-k/s + structural pack + CongImpl family with
   discharges, `s6_env`.
5. **S6b — IND**: clause, `derive_ind`, the §9 discharge.
6. **S6c — hilbert.rs** + app-assoc premises.
7. **S6d — transport_equal_open + the gate** (§12–§13). Commit; update
   SKELETONS (delete the "S4+ axiom-discharge gap" entry — filled by §2.2;
   add the §15 deferrals); record deviations-from-this-design in a §17
   implementation report here, per the S0–S3 note's discipline.

## 17. Implementation reports

### 17.1 S4 (slices §16.1–§16.3) — landed 2026-07-16, branch `lisp-demo`

All of §16.1–§16.3 is implemented and gated (`init/acl2/defun.rs` +
extensions to `prims.rs`/`term.rs`/`derivable.rs`); **S6 (§16.4–§16.7) is
not started**. The full §6 S4 gate list passes (7 tests in `defun.rs`,
incl. `t_defun_soundness_extended` and the §6.7 transport gate
`⊢ app ⌜(1)⌝ ⌜(2)⌝ = ⌜(1 2)⌝`), plus `t_discharge_arms` in
`derivable.rs` and the rewired `carrier.rs::t_induct_instance`; full
`cargo test -p covalence-init` and `-p covalence-lisp --features hol`
green. Names/deviations, per the S0–S3 discipline:

1. **Names.** `Terms::build_with(rows)` + `arc_terms()` (the static now
   *holds* `Arc<Terms>`; `terms()` unchanged for S0–S3 consumers);
   `Terms::rows()` is the accessor `eval_open`/S2 dispatch read.
   `PrimRow.sym` became `SmolStr` (user rows aren't `'static`).
   `defun.rs` public surface: `DefunSpec`, `admit_defun`, `defun_law`
   (per-constructor/defining laws at concrete args), `fold_ground` +
   `defun_ground`, `Acl2Session`. `derivable.rs` gained `AxiomRow`,
   `Discharge`, `UserRow`, `ClauseKind::Def`, `derive_def`,
   `object_vars`; `discharge_axiom` dispatches on `Discharge` with the
   five S3 schemas under a `discharge_schema` helper.
2. **UserRow carries more than §2.1**: also `def_enc` (the `Def(j)`
   clause formula, precomputed) and the raw `Thm::define` equation
   `def_eq` (pub(crate); law re-derivation needs it). `Acl2Env` keeps a
   `rows` field with the invariant `rows == tm.rows()` (constructors
   maintain it; drift would fail safe in the discharges).
3. **All four `Discharge` arms landed at S4a** (design put ModelEq/
   ModelHolds under S6a): the ∀-order contract is *first-occurrence
   `object_vars` order with bodies exactly the `eval_open` images*,
   kernel-checked; S1's `car_cons`/`cdr_cons` already satisfy it with
   **no** restatement (§7.3's "reorder" turned out unnecessary — ∀-names
   are irrelevant after `all_elim`). `model_eq_target` (the statement
   helper for callers) is NOT built — deferred to S6a with the
   structural pack (SKELETONS). Arms are unit-tested via direct
   `discharge_axiom` calls (closed `⊢ pred ⌜ax⌝` outputs + fail-safe
   negatives), not via an env soundness run — installing the pack as env
   *rows* is S6a.
4. **BASE may mention the recursive formal raw** (translated per-leaf:
   `xr ↦ aatom b / anil / acons h t` in the three cases); STEP rejects
   raw `xr` exactly as §4. Formal names may not be `b`/`h`/`t`/`sg` or
   start with `__` — new admission restriction (they'd collide with the
   induct binder hints / internal frees in the `def_eq_model` proof).
5. **Admissibility = dry-run of the translators** (`model_image` /
   `rec_steps`' `para_image`) at throwaway frees before any
   `Thm::define` — one code path both validates and builds, so nothing
   is minted on rejection (`t_defun_rejects` pins 6 rejection shapes).
6. **`defun_law` also accepts `aint ⌜i⌝` / `asym ⌜s⌝`** at the recursive
   position (payload `int_unfold`/`sym_unfold` into the atom case) —
   needed by `fold_ground` for int-payload lists (`t_defun_len`).
7. **`fold_ground` replaces §3.3.5's sketch**: a bottom-up head-driven
   normalizer (values, `CONS`, `BINARY-+` int literals via `plus_lit`,
   user rows via `defun_law` + recursion). No `aif`-guard deciding — the
   per-constructor laws never emit the top-level guard, and nested-`IF`
   ground deciding wasn't needed for the gates (SKELETONS fragment note).
8. **The carrier `Append` promotion (§3.3)**: the test-local struct is
   deleted; `rec_steps`/`rec_law_at` in `defun.rs` are the generalized
   engine (n formals, designated position, payload-aware leaf laws).
   `carrier.rs::t_induct_instance` keeps its exact assertions but now
   admits `APP` through `admit_defun` and runs the associativity
   induction over `defun_law` equations — this is also the §12
   "direct proof" the S6 gate's cross-check control will reuse.
9. **`Acl2Session`** uses `std::sync::OnceLock` (get-then-set; benign
   race) rather than `once_cell`; `new(env)` wraps any env, `soundness()`
   is the cached entry, `project` = cached soundness + `project_with`.
10. **Ground layout regression holds**: `ground_env()` is still 29
    clauses at the committed indices; one defun ⇒ 32 with
    `Cong(11)=18`, `Comp(11)=30`, `Def(0)=31` (`t_env_layout_regression`).
11. **`lang/lisp`**: only mechanical fallout (`CertEngine::tm` returns
    `&Terms`, two test borrows) — its hypothesis-style defun dictionary
    is untouched; migrating it onto S4 admission is future work.

### 17.2 S6-structural (slices §16.4–§16.7) — landed 2026-07-16, branch `lisp-demo`

All of §16.4–§16.7 is implemented and gated. **THE §12 GATE PASSES**:
`hilbert.rs::tests::t_app_assoc_gate` derives the base/step premises with
the deduction compiler, fires `derive_ind`, projects through the S6+APP
env's 50-clause soundness (incl. the §9 IND discharge), and
`transport_equal_open` lands the closed base-HOL
`⊢ ∀x y z. app (app x y) z = app x (app y z)` — every intermediate
asserted exactly, plus the direct-vs-transported cross-check control and
ill-founded-premise negative controls (swapped premises / wrong
induction variable / IH-less step shape all rejected, nothing minted).
The full §13 test list is in `derivable.rs::tests`
(`t_s6_env_layout`, `t_prop_axioms_derive`, `t_structural_pack`,
`t_cong_impl_instance`) and `hilbert.rs::tests` (`t_deduction_compiler`,
`t_transport_open_car_cons`, `t_transport_open_coverage`,
`t_ind_soundness_s6`, `t_app_assoc_premises`, `t_app_assoc_gate`).
Names/deviations, per the running discipline:

1. **Env shape.** `Acl2Env` gained a `pub s6: bool` flag;
   `ClauseKind::{Ind, CongImpl(usize)}`; `clause_index`/`n_clauses`
   implement the §2.1 formula exactly (`ground_env` keeps the committed
   29-clause layout, regression-gated). `s6_env()` = ground env + 5 new
   axiom rows (`prop-k`, `prop-s` as `Schema`; `car-cons`/`cdr-cons` as
   `ModelEq` of the S1 theorems verbatim; `consp-cons` as `ModelHolds`)
   + the flag — so `na = 10`, and the S6+APP gate env has 50 clauses
   (`Ind = 12`, `Cong(0) = 13`, `Comp(0) = 24`, `CongImpl(0) = 35`,
   `Def(0) = 49`). `admit_defun` preserves the flag.
2. **IND clause/discharge share one term builder** (`ind_encs` +
   `sigma_upd`): `sigma_upd(v, e)` at a *literal* `v` is syntactically
   `finite_sigma(&[(v, e)])`, which is what makes `derive_ind`'s
   internal `subst_ground` folds meet the clause instance. The §8 shape
   landed verbatim (∀f then ∀v, base-then-step, curried `IMPLIES`,
   `EQUAL-'NIL` base guard, both IHs).
3. **§9 discharge implementation notes**: the guard/`σ′ v` firing is
   `beta_nf` + `rw_all((v = v) = T)` + `rw_all(cond_true …)` — inner
   positions, where `collapse_conds` (leading-only) can't reach; §7.1's
   `val_eq_by_ext` is **not a named helper** — the
   pointwise-`lem`-split-then-`cat::fun_ext` move is inlined twice in
   `discharge_ind` (the per-IH `ih_transport` closure and the
   `upd (σ v) σ = σ` close), each pointwise case a `beta_conv` chain
   with `cond_true`/`cond_false` instances. `subst_sema` is proved once
   per discharge and instantiated per IH. The fallback `eval_ext`
   (§9-fallback) was **not needed** — the fresh-`__pn` discipline kept
   `fun_ext` happy.
4. **`fire_implies(tm, whole_ne, e_p, e_q, guard)`** landed as designed
   and `discharge_mp` was rewired onto it; the prop-s discharge uses it
   twice under assumed antecedents, prop-k is a vacuous `imp_intro` +
   two `implies_holds` nestings (both are `discharge_schema` match arms).
5. **`eval_open` var case** generalized to any `asym`-headed argument
   (free or literal name); committed callers unaffected (S3/S4 suites
   green unchanged). The old literal-only SKELETONS entry is deleted.
6. **`model_eq_target`/`model_holds_target` built** (the deferred S4
   item): statement = object vars ∀-closed in first-occurrence order
   over `defun::model_image` images (`model_image_of` is the pub(crate)
   seam) — `t_structural_pack` asserts the installed pack theorems match
   them *exactly*; §7.3's predicted "restatement" was again unnecessary
   (S1's `car_cons`/`cdr_cons` statements are verbatim targets;
   conclusions are locally nameless so binder names don't exist).
7. **`transport_equal_open` deviations**: the σ*-redex firing is one
   *leading-position* reduction per bind (`beta_conv` + `reduce` +
   `collapse_conds` on `σ* ⌜Vᵢ⌝` alone) rewritten into the chain —
   §10.4's single whole-image pass can't work, `collapse_conds` only
   collapses leading conds. φ is parsed off a probe `all_elim` (never
   trusted — the real instantiation is kernel-checked). Extra binds
   beyond `object_vars` are allowed (they just add outer ∀s); the
   committed ground `transport_equal` stays its own entry point rather
   than becoming the `binds = []` case.
8. **`hilbert.rs` deviations**: `Step::Fact` carries `(Term, Thm)` (not
   the design's `Fact(Thm)`) — the formula travels beside the theorem to
   avoid parsing HOL binders, and is re-checked against
   `derivable(env, ψ)` up front. §11's `eq_chain_under` became a small
   pub combinator kit over a `Fact {phi, thm}` pair (`axiom_inst`,
   `def_inst`, `cong_impl`, `mp`, `eq_refl`/`eq_symm`/`eq_trans`,
   `imp_identity`) plus a test-local step-list builder; the compiler
   itself (`derive_under` + `discharge_last`) is the classic
   innermost-out I/K/S transformation over an index-mapped line list.
9. **The §11 app-assoc object proofs** live in `hilbert.rs::tests`
   (`app_assoc_base`/`app_assoc_step`/`app_cons_lemma`), with the IH
   formulas computed *by* `subst_ground` (so they agree with
   `derive_ind`'s folds by construction). The step proof's hyp-free
   `(EQUAL (APP (CONS a d) Z) (CONS a (APP d Z)))` lemma is composed
   outside the compiler (all-`Fact` import) exactly as sketched.
10. **The §12 cross-check** re-derives the direct model-side proof
    inline against the *gate env's* `APP` model constant
    (`carrier.rs::t_induct_instance` admits its own env, whose model
    constant is a distinct `Thm::define` mint — constants don't compose
    across admissions, so the cross-check must run in-env); agreement is
    asserted on `all_elim`'d β-reduced instances (transported ∀-order is
    x,y,z; direct is y,z,x).
11. **Cost**: the S6+APP 50-clause soundness ≈ 20 s (debug), cached per
    session (`LazyLock` across the test module); each app-assoc premise
    compilation ≈ 15–20 s (the §11 quadratic blowup — 3 hypotheses).
    Within the risk-register budget; derived-rule caching is the noted
    lever before book-scale replay.
12. **Scope left open** (SKELETONS): S5/S7 recursion tiers,
    IMPLIES-form open transport, classical propositional axiom,
    defthm-as-new-axiom feedback, derivation monotonicity, and wiring
    `lang/lisp`'s surface `defthm` onto the S6 kernel path.
