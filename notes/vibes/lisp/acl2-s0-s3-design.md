# ACL2 S0–S3: concrete design (carrier, primitives, deep terms, Derivable_ACL2)

*Design for stages S0–S3 of [`acl2-full-plan.md`](./acl2-full-plan.md). Agent-authored
(vibes). Verified against the code on branch `lisp-demo` 2026-07-16; corrections to the
plan noted inline. Everything below is untrusted userspace over existing kernel rules —
no new axioms, no TCB edits.*

## 0. Corrections to the plan (verified against the repo)

1. **`metalogic/discharge.rs` does not exist** (plan §"Why this is tractable" is stale;
   checked `crates/kernel/hol/init/src/metalogic/` — no such file, on any branch). The
   discharge helpers to reuse are the *private* per-instance copies `br`/`bridge_eq`/
   `expand_to_pred` in `peano/pa.rs` (:455–:523) and `metalogic/toy.rs` (:251). This
   design creates the shared module — but inside `init/acl2/` (see §2), since
   `metalogic/` is outside the permitted edit area.
2. **`Derivable_ACL2` goes on the unary `metalogic::RuleSet`, not `RuleSet2`** (plan
   §"Shape" says `RuleSet2`). It is a one-argument judgement over encoded formulas; the
   valuation ∀σ lives *inside* the soundness predicate (forced by the instantiation
   clause — see §6.3). `RuleSet2` is for genuinely two-argument judgements
   (`Step`/`Derives`). Precedent: `peano/pa.rs` (unary, 11 clauses).
3. The old "list.rs cons-side wall" is **closed** (`list_induct`, `cons_inj`,
   `nil_ne_cons`, `list_recursion.rs` all landed) and was never on the carved route
   anyway — carved's only list dependence is `list bool` paths.
4. `lang/lisp`'s `int_head` (`Term::free("lisp.rel.int", int → sexpr)`) is an
   **unconstrained free variable** — fine for the Step relation, soundness-fatal as a
   model constructor. Not reused anywhere below.

## 1. Carrier decision (S0)

**Decision: a second carved exact-type instance with payload `P := coprod int bytes`**,
obtained by **parameterizing the existing carved construction over the atom-payload
type** (primary route), giving

```
A  :=  aatom P | anil | acons A A          (P = coprod int bytes)
aint i := aatom (inl i)    asym s := aatom (inr s)
```

Rejected alternatives, with reasons from the code:

- **sexpr-as-is (`carved()`)** — its payload is bare `bytes`; integers would be free
  variables (unsound as constructors, see §0.4) or bytes-encoded.
- **sexpr + wellformedness predicate / bytes-encoded ints** — ground gates would pass
  via `reduce`, but S4/S6 ∀-quantified arithmetic (lifting `add_comm` etc. onto the
  carrier) hits the missing open-form bytes↔nat seam: `bytesConsNat`/`bytesAt` are
  **declaration-only** (`eval/src/defs/blob.rs`), and the `nat_binary`/`nat_bits_iso`
  round-trip is incomplete (SKELETONS). This defers the wall; the coprod payload
  *deletes* it — every arithmetic axiom lifts from the fully-proved `init/int.rs`
  ring/order theory through one `intval` computation law (§5).
- **Church encoding** — rank-1 wall: no `cdr`/projections, which S1's completion
  axioms need. Exact-type carve required (carved.rs module docs say exactly this).
- **A brand-new hand datatype via the generic engine** — the engine's carved backend is
  shape-gated to `atom P | nil | cons rec rec` (`CarvedSExprBackend::realize`,
  carved.rs:1158); a differently-shaped type needs the generic exact-type carver,
  an open SKELETONS item. The ACL2 universe *is* sexpr-shaped, so we don't need it.

**Why parameterization is safe:** every `bytes` occurrence in `carved.rs` goes through
`fn bytes_ty()` **as a type only** (verified by grep — label constructors
`atom_lab`/`inl`/`inr`, binder types, `inl_inj`/`inl_ne_inr`/`inr_inj` calls at
`(bytes, tag)`; no bytes literals or bytes ops anywhere in the construction). The Wf
witness (`Wf snilU`) is payload-independent. The refactor threads two parameters
through `CarvedSExpr::build` → `build_with(payload: Type, prefix: &str)`:

- `payload` replaces every `bytes_ty()` call site (store it as a field, use it in
  `atom_lab`, `lab_ty`, the `__b`/`__wb` binder types, the `inl_inj`/`inl_ne_inr`/
  `inr_inj` type arguments, `para_step_tys` at carved.rs:1066, and the `InductiveSig`
  arg sort);
- `prefix` replaces the literal `"sexpr"` in every `defined(...)` name
  (`"sexpr.rep.atom"` → `format!("{prefix}.rep.atom")` etc. — `Thm::define` names are
  display hints, uniqueness is minted inside the rule, but keep them distinct).

`carved()` stays exactly `build_with(Type::bytes(), "sexpr")` — **behavior-identical**
(same defines, same order), gated by the existing carved/lisp/lang-lisp test suites.
The `CarvedSExprBackend::realize` shape gate stays bytes-hardwired (backend unchanged).
The binder hints `"b"`/`"h"`/`"t"` are load-bearing for `induct` — keep them.

**Fallback** (if the refactor breaks a consumer test or must be maximally
conservative): clone the construction into `init/acl2/carrier.rs` at `P`, `carved.rs`
untouched, and add a SKELETONS entry "duplicated carve pending the payload-generic
carver". The clone is mechanical (~1–1.5k lines) but pays again at S8 (rat payload
swap), which is why parameterization is primary.

## 2. Module/file layout + Cargo wiring

All proof-bearing code lives in **covalence-init** — forced, not optional: `prec`,
`prec_eq`, `apply_def`, `derive_cases_native` are `pub(crate)`
(carved.rs:1118/:1132/:149, api.rs:249). New directory-module (precedent:
`init/inductive/`, `init/int_parse/`, `init/regex/`):

```
crates/kernel/hol/init/src/init/acl2/
  mod.rs        — module registry + stage docs; `pub mod carrier; pub mod prims;
                  pub mod term; pub mod ladder; pub mod derivable;`
  carrier.rs    — S0: `acl2_carved()` LazyLock instance at P = coprod int bytes,
                  `Acl2` theory struct (aint/asym wrappers + freeness), gate tests
  prims.rs      — S1: model primitives + completion axioms + `sym_ne`, the
                  primitive table (one data structure, see §8), tests
  term.rs       — S2: ev/eval/evlis + subst/lsubst + computation laws + subst_sema
  ladder.rs     — shared ladder plumbing: unary `derive_mixed` twin + β-bridge
                  helpers (`br`/`bridge_eq`/`expand_to_pred` generalized from
                  pa.rs/toy.rs) — ACL2-local pending promotion to metalogic/
  derivable.rs  — S3: `Acl2Env`, `acl2_rule_set`, derive_* constructors,
                  `soundness`, `project_acl2`/`transport_equal`, gate test
  SKELETONS.md  — open items (linked from init/SKELETONS.md… see §9)
```

Edits to existing files (all inside the permitted `src/init/**` area):
- `init/mod.rs`: one line, `pub mod acl2;`.
- `init/inductive/carved.rs`: the payload/prefix parameterization (§1). Nothing else.
- `init/SKELETONS.md`: link the new per-module SKELETONS; update the "carved backend is
  sexpr-shape-only" entry to mention the second instance.

**Cargo wiring: none.** Everything is inside covalence-init; no new deps, no feature
changes, no workspace edits. Tests run under `cargo test -p covalence-init` (plus
`-p covalence-lisp` to gate the carved refactor). The `crates/lang/acl2` crate split
and the dialect-trait `reify`/`transport` hooks are S3 *follow-up* (front-end wiring in
`lang/`), not part of this slice and not gate-blocking — the S3 gate test lives in
covalence-init (§6.5).

**LazyLock discipline:** `acl2_carved()`'s initializer must not call `carved()`,
`lisp()`, or any other theory LazyLock (re-entrant-LazyLock deadlock class, recorded
incident); it calls `CarvedSExpr::build_with` directly. All changes cargo-test-gated,
never merged build-only.

Naming: every `Thm::define` in acl2/ uses the `"acl2."` prefix
(`"acl2.sexpr.rep.atom"`, `"acl2.consp"`, `"acl2.ev"`, …).

## 3. S0 — carrier signatures and gate

```rust
// carrier.rs
pub fn acl2_carved() -> Result<&'static CarvedSExpr>   // build_with(coprod(int,bytes), "acl2.sexpr")
pub fn acl2() -> Result<&'static Acl2>                 // theory wrapper, one LazyLock

pub struct Acl2 {
  pub ty:   Type,   // A
  pub atom: Term,   // aatom : coprod int bytes → A   (the instance's `atom` field)
  pub nil:  Term,   // anil : A                        (the instance's `snil`)
  pub cons: Term,   // acons : A → A → A
  pub car:  Term,   // built-in, ACL2 semantics from the construction:
  pub cdr:  Term,   //   car (aatom l) = car anil = anil, car (acons h t) = h
  pub aint: Term,   // Thm::define("acl2.int", λi:int.   aatom (inl(int,bytes) i))
  pub asym: Term,   // Thm::define("acl2.sym", λs:bytes. aatom (inr(int,bytes) s))
}
```

Theorem methods (each `-> Result<Thm>`, all closed, statements exact):

| name | statement |
|---|---|
| `cons_inj(h,t,h2,t2)` | `⊢ (acons h t = acons h2 t2) ⟹ (h = h2 ∧ t = t2)` — `SExprInductive::injective(2,…)` on the instance |
| `atom_inj(l,l2)` | `⊢ (aatom l = aatom l2) ⟹ l = l2` — instance `inj_atom` |
| `int_inj(i,j)` | `⊢ (aint i = aint j) ⟹ i = j` — atom_inj ∘ `coprod::inl_inj(int,bytes,…)` through the aint define |
| `sym_inj(s,s2)` | `⊢ (asym s = asym s2) ⟹ s = s2` — atom_inj ∘ `inr_inj` |
| `int_ne_sym(i,s)` | `⊢ (aint i = asym s) ⟹ F` — atom_inj + `inl_ne_inr(int,bytes,…)` |
| `distinct(i,j,xs,ys)` | `⊢ (Cᵢ x⃗ = Cⱼ y⃗) ⟹ F` for i≠j — instance `distinct` (all pairs: atom/nil, atom/cons, nil/cons) |
| `induct(motive, cases)` | instance `induct`: cases `[⊢P(aatom b)` (free `b:P`)`, ⊢P anil, ⊢P h ⟹ P t ⟹ P (acons h t)]` ⟹ `⊢ ∀s. P s` — binder hints `b`/`h`/`t` mandatory |
| `cases()` | `⊢ ∀s. (∃b. s = aatom b) ∨ (s = anil ∨ ∃h t. s = acons h t)` — `derive_cases_native` / `InductiveFacts::cases` on the instance backend bundle |

Recursor: instance `prec(steps, β)` / `prec_eq(steps, i, β)` with step types
`[coprod int bytes → β, β, A → A → β → β → β]` (paramorphic — cons step gets raw
args *and* images). Definition pattern is `init/lisp.rs` verbatim: `Thm::define(name,
prec(steps, β))`, transport computation laws via `apply_def` + `prec_eq`, folding
recursor images back to the defined constant (`rw_all(def_applied.sym())`) **before**
`reduce_rhs` (lisp.rs:301 trick — otherwise the ε-recursor unfolds).

**S0 gate — the test list** (all in `carrier.rs` `#[cfg(test)]`, every theorem asserts
`hyps().is_empty()` and the exact printed conclusion):

1. `t_cons_inj` — asserts `cons_inj` at free `h,t,h2,t2`.
2. `t_distinct_all_pairs` — the three mixed pairs (mirror `carved.rs::distinctness_all_pairs`).
3. `t_payload_freeness` — `int_inj`, `sym_inj`, `int_ne_sym` at free vars, plus one
   ground literal instance `⊢ ¬(asym "T" = asym "NIL")` via `sym_ne` (contrapose
   `sym_inj` against `reduce`'s bytes-literal disequality — checks the LitEqCert path).
4. `t_cases` — asserts `cases()`.
5. `t_prec_smoke` — one `prec_eq` computation equation per constructor at `β := A`.
6. `t_induct_instance` — a genuine structural-induction theorem: port
   `init/lisp.rs::append`/`append_assoc` (:114/:369) onto the new carrier —
   `aappend` by paramorphic recursion, then
   `⊢ ∀x y z. aappend (aappend x y) z = aappend x (aappend y z)`.
   Mechanical transplant (lisp.rs is the proven template; only the carrier handles
   change). This is the plan's "induction instance" gate and doubles as the S4 preview.

## 4. S1 — primitives + completion axioms (prims.rs)

All model functions are `Thm::define`d over `A`; ACL2 predicates return **`A`-valued
booleans** (`t`/`nil`), since they occur inside terms. Definitions:

```
t       := asym ⌜"T"⌝                                    ("acl2.t")
(nil     = the carrier anil — see representation note below)
aconsp  := prec [λl. nil, nil, λh t _ _. t]                       : A → A
asymbolp:= prec [λl. coprod_case (λi. nil) (λs. t) l, t, λ…. nil] : A → A   (anil IS a symbol)
aintp   := prec [λl. coprod_case (λi. t) (λs. nil) l, nil, λ…. nil]
intval  := prec [λl. coprod_case (λi. i) (λs. int 0) l, 0, λ…. 0] : A → int
aequal  := λx y. cond A (x = y) t nil                             : A → A → A
aif     := λc y z. cond A (c = anil) z y                          : A → A → A → A
aplus   := λx y. aint (intAdd (intval x) (intval y))
atimes  := λx y. aint (intMul (intval x) (intval y))
aneg    := λx.   aint (intNeg (intval x))
alt     := λx y. cond A (intLt (intval x) (intval y)) t nil
```

(`coprod_case`/`cond`/`intAdd`/… are the existing catalogue constants —
`covalence_hol_eval::defs::{coprod_case, cond, int_add, int_mul, int_neg, int_lt}`.)

**Representation note (honesty contract):** ACL2's `nil` is modelled by the datatype
leaf `anil`, *not* by `asym "NIL"`; `t` is `asym "T"`. `asymbolp anil = t` (nil is a
symbol in ACL2). The front-end translator must never emit `asym "NIL"` (it would be a
distinct junk value); record this contract in prims.rs docs and enforce it at S11.

Theorems (each a named `pub fn … -> Result<Thm>`, all `⊢`-closed, ∀-quantified where
shown; proofs = `prec_eq` + fold-trick + `coprod::case_inl`/`case_inr` for payload
dispatch + `cond_true`/`cond_false`):

- **car/cdr computation + completion** (from the instance's `proj_scons`/`proj_leaf`):
  `car_cons: ⊢ ∀h t. car (acons h t) = h`, `cdr_cons`,
  `car_atom: ⊢ ∀b:P. car (aatom b) = anil` (hence `car_int`, `car_sym` instances),
  `car_nil: ⊢ car anil = anil`, cdr analogues. These **are** ACL2's car/cdr completion
  axioms, proved not postulated.
- **recognizers:** `consp_cons: ⊢ ∀h t. aconsp (acons h t) = t`,
  `consp_atom/consp_nil = nil`; `intp_int: ⊢ ∀i. aintp (aint i) = t`,
  `intp_sym/nil/cons = nil`; `symbolp_sym: ⊢ ∀s. asymbolp (asym s) = t`,
  `symbolp_nil: ⊢ asymbolp anil = t`, `symbolp_int/cons = nil`.
- **equality:** `equal_refl: ⊢ ∀x. aequal x x = t` (cond_true after `eqt_intro∘refl`);
  `equal_ne: ⊢ ∀x y. ¬(x = y) ⟹ aequal x y = nil` (guard to `F` via `eqf_intro`, then
  cond_false); `equal_holds: ⊢ ∀x y. ¬(aequal x y = anil) ⟹ x = y` (bool case split on
  `x = y`; the ¬-case contradicts via `equal_ne` + `t_ne_nil`);
  `t_ne_nil: ⊢ ¬(t = anil)` (instance distinct, atom vs nil).
- **if:** `if_nil: ⊢ ∀y z. aif anil y z = z`;
  `if_t: ⊢ ∀c y z. ¬(c = anil) ⟹ aif c y z = y`.
- **arithmetic completion + lifting seam:**
  `intval_int: ⊢ ∀i. intval (aint i) = i` (THE lifting law),
  `intval_sym/nil/cons = 0` (non-numbers as 0 — ACL2's arithmetic completion),
  `intval_plus: ⊢ ∀x y. intval (aplus x y) = intAdd (intval x) (intval y)`
  (definition + intval_int).
- **lifted axioms (the S1 demonstration set):**
  `plus_comm: ⊢ ∀x y. aplus x y = aplus y x` (from `init::int::add_comm`),
  `plus_assoc: ⊢ ∀x y z. aplus (aplus x y) z = aplus x (aplus y z)`
  (`add_assoc` + `intval_plus`). Further ACL2 arithmetic axioms lift the same way
  on demand at S3/S4 — zero bytes/encoding proofs anywhere.
- **helper:** `sym_ne(s1: &[u8], s2: &[u8]) -> Result<Thm>` — `⊢ ¬(asym ⌜s1⌝ = asym ⌜s2⌝)`
  for distinct literals, via `reduce`'s blob disequality + contraposed `sym_inj`.
  Heavily used by S2's dispatch firing.

**S1 gate:** every theorem above as a test; plus the ground instance
`⊢ aplus (aint 2) (aint 2) = aint 4` computed by `apply_def` + `intval_int` +
`TermExt::reduce` on `intAdd 2 2` (the performance seam — literals fold, never unfold).

## 5. S2 — deep terms + valuation semantics (term.rs)

**Decision: pseudo-terms are carrier values (metacircular / terms-as-data)** — no
second datatype. Justification: (a) a dedicated pterm type with ≥4 constructors is not
sexpr-shaped, so it needs the generic exact-type carver (open SKELETONS item); (b) ACL2
terms literally are s-expressions; (c) `quote` payloads are then just values. The
S2/S3 **fragment**: variables (`asym s`), quoted constants (`(QUOTE v)`), applications
of the fixed primitive table (`(f a₁ … aₙ)` with `f` a primitive symbol). **`lambda` is
deferred to S4** (SKELETONS entry) — S3 is the ground/equational fragment per the plan.

Rust-side encoders (plain `Term` builders over free/closed `A`-terms, no defines):
`q(v) = list2 (asym "QUOTE") v`, `app1/app2/app3(sym, args…)`, `mk_equal(a,b) =
app2("EQUAL",a,b)`, `mk_if(a,b,c)`, `mk_implies(p,q) = mk_if(p, mk_if(q, q(t), q(anil)),
q(t))`, `mk_plus`, etc.

**Evaluator — one paramorphic recursor, pair-valued** (term-eval × list-eval; needed
because a cons is a term or an argument list and shape can't distinguish them):

```
ev : A → (bytes → A) → (A × A)          β := (bytes→A) → prod A A, "acl2.ev"
  atom l  ↦ λσ. pair (coprod_case (λi. aint i) (λs. σ s) l) anil
  anil    ↦ λσ. pair anil anil
  acons h t (images eh et) ↦ λσ. pair (dispatch h) (acons (fst (eh σ)) (snd (et σ)))
    where vs := snd (et σ) and dispatch h :=
      cond (h = ⌜asym "QUOTE"⌝) (car t)                      -- raw t: paramorphism
      (cond (h = ⌜asym "IF"⌝)   (aif (car vs) (car (cdr vs)) (car (cdr (cdr vs))))
      (cond (h = ⌜asym "CAR"⌝)  (car (car vs))
      … one cond per primitive-table row (CDR CONS CONSP INTEGERP SYMBOLP EQUAL
        BINARY-+ BINARY-* UNARY-- <) …
      anil))                                                  -- unknown head: nil

eval  := λφ σ. fst (ev φ σ)     evlis := λφ σ. snd (ev φ σ)   ("acl2.eval"/"acl2.evlis")
```

Strict `aif` is semantically exact (the logic is total). Unknown heads evaluate to
`anil` — honest fragment boundary: the S3 clause set derives nothing about them.
Variables evaluate through σ; integers self-evaluate; constants arrive quoted (the
translator quotes them). Use `init/prod.rs` `pair/fst/snd` with the `fst_pair`/
`snd_pair` theorems — never `delta_all` on prod (known over-unfolding gotcha).

Computation laws (from the three `prec_eq` equations, projected through fst/snd +
`fire_cond`-style guard firing with `sym_ne` deciding the symbol guards):

- `eval_var: ⊢ ∀s σ. eval (asym s) σ = σ s`
- `eval_int: ⊢ ∀i σ. eval (aint i) σ = aint i`
- `eval_nil: ⊢ ∀σ. eval anil σ = anil`
- `eval_quote: ⊢ ∀x σ. eval (q x) σ = x`
- `evlis_nil: ⊢ ∀σ. evlis anil σ = anil`, `evlis_atom: ⊢ ∀b σ. evlis (aatom b) σ = anil`
- `evlis_cons: ⊢ ∀h t σ. evlis (acons h t) σ = acons (eval h σ) (evlis t σ)`
- `eval_app_F` per table row, e.g.
  `eval_app_car: ⊢ ∀t σ. eval (acons ⌜CAR⌝ t) σ = car (car (evlis t σ))`,
  `eval_app_plus: ⊢ ∀t σ. eval (acons ⌜BINARY-+⌝ t) σ = aplus (car (evlis t σ)) (car (cdr (evlis t σ)))`,
  `eval_app_if: ⊢ ∀t σ. eval (acons ⌜IF⌝ t) σ = aif (car (evlis t σ)) …` — data-driven
  from the table (each row records how many earlier guards must fire `F` via `sym_ne`).

**Substitution — the same pair-valued paramorphic shape** (`subst_pair`, then
`subst := fst`, `lsubst := snd`), σs : bytes → A mapping variable names to *term
encodings*:

```
  atom l  ↦ λσs. pair (coprod_case (λi. aint i) (λs. σs s) l) anil
  anil    ↦ λσs. pair anil anil
  acons h t (sh st) ↦ λσs. pair (cond (h = ⌜QUOTE⌝) (acons h t)      -- quotes opaque
                                       (acons h (snd (st σs))))       -- head stays raw
                                (acons (fst (sh σs)) (snd (st σs)))
```

Laws: `subst_var: ⊢ ∀s σs. subst (asym s) σs = σs s`, `subst_quote`, `subst_app:
⊢ ∀h t σs. ¬(h = ⌜QUOTE⌝) ⟹ subst (acons h t) σs = acons h (lsubst t σs)`,
`lsubst_cons`, etc.

**The key S2 lemma (hardest proof of the slice) — semantic substitution:**

```
subst_sema: ⊢ ∀φ. ∀σs σ.  eval  (subst  φ σs) σ = eval  φ (λv. eval (σs v) σ)
                        ∧ evlis (lsubst φ σs) σ = evlis φ (λv. eval (σs v) σ)
```

By carrier `induct` at the conjunctive motive (both components needed as IH).
Case structure, fully determined:
- **atom:** payload split via `coprod::cases` on `l`; int/sym branches by
  `eval_int`/`eval_var`/`subst_var` + β. (No dependence on σs defaults — fully general.)
- **anil:** both sides `anil` by the nil equations.
- **acons (h,t free, IHs for h,t):** ONE boolean case split on `(h = ⌜QUOTE⌝)`
  (excluded middle on a HOL equation — `DerivedRules` bool cases):
  - guard `T`: both `subst` and `eval`'s dispatch fire their QUOTE branch;
    `eval_quote` both sides; the raw `t` matches literally.
  - guard `F` (`eqf_intro` bridges `¬` → `= F`): `subst_app` keeps `h` raw, so both
    sides are `dispatch(h, …)` cond-spines differing **only** in `vs` — rewrite
    `evlis (lsubst t σs) σ = evlis t (…)` by the t-IH's second component and the spines
    are α-equal; **no further guard firing needed** (the raw-`t` argument occurs only
    in the already-discharged QUOTE branch). Second component: `evlis_cons`/
    `lsubst_cons` + both IH components.

**S2 gate:** `t_eval_ground` — `⊢ eval ⌜(CAR (CONS '1 '2))⌝ σ = aint 1` with σ a free
valuation, computed by chaining `eval_app_car`/`eval_app_cons`/`eval_quote` +
`car_cons` + `reduce`; plus `t_subst_sema` asserting the lemma; plus one substitution
computation instance `⊢ subst ⌜(EQUAL X X)⌝ σs = ⌜(EQUAL (QUOTE v) (QUOTE v))⌝` for a
concrete finite σs (built as nested `cond` on names with identity default `λv. asym v`).

## 6. S3 — Derivable_ACL2, soundness, transport (ladder.rs + derivable.rs)

### 6.1 Ladder plumbing (ladder.rs — the reusable seam)

Generalized from `pa.rs`:455–:523 / `toy.rs`:251 (currently copy-pasted per instance):

```rust
pub fn derive_mixed(rs: &RuleSet, clause_idx: usize, n_clauses: usize,
                    args: &[Term], premises: Vec<Premise>) -> Result<Thm>
    // unary twin of binary::derive_mixed: derive_via_closed + nth_conjunct +
    // all_elim per arg + imp_elim per premise (Side = plain fact,
    // Derivation = sub-derivation auto-opened via all_elim(d)/imp_elim(closed))
pub fn br(d_pred: &Term, enc: &Term) -> Result<Thm>       // ⊢ (λφ.pred φ) ⌜e⌝ = pred ⌜e⌝ (beta_conv)
pub fn bridge_eq(…) / pub fn expand_to_pred(…)            // pa.rs shapes, RuleSet-generic
```

Doc-note + SKELETONS entry: promotion target `metalogic/` (outside the current edit
area); `peano/pa.rs` and `metalogic/toy.rs` migrate onto it then.

### 6.2 The environment + rule set (derivable.rs)

Data-driven clause layout (GrammarEnv pattern, **not** relation.rs's hand-maintained
index arithmetic), env-scoped from day one so S4's per-defun growth has a home:

```rust
pub struct Acl2Env {
  pub axioms: Vec<(SmolStr, Term)>,   // closed A-encodings ⌜ax⌝ (formulas over encoded vars X,Y,Z…)
  pub prims:  &'static [PrimRow],     // the S1/S2 primitive table (drives comp + congruence clauses)
}
pub fn ground_env() -> Acl2Env        // the S3 instance
pub fn acl2_rule_set(env: &Acl2Env) -> Result<RuleSet<'_>>   // unary metalogic::RuleSet, Φ := A
pub fn derivable(env, φ: &Term) -> Result<Term>              // Derivable_ACL2 ⌜φ⌝
```

Clause layout, deterministic order (index map derived from env, exposed as
`Acl2Env::clause_index(kind)`):

1. **Axiom clauses**, one per `env.axioms` entry: `d ⌜ax⌝`. S3 axiom list:
   `equal-refl (EQUAL X X)`, `equal-symm (IMPLIES (EQUAL X Y) (EQUAL Y X))`,
   `equal-trans`, `if-true (IMPLIES X (EQUAL (IF X Y Z) Y))`,
   `if-false (IMPLIES (EQUAL X (QUOTE nil)) (EQUAL (IF X Y Z) Z))` — all closed
   carrier values with variables as `asym "X"` etc.; instances flow from the INST rule.
2. **MP:** `∀p q:A. d (mk_implies p q) ⟹ d p ⟹ d q`.
3. **INST:** `∀s:(bytes→A). ∀φ:A. d φ ⟹ d (subst φ s)`. First-order in `d` — the
   β-capture wall does not apply (it blocks HOAS-*motive* clauses in Church-fold
   carriers, peano/SKELETONS #1; cfg/mod.rs:31 confirms first-order clause sets are
   safe; here `s` is an ordinary function argument, `all_elim`'d with a concrete term).
4. **Congruence clauses**, one per primitive-table row (arity-templated):
   `∀a₁ b₁ a₂ b₂:A. d ⌜(EQUAL a₁ b₁)⌝ ⟹ d ⌜(EQUAL a₂ b₂)⌝ ⟹ d ⌜(EQUAL (f a₁ a₂) (f b₁ b₂))⌝`.
5. **Computation clauses** (the quote-homomorphism family), one per row:
   `∀x⃗:A. d (mk_equal (appₙ ⌜f⌝ (q x₁) … (q xₙ)) (q (f_model x₁ … xₙ)))` — e.g.
   plus: `∀x y. d ⌜(EQUAL (BINARY-+ 'x 'y) '(aplus x y))⌝`. Ground arithmetic facts
   are instances with the model image folded by `reduce`.

Clause count ≈ 5 + 2 + 2·|table| ≈ 27 — fine for `nth_conjunct`'s linear scan;
the cfg `family_soundness` packaging is the recorded escape hatch when S4 grows this.

### 6.3 Derivation constructors

Thin wrappers over `ladder::derive_mixed` (each `-> Result<Thm>` concluding
`⊢ Derivable_ACL2 ⌜…⌝`, hypothesis-free):

```rust
pub fn derive_axiom(env, name)                          // clause-1 family
pub fn derive_mp(env, d_imp: Thm, d_p: Thm)             // Premise::Derivation ×2
pub fn derive_inst(env, d_phi: Thm, s: Term)            // s : bytes → A concrete
pub fn derive_cong(env, row, d_eq1: Thm, d_eq2: Thm)
pub fn derive_comp(env, row, args: &[Term])             // + fold literal images by reduce
```

No type-variable pinning needed anywhere (the carrier is ground — simpler than
pa/toy, no `inst_tfree` step).

### 6.4 Soundness + transport

```
holds := λv:A. ¬(v = anil)
pred  := λφ:A. ∀σ:(bytes→A). holds (eval φ σ)          -- ∀σ INTERNAL (forced by INST)

pub fn soundness(env) -> Result<Thm>
   ⊢ ∀φ:A. Derivable_ACL2 φ ⟹ (∀σ. ¬(eval φ σ = anil))       via rule_induction
pub fn project_acl2(env, der: Thm) -> Result<Thm>              // project_normalized shape
   ⊢ ∀σ. ¬(eval ⌜φ⌝ σ = anil)
pub fn transport_equal(env, projected: Thm) -> Result<Thm>
   // for φ = ⌜(EQUAL lhs rhs)⌝ with closed lhs/rhs: instantiate σ := λv. anil,
   // compute eval by the S2 equations, then equal_holds ⟹  ⊢ ⟦lhs⟧ = ⟦rhs⟧  (base HOL)
```

Do **not** copy prop.rs's free-valuation trick (free `v`, meta-level ∀) — the INST
clause's discharge must vary σ, which is exactly why PA's specialise clause is blocked.
Per-clause discharges (each a lemma proving the clause at `d := pred`, β-bridged by
`ladder::br`):

- axiom clauses: `∀σ. eval ⌜ax⌝ σ ≠ anil` — eval unfolds (concrete heads, guards fired
  by `sym_ne`), lands on S1 facts (`equal_refl`+`t_ne_nil`; symm/trans/if-axioms need
  one bool split on the relevant `… = anil`).
- MP: unfold `mk_implies` through `eval_app_if`; `if_t` on the p-premise; bool split on
  `eval q σ = anil` (nil-branch contradicts the implies-premise via `if_nil`).
- INST: exactly `subst_sema` — the σ on the right becomes `λv. eval (s v) σ`, which the
  internalized ∀σ absorbs.
- congruence: `equal_holds` on both premises, rewrite, `equal_refl`.
- computation: `eval_app_F` + `eval_quote` + the S1 computation law for `f_model`,
  then `equal_refl` + `t_ne_nil`.

### 6.5 S3 gate — `(defthm four (equal (+ 2 2) 4))` via transport

Test `t_defthm_four_transports` (derivable.rs):

1. `φ := mk_equal(app2(⌜BINARY-+⌝, q(aint 2), q(aint 2)), q(aint 4))`.
2. `der := derive_comp(env, Plus, [aint 2, aint 2])` — concludes
   `⊢ Derivable_ACL2 ⌜(EQUAL (+ '2 '2) '(aplus (aint 2) (aint 2)))⌝`; fold
   `aplus (aint 2) (aint 2) → aint 4` inside the conclusion by S1's ground law
   (`reduce` on `intAdd 2 2`), landing `⊢ Derivable_ACL2 ⌜φ⌝`.
3. `s := soundness(env)`; `p := project_acl2(env, der)` —
   `⊢ ∀σ. ¬(eval ⌜φ⌝ σ = anil)`.
4. `final := transport_equal(env, p)` — `⊢ aplus (aint 2) (aint 2) = aint 4`.
5. Assert: `final.hyps().is_empty()`, exact statement, and that the value was produced
   by the derivation pipeline (the test constructs no direct-arithmetic shortcut; the
   intermediate `Derivable` and soundness theorems are asserted too).

Front-end note (out of this slice): `lang/lisp::acl2.rs::admit_defthm` later reroutes
translate → encode → derive → project → transport, replacing "rejected: free
variables"; the `crates/lang/acl2` crate split + dialect-trait `reify`/`transport`
hooks happen then (layout per the reconnaissance: `Box<dyn DialectSession>` to break
the `Lang::Acl2` cycle). The kernel-side gate above does not depend on it.

## 7. Risk register

| risk | status/mitigation |
|---|---|
| carved parameterization regresses `carved()` consumers (lang/lisp, sexpr_parse, json_parse, web /lisp) | payload threads as a *type only* (verified); behavior-identical bytes instance; gate = existing `cargo test -p covalence-init -p covalence-lisp`; fallback = clone (§1) |
| LazyLock re-entrancy deadlock (recorded incident class) | `acl2_carved()` init calls `build_with` directly, never another theory LazyLock; **everything cargo-test-gated, never build-only** |
| `pub(crate)` engine surface (`prec`, `prec_eq`, `apply_def`, `derive_cases_native`) | modules live in covalence-init `src/init/acl2/` — resolved by layout |
| old list.rs cons-side wall | **closed** (list_induct/cons_inj/list_recursion landed) and irrelevant to carved (only `list bool` paths used) |
| bytes↔int open-form seam (`bytesConsNat`/`bytesAt` declaration-only) | **avoided entirely** by the coprod payload; arithmetic lifts from proved `init/int.rs` via `intval_int` |
| β-capture wall (peano/SKELETONS #1) | not applicable: first-order clause set, lambda-as-data, no HOAS motives (cfg/mod.rs:31 precedent); INST's function-typed ∀ is an ordinary `all_elim` |
| free-valuation trap (prop/PA precedent: specialise clause blocked) | pred internalizes ∀σ; INST discharged by `subst_sema` |
| `subst_sema` cons case (free-`h` cond dispatch can't fire) | designed around: single bool split on `(h = ⌜QUOTE⌝)`; F-branch reduces to IH rewrite with **no** further guard firing (§5). Budget as the hardest lemma of the slice |
| prod `delta_all` over-unfolding (recorded gotcha) | use `fst_pair`/`snd_pair` theorems only |
| recursor unfolding in computation laws | fold images back to the defined constant before `reduce_rhs` (lisp.rs:301 trick) |
| clause-proof/layout mismatch in `rule_induction` | fails safe (kernel error in conj/imp_elim, never unsoundness); lay out clauses once in `acl2_rule_set`, reused verbatim for bound `d` and `d := pred` |
| clause-count growth at S4+ (`nth_conjunct` linear, Closed rebuilt per call) | env-scoped rule set from day one; cfg `family_soundness` is the proven size-independent packaging to switch to |
| `nil`-vs-`asym "NIL"` junk value | representation contract (§4): translator never emits `asym "NIL"`; `asymbolp anil = t` |
| `<`-computation clause / lambda / per-book axioms | deferred with SKELETONS entries (§9); gate does not need them |

## 8. Reuse seam: mid-level API vs ACL2-specific

**Reusable (built generic now):**
- the **payload-generic carved carve** (`build_with(payload, prefix)`) — directly
  serves S8's rat payload swap and any future sexpr-shaped carrier; keeps `carved()`
  as one instance;
- **`ladder.rs`** — unary `derive_mixed` + β-bridge helpers (`br`/`bridge_eq`/
  `expand_to_pred`), `RuleSet`-generic, the missing shared discharge module the plan
  wrongly assumed existed; promotion target `metalogic/` (then pa/toy migrate);
- the **primitive table** (`PrimRow { surface_sym, arity, model_const, comp_law, … }`)
  — ONE data structure driving S1 definitions, S2 `eval` dispatch + `eval_app_F` laws,
  and S3 congruence + computation clauses. Adding a primitive touches one row.

**ACL2-specific (stays in init/acl2/):** the carrier instance, model semantics
(`aif`/`aequal`/`intval` completion choices), encoders, `Acl2Env` axiom list,
`transport_equal`, the honesty/representation contracts.

**Deferred, flagged not built:** the dialect-trait `reify`/`transport` hooks + the
`crates/lang/acl2` crate (S3 follow-up, front-end side); the theory-ladder *trait*
proper (prop/PA/ACL2 share the metalogic functions today — a trait adds value only
once a third consumer needs dynamic dispatch; note in SKELETONS, don't speculate).

## 9. SKELETONS entries (created with the code, per stage)

`init/acl2/SKELETONS.md` (new, linked from `init/SKELETONS.md`):
- S2/S3 fragment: `lambda` terms not in the eval/subst fragment (deferred to S4's
  definitional principle); unknown heads evaluate to `anil`.
- `<` computation clause + ordering axioms deferred (S3 gate is `+`-only).
- `ladder.rs` is metalogic-shaped but ACL2-homed — promote to `metalogic/` and migrate
  `peano/pa.rs`/`metalogic/toy.rs` when that area is editable.
- (only if fallback route taken) duplicated carve pending the payload-generic carver.

`init/SKELETONS.md`: update the "carved backend is sexpr-shape-only" entry to record
the second (`coprod int bytes`) instance; `crates/lang/lisp/SKELETONS.md`: the
"ground-only defthm" entry gains a pointer here (it is *filled* only when the S3
front-end rewiring lands, not by this slice).

## 9.5 S0 implementation report (2026-07-16, branch `lisp-demo`)

S0 landed on the **primary route** — no fallback needed, no walls hit:

- `carved.rs` parameterization went through as predicted: payload threads as a
  type only; `build_with(payload, prefix)` + a `payload` field; `carved()` =
  `build_with(Type::bytes(), "sexpr")`, all 7 existing carved tests + the
  full covalence-init/covalence-lisp suites green (behavior-identical).
- One design detail not in §1: the **recursor cache had to move per-instance**
  (the old `rec_poly` was a process-global `LazyLock` keyed to the `sexpr`
  instance — a second instance would have silently gotten the wrong recursor).
  Now a `rec_cell: OnceLock<…>` field + `CarvedSExpr::{rec_poly, rec_at}`
  methods; `SExprInductive` gained a lifetime (`&'a CarvedSExpr`) and a
  `CarvedSExpr::inductive()` accessor. The engine (`recursion_equations` etc.)
  is fully payload-agnostic (grep: zero `bytes` references).
- `sym_ne` needed one bridge the design didn't spell out: `reduce` on blob
  literals yields the **literal** `⌜F⌝`, while `not_intro` wants the *defined*
  `F` — `covalence_hol_eval::fal_from_lit` crosses (the EG3b bridge).
- `cases()` runs `derive_cases_native` directly over the instance's bare
  `induct` (the backend bundle stays bytes-gated, as designed).
- Gate tests (`init/acl2/carrier.rs`): `t_cons_inj`, `t_distinct_all_pairs`,
  `t_payload_freeness` (incl. ground `⊢ ¬(asym "T" = asym "NIL")` and the
  equal-literal rejection), `t_cases` (exact disjunction), `t_prec_smoke`,
  `t_induct_instance` (`aappend` associativity by structural induction — the
  lisp.rs transplant was mechanical, carrier handles only). All closed
  (`hyps().is_empty()`), exact statements asserted.

## 10. Order of work (implementation agent, S0 slice first)

1. carved.rs parameterization (`build_with`), `carved()` unchanged; full test suite
   green (`cargo test -p covalence-init -p covalence-lisp`).
2. `init/acl2/carrier.rs` + `mod.rs` registration + S0 gate tests (§3).
3. commit; then S1 (`prims.rs`), S2 (`term.rs` — `subst_sema` last), S3 (`ladder.rs`
   then `derivable.rs`), each stage test-gated and committed per the plan's discipline.
