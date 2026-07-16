# ACL2 S5: ordinals below ε₀ — concrete design (o-p, o<, wf, IND-ORD)

*Design for stage S5 of [`acl2-full-plan.md`](./acl2-full-plan.md), continuing
[`acl2-s0-s3-design.md`](./acl2-s0-s3-design.md) and
[`acl2-s4-s6-design.md`](./acl2-s4-s6-design.md). Agent-authored (vibes).
Verified against the committed S0–S4+S6 code
(`crates/kernel/hol/init/src/init/acl2/`, branch `lisp-demo`, 2026-07-16),
including both implementation reports. Everything below is untrusted userspace
over existing kernel rules — no new axioms, no TCB edits; every object "axiom"
is an env clause whose soundness is discharged by a proved model theorem.*

## 0. Decision summary (the judgment calls, made)

1. **ACL2-faithful ordinals confirmed**: ordinals ARE conses; `o-p : A → A`
   and `o< : A → A → A` are **carrier functions** (t/nil-valued, usable inside
   object terms), matching ACL2's own `defun`s modulo the normalizations in
   §1.1. The evaluated alternative — `o<` as a HOL relation only — dies on the
   IND-ORD clause: measure obligations `(O< m' m)` are *object formulas*, so
   `O<` must be an env **row** for `eval` to dispatch. Carrier functions it is.
2. **No new recursion machinery.** `o<`/`o-p` are *not* S4-admissible
   (depth-2 `caar` descent), and they do **not** need fuel, `cv_exists`, or a
   generic course-of-values carrier recursion: each is **one pair-valued
   paramorphism** (the S2 `ev` trick — the second pair component carries the
   value at `car x`; see §2.2). Definitions are direct `prec` builds in
   `init/acl2/ordinal.rs`.
3. **Rows are hand-installed `UserRow`s**, bypassing `admit_defun`'s template
   check but keeping the uniform `discharge_def` (which is template-independent
   — it needs only a genuinely proved `def_eq_model`). This install seam
   (§3) is deliberately **the S7 seam**: measured defuns will enter the same
   way, with `def_eq_model` proved by wf-recursion instead of `prec`.
4. **Chosen wf fragment: FULL ε₀.** `wf : ⊢ ∀x. ¬(o-p x = anil) ⟹ Acc x`
   for *all* CNF notations. The graded hierarchy (tower height `ht`) is used,
   but the grade is an **internal** `nat` (`k := ht x` at the end), so no
   meta-level fragment cap. Honesty ladder if walls appear, in order:
   **L0 = below ω** (finite ordinals; its own named theorem and the first
   commit of S5b) → **direct ω² slice** (`ω·c+n` by a bare lex `int×int`
   argument, independent of the main lemma) → **full ε₀**. Gates assert
   exactly what is proved (§11).
5. **`ints`-not-`rats` is NOT a deviation here**: ACL2's `o-p` requires
   `natp` leaves and `posp` (positive *integer*) coefficients — no rationals
   anywhere in ordinal notations. The actual dialect deviations are the
   §1.1 normalizations (`=`→`EQUAL`, `<=`/`and`/`not`/`atom` macro-expansion
   to the IF/CONSP fragment), recorded there.
6. **No `o<` transitivity lemma is needed** (a classic trap: mechanized ε₀
   proofs often prove trans/irrefl first). The main lemma's motive covers
   *equal-or-below* first exponents, which absorbs every place transitivity
   would be used (§6.3). `o<` order theory beyond wf is out of scope.
7. **nat wf infrastructure found and reused**: `strong_induct` /
   `strong_below` (`init/lambda_iter.rs`, proved in `lambda_iter.cov`) and the
   Rust driver `strong_induct_on` (`init/cv_recursion.rs`, `pub(crate)` —
   accessible). What is **missing** is the nonneg-int bridge (int `<` is only
   proved linear-order; no induction reaches `int`): three lemmas are added to
   `init/int.rs` where the private quotient recon lives (§4).

## 1. ACL2 sources and their normalized bodies

### 1.1 Normalization contract (dialect deviations, recorded here)

The front end (S11) and the S5 encodings normalize ACL2 source to the
committed head fragment (rows + `IF` + `QUOTE`), exactly as S4 did for `endp`:

- `(and a b …)` → `(IF a (and b …) 'NIL)`; `(or a b)` → `(IF a a b)`
  (for the guard positions below, `(or a b)` → `(IF a 'T b)` is used instead —
  equivalent at guard positions, and it keeps `eval` images small);
- `(not a)` / `(o-finp x)` = `(atom x)` guards → `CONSP` tests with **flipped
  branches** (no `NOT`/`ATOM` head enters a body);
- `(<= a b)` → `(IF (< b a) 'NIL 'T)` (the committed `ale` shape);
- **`(= a b)` and `(eql a b)` → `(EQUAL a b)`** in `o<`/`o-p`. Deviation: ACL2
  `=` is numeric equality (`(equal (fix a) (fix b))`), which differs from
  `EQUAL` on *non-numeric garbage* (e.g. `(= 'A 'B)` is `T`, `(EQUAL 'A 'B)`
  is `NIL`). On `o-p` arguments (the only ones wf ever sees) the two agree
  (coefficients are `posp` integers). Recorded as a dialect deviation of our
  `O<`'s completion behaviour; revisit only if a book states `o<` facts about
  garbage (add `FIX` as a defun then).

### 1.2 The seven constants (normalized bodies, ACL2 order preserved)

```text
NATP X          := (IF (INTEGERP X) (IF (< X '0) 'NIL 'T) 'NIL)
POSP X          := (IF (INTEGERP X) (< '0 X) 'NIL)
O-FIRST-EXPT X  := (IF (CONSP X) (CAR (CAR X)) '0)
O-FIRST-COEFF X := (IF (CONSP X) (CDR (CAR X)) X)
O-RST X         := (CDR X)
O< X Y  := (IF (CONSP X)
               (IF (CONSP Y)
                   (IF (EQUAL (O-FIRST-EXPT X) (O-FIRST-EXPT Y))
                       (IF (EQUAL (O-FIRST-COEFF X) (O-FIRST-COEFF Y))
                           (O< (O-RST X) (O-RST Y))
                           (< (O-FIRST-COEFF X) (O-FIRST-COEFF Y)))
                       (O< (O-FIRST-EXPT X) (O-FIRST-EXPT Y)))
                   'NIL)
               (IF (CONSP Y) 'T (< X Y)))
O-P X   := (IF (CONSP X)
               (IF (CONSP (CAR X))
                   (IF (O-P (O-FIRST-EXPT X))
                       (IF (EQUAL (O-FIRST-EXPT X) '0)
                           'NIL
                           (IF (POSP (O-FIRST-COEFF X))
                               (IF (O-P (O-RST X))
                                   (O< (O-FIRST-EXPT (O-RST X)) (O-FIRST-EXPT X))
                                   'NIL)
                               'NIL)
                           )
                       'NIL)
                   'NIL)
               (NATP X))
```

Notes against the ACL2 sources: `o<`'s cond branches are reordered only by the
`o-finp`→`CONSP` flip; the `(not (equal …))` guards become equal-tests with
swapped branches (shown swapped above). `O-P` keeps ACL2's conjunct order
(`consp (car x)` first, so `O-FIRST-EXPT X` under it is `caar x`).

## 2. Model layer — `init/acl2/ordinal.rs`

New module, `pub mod ordinal;` in `acl2/mod.rs`. One `Ordinals` theory struct
behind one `LazyLock` (`pub fn ordinals() -> Result<&'static Ordinals>`),
initializer calling only `acl2()`/`prims()`/`terms()` (one-way, no env
LazyLocks — the recorded re-entrancy discipline). All defines use the
`"acl2.ord."` prefix. If the file exceeds ~2.5k lines, split into
`ordinal/{mod,model,wf}.rs` (implementation call; record it).

### 2.1 Simple constants

`natp`, `posp`, `ofe`, `ofc`, `ors` are plain `Thm::define`s whose bodies are
**exactly the `model_image` translations** of §1.2 over the base table + the
new rows, e.g. `natp := λx. aif (aintp x) (aif (alt x (aint 0)) anil t) anil`,
`ofe := λx. aif (aconsp x) (car (car x)) (aint 0)`, `ors := λx. cdr x`.
Their `def_eq_model` is `apply_def` + `all_intro` (the committed non-recursive
recipe). Their unfolding laws (`natp_int`, `ofe_cons: ⊢ ∀h t. ofe (acons h t)
= car h`, `ofe_atom/nil = aint 0`, `ors_cons`, …) are one-line
`apply_def` + guard-firing (`consp_*` + `if_t`/`if_nil` + `t_ne_nil`).

### 2.2 `o<` and `o-p` as pair-valued paramorphisms

**The depth-2 problem**: `o<` recurses at `(caar x, caar y)` — a single
paramorphism on `x` yields images at `car x`/`cdr x` only. **The S2 pair
trick solves it**: make the recursion compute the pair
*(value at `x`, value at `car x`)*.

`OLT : A → prod (A → A) (A → A)` := `prec(steps, prod (fun A A) (fun A A))`,
with intended semantics `OLT x = (λy. o< x y, λy. o< (car x) y)`:

```text
atom l ↦ pair (λy. aif (aconsp y) t (alt (aatom l) y))
              (λy. aif (aconsp y) t (alt anil y))          -- car(atom) = anil
anil   ↦ pair (λy. aif (aconsp y) t (alt anil y)) (same)
acons h t (images oh : β, ot : β) ↦
  pair (λy. aif (aconsp y)
              (aif (aequal (car h) (car (car y)))
                   (aif (aequal (cdr h) (cdr (car y)))
                        (fst ot (cdr y))                    -- o< (cdr x) (cdr y)
                        (alt (cdr h) (cdr (car y))))
                   (snd oh (car (car y))))                  -- o< (caar x) (caar y)
              anil)
       (fst oh)                                             -- o< (car x) ·  =  o< h ·
```

`olt := λx y. fst (OLT x) y` (`Thm::define`, "acl2.ord.o-lt").

- **Per-constructor laws** (`prec_eq` + fold-back trick + `fst_pair`/`snd_pair`
  — never `delta_all` on prod): `olt_atom`, `olt_nil`, `olt_cons` (statements
  read off the steps, projected through `fst`).
- **The folding lemma** (pointwise; no `fun_ext` needed):
  `olt_snd: ⊢ ∀x y. snd (OLT x) y = olt (car x) y` — by carrier `cases()`
  (NOT induction): atom/nil cases both sides are the shared atom arm
  (`car_atom`/`car_nil`); cons case `snd (OLT (acons h t)) = fst (OLT h)` by
  the cons law, `= olt h · = olt (car (acons h t)) ·` by `car_cons`.
- **The ACL2 defining equation** (the `def_eq_model` target, RHS =
  `model_image` of §1.2's `O<` body over the full table — so it mentions
  `ofe`/`ofc`/`ors`/`alt`/`aequal`/`aif` and `olt` itself):
  `⊢ ∀x y. olt x y = aif (aconsp x) (aif (aconsp y) (aif (aequal (ofe x)
  (ofe y)) (… olt (ors x) (ors y) …) (olt (ofe x) (ofe y))) anil)
  (aif (aconsp y) t (alt x y))` — proved by carrier `induct` at
  `λx. ∀y. …` with **unused IHs** (the committed §3.3.4 move): per case, fire
  the `aconsp x` guard, rewrite `ofe/ofc/ors` at the known constructor
  (`ofe_cons` etc. — this is where `car h`/`cdr h` meet the paramorphism's
  raw arguments), and close with the per-constructor law + `olt_snd`.
  No induction is *logically* needed (cases suffice); `induct`-with-unused-IHs
  is used because it is the committed, tested driver shape.

`OP : A → prod A A` (intended `(o-p x, o-p (car x))`) is the same shape, one
level simpler (β = `prod A A`, no λy):

```text
atom l ↦ pair (natp (aatom l)) (natp anil)
anil   ↦ pair (natp anil) (natp anil)
acons h t (ph, pt) ↦
  pair (aif (aconsp h)
            (aif (snd ph)                                    -- o-p (caar x)
                 (aif (aequal (car h) (aint 0)) anil
                      (aif (posp (cdr h))
                           (aif (fst pt)                     -- o-p (cdr x)
                                (olt (ofe (cdr … t)) (car h)) -- o< (fe rst) (caar x)
                                anil)
                           anil))
                 anil)
            anil)
       (fst ph)                                              -- o-p (car x)
```

(`olt` is a defined constant by now — no mutual recursion.) `op := λx. fst
(OP x)`; folding lemma `op_snd: ⊢ ∀x. snd (OP x) = op (car x)` by `cases()`;
per-constructor laws; ACL2 defining equation as `def_eq_model` (same recipe;
RHS = `model_image` of §1.2's `O-P` body, i.e. through `natp`/`posp`/`ofe`/
`ofc`/`ors`/`olt` model constants).

### 2.3 Ground folding + the `alt` seam

- **`Prims::lt_lit(i, j)`** (new, in `prims.rs`): `⊢ alt (aint i) (aint j) =
  t` (resp. `= anil`) for literals — the `plus_lit` one-seam pattern
  (`intval_int` + `reduce` on `intLt i j` + `cond_true/false`). This fills the
  SKELETONS "`alt` has no laws" entry's first half.
- **`alt_iff`** (model law, ordinal.rs or prims.rs): `⊢ ∀x y.
  ¬(alt x y = anil) = intLt (intval x) (intval y)` — both directions via
  `cond_true`/`cond_false` + `t_ne_nil` + bool `lem` split. THE bridge between
  object `<` and `init/int.rs` order theory; used by every K-lemma in §5.
- **`ord_fold(t: &Term) -> Result<Thm>`**: ground normalizer for
  `op`/`olt`/`natp`/`posp`/`ofe`/`ofc`/`ors` applied to constructor-literal
  values — chases the per-constructor laws + `lt_lit` + `int_ne`/`sym_ne`
  guard deciding, recursing on the §2.2 recursion structure. This is the
  o-p/o< analogue of `defun_ground`; **do not feed ord heads to
  `defun::fold_ground`** (its non-recursive arm would unfold the raw pair
  define and stall — fails safe, but `ord_fold` is the supported path; add
  the head-dispatch there only if a later stage wants one entry point).

### 2.4 Tower height (HOL-level only; not a row)

`HP : A → prod nat nat` (catamorphism; intended `(ht x, ht (car x))`):
`atom/anil ↦ pair 0 0`; `acons h t (ph, pt) ↦ pair (succ (snd ph)) (fst ph)`.
`ht := λx. fst (HP x)`; laws `ht_atom/nil = 0`, `ht_cons: ⊢ ∀h t.
ht (acons h t) = succ (ht (car h))` (via the folding lemma `hp_snd:
⊢ ∀x. snd (HP x) = ht (car x)`, `cases()` again). Used ONLY by the §6.4
grading induction; never enters the object language, rows, or statements of
`wf`.

## 3. Env plumbing — `install_user_rows` (the S7 seam)

`derivable.rs` (or defun.rs) gains the batch install seam:

```rust
pub(crate) fn install_user_rows(env: &Acl2Env, rows: Vec<UserRow>) -> Result<Acl2Env>
```

mirroring `admit_defun`'s tail (defun.rs:597–611) with **one** `Terms::
build_with` rebuild for the whole batch: name-collision checks (reuse
`check_names`' core), push each row's `PrimRow { sym, arity, model }`, rebuild
`tm`, push `users`. Callers are responsible for `def_eq_model` being genuinely
proved — `discharge_def` (derivable.rs:1964) is already shape-independent
(`eval_open` on `def_enc` + the supplied equation), so a wrong equation fails
safe in `soundness`, never mis-derives. `rec_formal: None` on hand rows
(metadata for the S4 template engines only; `defun_law` is not used for them).

**Why this is the S7 seam**: S7's measured defuns produce `model` +
`def_eq_model` by wf-recursion (§10) and enter through exactly this function;
S5 proves the seam works end-to-end with the seven ordinal rows.

`with_ordinals(env: &Acl2Env) -> Result<Acl2Env>` (ordinal.rs): requires
`env.s6` (IND-ORD reuses S6 machinery); installs, in order, the seven
`UserRow`s (NATP, POSP, O-FIRST-EXPT, O-FIRST-COEFF, O-RST, O<, O-P — models
from `ordinals()`, minted once, env-independent), the §8 axiom pack, and sets
`ind_ord = vec![1]` (§7). Arities: all 1 except `O<` (2).

## 4. The nonneg-int bridge — additions to `init/int.rs`

`nat_to_int` (`natToInt := λn. iter[int] n intSucc 0`) exists; nothing relates
it to the order. Three `pub` lemmas, appended to `int.rs` next to the recon
layer (they need the private `recon`/`rel_of_pairs`/`class_*` helpers — that
is *why* they live in int.rs, the one deviation from "everything in acl2/"):

- `nat_to_int_nonneg: ⊢ ∀n:nat. intLe (int 0) (natToInt n)` — `nat_induct`
  (`intSucc` monotone via `lt_succ` + `le_def`).
- `nat_to_int_lt: ⊢ ∀m n. natLt m n ⟹ intLt (natToInt m) (natToInt n)`
  — `nat_induct` on `n` (strict mono: `m < S k ⟹ m ≤ k`, IH/refl split via
  `le_iff_lt_or_eq`, then `lt_succ` + `lt_trans`).
- `int_nonneg_nat: ⊢ ∀i:int. intLe (int 0) i ⟹ ∃n. i = natToInt n` — recon
  `i = class(a, b)`; `0 ≤ i` unfolds through the quotient `le` to `b ≤ a` on
  reps; witness `n := a - b` (`nat_sub` + `le.add_sub`), plus the helper
  `natToInt n = class(n, 0)` by `nat_induct` (zero/succ through the class
  arithmetic — the committed recon toolkit).

Order **reflection** is derived, not proved separately: from `intLt (natToInt
m) (natToInt n)` and trichotomy on `natLt m n` — the `m = n` / `n < m` branches
contradict via `lt_irrefl`/`nat_to_int_lt`+`lt_trans`.

On top (in ordinal.rs), the Rust driver mirroring `strong_induct_on`:

```rust
/// ⊢ ∀<ivar>:int. 0 ≤ ivar ⟹ body   by strong induction on nonneg ints.
/// prove_case(iv, ih) gets ih : {…} ⊢ ∀j. 0 ≤ j ⟹ j < iv ⟹ motive j.
pub(crate) fn nonneg_si_on(ivar, motive, prove_case) -> Result<Thm>
```

built from `strong_induct` at motive `λn. P (natToInt n)` + the three bridge
lemmas (transport in: `int_nonneg_nat`; IH transport: reflection). Used by L0
and the coefficient induction; no quantified-`P` theorem form needed.

## 5. The Acc predicate and the inversion kit

### 5.1 `R`, `Acc`, and its three rules (all in ordinal.rs)

```text
R    := λy x:A. ¬(op y = anil) ∧ ¬(olt y x = anil)          ("acl2.ord.below")
Acc  := λx:A. ∀S:A→bool. (∀z. (∀y. R y z ⟹ S y) ⟹ S z) ⟹ S x   ("acl2.ord.acc")
```

(the impredicative least-predicate shape of `carved.rs`'s `Wf`, single-rule
case — no `RuleSet` needed). Rules, each a small unfold/apply proof:

- `acc_intro: ⊢ ∀x. (∀y. R y x ⟹ Acc y) ⟹ Acc x`
- `acc_elim:  ⊢ ∀S. (∀z. (∀y. R y z ⟹ S y) ⟹ S z) ⟹ ∀x. Acc x ⟹ S x`
  (definition unfolding; the well-founded-induction principle)
- `acc_inv:   ⊢ ∀x. Acc x ⟹ ∀y. R y x ⟹ Acc y`
  (apply `Acc x` at `S := λz. ∀y. R y z ⟹ Acc y`; closure via `acc_intro`)

Plus the Rust driver `acc_induct_on(sname, motive, prove_case)` wrapping
`acc_elim` with the assume/`all_elim`/`beta_conv`/re-close cleanup (the
committed `soundness`-style β-plumbing; `strong_induct_on` shape).

### 5.2 Inversion kit (model lemmas; the mechanical layer)

Each by carrier `cases()` + the §2 per-constructor laws + `aif`-chain
splitting (bool `lem` split per guard; the `anil` branch contradicts the
`≠ anil` hypothesis), `equal_holds` for equality guards, `alt_iff` for `<`
guards. All `⊢`-closed, ∀-quantified:

| name | statement (sketch) |
|---|---|
| `aequal_nil` | `⊢ ∀a b. aequal a b = anil ⟹ ¬(a = b)` (contrapose `equal_refl` + `t_ne_nil`) |
| `consp_inv` | `⊢ ∀x. ¬(aconsp x = anil) ⟹ ∃h t. x = acons h t` |
| `intp_inv` | `⊢ ∀x. ¬(aintp x = anil) ⟹ ∃i. x = aint i` |
| `natp_inv` | `⊢ ∀x. ¬(natp x = anil) ⟹ ∃i. x = aint i ∧ intLe 0 i` |
| `posp_inv` | `⊢ ∀x. ¬(posp x = anil) ⟹ ∃i. x = aint i ∧ intLt 0 i` |
| `op_fin` | `⊢ ∀x. ¬(op x = anil) ⟹ aconsp x = anil ⟹ ∃i. x = aint i ∧ intLe 0 i` |
| `op_cons` | `⊢ ∀h t. ¬(op (acons h t) = anil) ⟹ ∃e c. h = acons e c ∧ ¬(op e = anil) ∧ ¬(e = aint 0) ∧ (∃j. c = aint j ∧ intLt 0 j) ∧ ¬(op t = anil) ∧ ¬(olt (ofe t) e = anil)` (six `aif` splits down §2.2's `OP` cons arm) |
| `op_fe` | `⊢ ∀x. ¬(op x = anil) ⟹ ¬(op (ofe x) = anil)` (finite: `ofe = aint 0`, `ord_fold` ground `op (aint 0) = t`; cons: `op_cons` + `ofe_cons`) |
| `olt_fin_inv` | `⊢ ∀y i. ¬(op y = anil) ⟹ ¬(olt y (aint i) = anil) ⟹ ∃j. y = aint j ∧ intLe 0 j ∧ intLt j i` (cons-`y` arm hits `olt`'s `(IF (CONSP Y) … 'NIL)` → `anil`, contradiction; atom arm via `alt_iff` + `op_fin`) |
| `olt_cons_inv` | the 4-way: `⊢ ∀y e c r. ¬(op y = anil) ⟹ ¬(olt y (acons (acons e c) r) = anil) ⟹ (∃j. y = aint j ∧ 0 ≤ j) ∨ ∃ey cy ry. y = acons (acons ey cy) ry ∧ [op-components via op_cons] ∧ ( (¬(ey = e) ∧ ¬(olt ey e = anil)) ∨ (ey = e ∧ ¬(cy = c) ∧ intLt (intval cy) (intval c)) ∨ (ey = e ∧ cy = c ∧ ¬(olt ry r = anil)) )` |

`olt_cons_inv` is the workhorse: unfold `olt` at cons/cons (`olt_cons` law +
`ofe_cons`/`ofc_cons`/`ors_cons` on the known target), split the two `aequal`
guards (`equal_holds` on the `t` side, `aequal_nil` on the `anil` side),
`alt_iff` on the coefficient branch. Budget it as the S5b mechanical hotspot
(long but decision-free).

## 6. THE HARD PROOF — `wf`, at subst_sema precision

Statements (ordinal.rs, all closed):

```text
L0        : ⊢ ∀i:int. intLe (int 0) i ⟹ Acc (aint i)
main_ord  : ⊢ ∀e. Acc e ⟹ ∀x. ¬(op x = anil) ⟹
                 ((ofe x = e) ∨ ¬(olt (ofe x) e = anil)) ⟹ Acc x
graded_wf : ⊢ ∀k:nat. ∀x. ¬(op x = anil) ⟹ natLe (ht x) k ⟹ Acc x
wf        : ⊢ ∀x. ¬(op x = anil) ⟹ Acc x
wf_induct : ⊢ ∀P:A→bool. (∀x. (∀y. R y x ⟹ P y) ⟹ P x) ⟹
                 ∀x. ¬(op x = anil) ⟹ P x
```

### 6.1 L0 (finite ordinals; the "below ω" milestone — commit separately)

`nonneg_si_on("i", λi. Acc (aint i), …)`: closure at `i` with IH. `acc_intro`
at `aint i`: fix `y`, open `R y (aint i)` (HOL ∧-elim). `olt_fin_inv` →
`y = aint j`, `0 ≤ j`, `j < i`; IH at `j` → `Acc (aint j)`; rewrite → `Acc y`.

### 6.2 The `Main'` motive — why equality is included

`Main'(e) := λe. ∀x. op x ⟹ (ofe x = e ∨ olt (ofe x) e) ⟹ Acc x` ("every
ordinal whose first exponent is ≤ e is accessible"). Including `= e` is the
load-bearing choice: it makes the *strict* case of the closure step one line
(below), eliminates any need for `o<`-transitivity, and gives §6.4 the exact
form it needs (`ofe x = e₁` with `Acc e₁`).

### 6.3 `main_ord` closure step (via `acc_induct_on` at motive `Main'`)

Given `e` and `IH_e : ∀e'. R e' e ⟹ Main'(e')`. Derive first the helper

```text
ME : ∀y. ¬(op y = anil) ⟹ ¬(olt (ofe y) e = anil) ⟹ Acc y
```

(proof: `e' := ofe y`; `op e'` by `op_fe`; `R e' e` holds; `IH_e` → `Main' e'`;
apply at `y` with the **left** disjunct `ofe y = e'` by refl).

Now fix `x` with `Hop : op x` and the disjunction `Hfe`. `∨`-elim:

- **Strict arm** (`olt (ofe x) e`): `Acc x` by `ME` at `x`. Done — this is
  where a transitivity-based proof would start working; ours is finished.
- **Equal arm** (`ofe x = e`): carrier `cases()` on `x`:
  - atom/nil: `op_fin` → `x = aint j`, `0 ≤ j` → **L0**.
  - `x = acons h t`: `op_cons` → `h = acons e₁ c₁`, `c₁ = aint j₁` (`0 < j₁`),
    `op e₁`, `op t`, `olt (ofe t) e₁`; `ofe_cons` + the equal arm → `e₁ = e`
    (rewrite everywhere). Then the **coefficient induction**: prove

    ```text
    Q : ∀c:int. 0 ≤ c ⟹ ∀r. ¬(op r = anil) ⟹ ¬(olt (ofe r) e = anil) ⟹
          Acc (acons (acons e (aint c)) r)
    ```

    by `nonneg_si_on` on `c` (with `IH_c`); inside, fix `r` and note
    `Acc r` by `ME`. Then the **rest induction**: `acc_induct_on` on `r`
    (justified by that `Acc r`) at motive

    ```text
    N := λr. ¬(op r = anil) ⟹ ¬(olt (ofe r) e = anil) ⟹
             Acc (acons (acons e (aint c)) r)
    ```

    (with `IH_r : ∀r'. R r' r ⟹ N r'`). Closure body: write
    `X̂ := acons (acons e (aint c)) r`; show `Acc X̂` by `acc_intro`: fix `y`,
    open `R y X̂`, apply `olt_cons_inv` at `(y, e, aint c, r)`, 4-way ∨-elim:
    1. *finite*: `y = aint j`, `0 ≤ j` → **L0**.
    2. *strict exponent* (`olt ey e`): `y`'s `op` ✓; `ofe y = ey`
       (`ofe_cons`) → **ME** → `Acc y`.
    3. *coefficient* (`ey = e`, `intLt (intval cy) c`): `op_cons` on `y` →
       `cy = aint jy`, `0 < jy`, so `0 ≤ jy` and `jy < c` (via `intval_int`);
       **IH_c** at `jy`, applied at `ry` (`op ry`, `olt (ofe ry) ey = e` —
       both from `op_cons` on `y`) → `Acc (acons (acons e (aint jy)) ry)`;
       rewrite by the extracted equalities (`ey = e`, `cy = aint jy`) →
       `Acc y`.
    4. *rest* (`ey = e`, `cy = aint c`, `olt ry r`): `R ry r` (`op ry` ✓,
       `olt ry r` ✓) → **IH_r** → `N ry`; its hypotheses (`op ry`,
       `olt (ofe ry) e`) from `op_cons` on `y` → `Acc (acons (acons e
       (aint c)) ry)` → rewrite → `Acc y`.

    Finally `Q` at `c := j₁` (from `0 < j₁`), `r := t` → `Acc x` (rewriting
    `x = acons (acons e (aint j₁)) t`). ∎

Nesting bookkeeping: three inductions deep (Acc-on-`e` ⊃ nonneg-int-on-`c` ⊃
Acc-on-`r`), each through its Rust driver with the ambient hypotheses carried
as ordinary `Thm` hyps and discharged by the drivers' `imp_intro`/`all_intro`
cleanups; fresh-name discipline (`__oe`, `__oc`, `__or`, `__oy`, …) exactly as
in the committed IND discharge. Every branch above names its closing lemma —
there are no "then somehow" steps left.

### 6.4 Grading, `wf`, `wf_induct`

`graded_wf` by plain `Thm::nat_induct` on `k`:

- `k = 0`: `ht x ≤ 0` → `ht x = 0` (`le_zero_iff`); `x` cannot be a cons
  (`ht_cons` is a `succ`, `succ ≠ 0`); `op_fin` → **L0**.
- `k+1`: cons case: `e₁ := ofe x = car h`; `op e₁` (`op_fe`);
  `ht x = succ (ht e₁)` (`ht_cons` + `ofe_cons`), so `ht e₁ ≤ k` (succ-le
  cancellation from the nat kit); **IH** → `Acc e₁`; **main_ord** → `Main' e₁`;
  apply at `x` with the *equal* disjunct (`ofe x = e₁`, refl) → `Acc x`.
  Atom case: L0.

`wf` := `graded_wf` at `k := ht x` + `natLe` reflexivity. **This single
instantiation is what makes the fragment full ε₀** — the grade never appears
in the statement. `wf_induct` := `wf` + `acc_elim` at `P` (one composition).

Note `graded_wf`'s IH is used at a *different `x`* (namely `e₁`) — that is
why the grading works with plain `nat_induct` (motive `λk. ∀x. …`, `x`
inside).

## 7. The ordinal-induction clause — IND-ORD

### 7.1 Env shape

`Acl2Env` gains `pub ind_ord: Vec<usize>` (IH-counts, one clause per entry;
`ground_env`/`s6_env` leave it empty — committed layouts and index tests
unchanged). `ClauseKind::IndOrd(s)`; layout **appends after the Def block**:

```text
IndOrd(s) = na + 2 + s6 + (2+s6)·nr + nu + s        n_clauses += ind_ord.len()
```

`with_ordinals` sets `ind_ord = vec![1]` (single-IH shape; the family
mechanism is general — S7 adds shapes on demand).

### 7.2 The clause term (shape `k` = number of IHs; first slice `k = 1`)

With `s_upd` = the committed `sigma_upd` and `⟨t⟩ᵢ` abbreviating
`subst m (s_upd v tᵢ)` / `subst f (s_upd v tᵢ)` (unreduced, S6-style):

```text
IND-ORD_k:  ∀f:A. ∀v:bytes. ∀m:A. ∀q:A. ∀t₁…t_k:A.
    d ⌜(O-P m)⌝                                                    -- measure total
  ⟹ d (mk_implies q (O< ⟨m⟩ᵢ m))          for i = 1..k             -- decrease
  ⟹ d (mk_implies (mk_equal q ⌜'NIL⌝) f)                           -- base
  ⟹ d (mk_implies q (mk_implies ⟨f⟩₁ (… (mk_implies ⟨f⟩_k f))))    -- step
  ⟹ d f
```

(`(O< a b)` = `tm.app(b"O<", &[a, b])` — legal at free `A`-args; `O-P`/`O<`
being rows is what makes the premises evaluable.) Premise order: measure,
decreases (i ascending), base, step — mirrored verbatim in the discharge.
This is ACL2's single-variable measured induction principle with one governing
case `q` and `k` IH substitutions; multi-case schemes (S7 defun-derived) are
future shapes, same family.

`derive_ind_ord(env, k, phi, v, m, q, ts, d_op, d_decs, d_base, d_step)`
mirrors `derive_ind` (derivable.rs:727): at literal `v` the `s_upd` instances
are `finite_sigma`, so the caller's *reduced* premises are rewritten backward
by `subst_ground` folds (`.rewrite(&fold.sym()?)`) before `fire` — wrong folds
fail `imp_elim`, never mis-derive. Requires `!env.ind_ord.is_empty()` and
`k`-matching shape.

### 7.3 Soundness discharge (at `d := pred`; free `f v m q t₁…t_k`)

Premises assumed applied and opened via `ladder::br` (committed style):

- `Hop : ∀σ. ¬(eval ⌜(O-P m)⌝ σ = anil)` — `eval_open` chain (`eval_app` for
  the `O-P` row + `evlis` + `car_cons`) rewrites to `¬(op (eval m σ) = anil)`.
- `Hdecᵢ, Hbase, Hstep` similarly (`mk_implies` images in `fire_implies` form;
  the `⟨·⟩ᵢ` subterms stay symbolic — the `refl` fallback, by design).

Goal `∀σ. ¬(eval f σ = anil)`. Apply **`wf_induct`** at

```text
P := λa:A. ∀σ. (eval m σ = a) ⟹ ¬(eval f σ = anil)
```

(`f m q tᵢ v` free in `P` — the committed aappend-motive precedent). Closure
step: fix `a`, `IH_P`; fix `σ`, `Hm : eval m σ = a`. Bool `lem` split on
`eval q σ = anil`:

- **nil**: `Hbase` at `σ`; its guard image `aequal (eval q σ) anil` fires to
  `t` (`equal_refl` after rewriting by the split hypothesis); `fire_implies`
  → done.
- **holds**: for each `i`: let `σᵢ := upd (eval tᵢ σ) σ` (the S6 §9 `upd`
  term). Two committed moves: (a) `subst_sema` at `(m, s_upd v tᵢ, σ)` +
  the pointwise-`lem`-then-`fun_ext` valuation identification (verbatim the
  committed `ih_transport` inline, with `e := eval tᵢ σ`) gives
  `eval ⟨m⟩ᵢ σ = eval m σᵢ`, and the same for `f`. (b) `Hdecᵢ` at `σ` +
  guard + (a) + `Hm` → `¬(olt (eval m σᵢ) a = anil)`; `Hop` at `σᵢ` →
  `¬(op (eval m σᵢ) = anil)`; so `R (eval m σᵢ) a` → **IH_P** at
  `y := eval m σᵢ`, applied at `σᵢ` with refl → `¬(eval f σᵢ = anil)`
  → rewrite by (a) → the step's IHᵢ image holds. `fire_implies` (k+1)-deep
  on `Hstep` → `¬(eval f σ = anil)`.

Close: `wf_induct`-output at `x := eval m σ` (its `op` hypothesis = `Hop σ`),
`P` at `σ`, refl; `all_intro`; `expand_to_pred`; `imp_intro` premises in
clause order; `all_intro` the k+4 clause variables. Structurally this is
*simpler* than the committed IND discharge (no carrier induction; the only
delicate move, valuation identification, is reused verbatim). ∎

## 8. The S5 axiom pack (env rows enabling object-level derivations)

The IND-ORD gate's obligation proofs (§11 G4) need object-level case analysis
and typed arithmetic. New `AxiomRow`s in `with_ordinals`, each with a one-shot
discharge; **the exact list is driven by the two G4 obligation scripts** — the
design pins these, implementation may add ±2 of the same kinds (record):

**Schema arms** (new match arms in `discharge_schema`, each one bool split /
`implies_holds` nest — MP-discharge machinery):

- `cases`: `(IMPLIES (IMPLIES Q P) (IMPLIES (IMPLIES (EQUAL Q 'NIL) P) P))`
  — object case split; discharge = `lem` on `eval Q σ = anil`. **This makes
  the object logic classical** (deliberately fills the SKELETONS "no classical
  axiom" entry; ACL2 is classical).
- `equal-mp`: `(IMPLIES (EQUAL P Q) (IMPLIES P Q))` — holds-transport across
  object equality (`equal_holds` + rewrite).
- `contra`: `(IMPLIES P (IMPLIES (EQUAL P 'NIL) Q))` — explosion from
  contradictory hyps (vacuous by the two premises).
- `truth`: `'T` (the formula `q(t)`; discharge: `eval_quote` + `t_ne_nil`).

**Model arms.** Conditional model facts need the missing IMPLIES-form arm:

- `Discharge::ModelImplies(Thm)` + `model_implies_target(env, enc)`
  (generalizing `model_eq_target`/`model_holds_target`): for
  `enc = (IMPLIES h₁ (… (IMPLIES hₙ c)))`, target =
  `⊢ ∀v⃗. ¬(H₁ = anil) ⟹ … ⟹ [image of c: L = R if EQUAL-headed, else
  ¬(C = anil)]` over `eval_open` images in first-occurrence `object_vars`
  order; engine = `implies_holds` nesting around the ModelEq/ModelHolds cores.

Pack rows (names → statements; model proofs all from committed kit —
`intval_*`, `int.rs` order/ring, `aplus`/`aneg` definitions):

| row | statement | model source |
|---|---|---|
| `consp-plus` | `(EQUAL (CONSP (BINARY-+ A B)) 'NIL)` | `aplus` returns `aint …`; `consp_atom` |
| `consp-neg` | `(EQUAL (CONSP (UNARY-- A)) 'NIL)` | ditto `aneg` |
| `integerp-plus` | `(INTEGERP (BINARY-+ A B))` | `intp_int` |
| `integerp-neg` | `(INTEGERP (UNARY-- A))` | ditto |
| `integerp-not-consp` | `(IMPLIES (INTEGERP X) (EQUAL (CONSP X) 'NIL))` | `intp_inv` + `consp_atom` |
| `plus-nonneg` | `(IMPLIES (EQUAL (< A '0) 'NIL) (IMPLIES (EQUAL (< B '0) 'NIL) (EQUAL (< (BINARY-+ A B) '0) 'NIL)))` | `alt_iff` + `intval_plus` + int order (holds for ALL `A B` via `intval` completion) |
| `lt-plus-one` | `(IMPLIES (EQUAL (< A '0) 'NIL) (< B (BINARY-+ '1 (BINARY-+ A B))))` | ditto (`0 ≤ a ⟹ b < 1 + (a + b)`) |
| `neg-nonneg` | `(IMPLIES (< A '0) (EQUAL (< (UNARY-- A) '0) 'NIL))` | `alt_iff` + `intval_neg` + order |

## 9. Transport — `transport_implies_open`

`derivable.rs` gains the IMPLIES-form open transport (fills that SKELETONS
entry; **required by the S7 seam** — measure obligations project as guarded
formulas that S7 must consume as model facts):

```rust
pub fn transport_implies_open(env, projected: &Thm, binds: &[(&[u8], &str)])
    -> Result<Thm>
// from ⊢ ∀σ. ¬(eval ⌜(IMPLIES h₁ (… (IMPLIES hₙ c)))⌝ σ = anil)
// to   ⊢ ∀x⃗:A. ¬(H₁(x⃗) = anil) ⟹ … ⟹ [L(x⃗) = R(x⃗) | ¬(C(x⃗) = anil)]
```

Same skeleton as the committed `transport_equal_open` (σ* from `finite_sigma`,
coverage check mandatory, per-bind leading-position redex firing), plus:
assume each antecedent's image `≠ anil`, `fire_implies` down the spine,
`equal_holds` on an `EQUAL`-headed conclusion (else leave holds-form),
`imp_intro`/`all_intro` in `binds` order. `n = 0` degenerates to the
committed ground/EQUAL paths (keep all entry points separate, per precedent).

## 10. The S7 seam (designed now, built later)

S5 hands S7, explicitly:

1. **`wf` + `wf_induct` + `Acc`/`acc_*`** — the termination substrate.
2. **`install_user_rows`** — the admission path for non-template defuns
   (§3); S7 supplies `model` + `def_eq_model` per defun.
3. **`transport_implies_open`** — turning derived obligations
   (`⊢ Derivable ⌜(O-P m)⌝`, `⊢ Derivable ⌜(IMPLIES tests (O< m' m))⌝`)
   into the model-side facts (`⊢ ∀x⃗. ¬(op (m x⃗) = anil)`, guarded
   `olt`-decrease) that the recursion construction consumes.
4. **The recursion construction itself is S7's job**, recipe fixed now: the
   `init/recursion.rs` graph method (least graph relation closed under the
   defining clauses; single-valuedness and totality **by `wf_induct` on the
   measure value** instead of `nat_induct`), yielding the total `model` and
   `def_eq_model` — postulate-free, ε-free (the foundation-invariant
   discipline). Mutual recursion / multi-case induction schemes: new
   `ind_ord` shapes + a tupled measure, same clause family.
5. **IND-ORD shape growth** (`ind_ord: Vec<usize>` + the §7.2 template) —
   S7's defun-derived induction schemes register shapes; no new soundness
   argument (the §7.3 discharge is generic in `k`).

## 11. Gates (each: `hyps().is_empty()` + exact statement, shared `check()`
style; negative controls mint nothing)

**G1 — model layer (`ordinal.rs` tests):**
1. `t_ord_defs_build` — the seven constants typecheck; per-constructor laws
   exact.
2. `t_olt_op_def_eqs` — the two ACL2 defining equations (§2.2), closed,
   exact (these are "ACL2's ordinal axioms as model theorems" from the plan).
3. `t_ord_fold_ground` — `⊢ op ⌜((1 . 2) . 0)⌝ = t` (= ω·2),
   `⊢ op ⌜((0 . 2) . 0)⌝ = anil` (zero exponent), `⊢ op ⌜(5)⌝… = anil`
   (`(5)` = `acons (aint 5) anil`: car not a cons), `⊢ op (aint 3) = t`,
   `⊢ olt ⌜1⌝ ⌜((1 . 1) . 0)⌝ = t` (1 < ω), `⊢ olt ⌜((1 . 1) . 0)⌝
   ⌜((1 . 2) . 0)⌝ = t` (ω < ω·2), `⊢ olt ⌜((2 . 1) . 0)⌝
   ⌜(((1 . 1) . 0) . 1) . 0)⌝`-shape `= t` (ω² < ω^ω), plus one `= anil`
   reflexive control.
4. `t_lt_lit_alt_iff` — the §2.3 seam lemmas.

**G2 — well-foundedness:**
5. `t_acc_rules` — `acc_intro`/`acc_elim`/`acc_inv`, exact.
6. `t_int_bridge` — the three `int.rs` lemmas + a `nonneg_si_on` smoke
   instance (in `int.rs`/`ordinal.rs` tests respectively).
7. `t_l0_finite_wf` — **L0**, exact (the "below ω" milestone).
8. `t_wf_epsilon0` — **`wf`**, `main_ord`, `graded_wf`, `wf_induct`, all
   closed and exact. THE S5 theorem.

**G3 — env integration:**
9. `t_ord_env_layout` — `with_ordinals(s6_env)` clause count/indices per the
   formulas (na = 10 + |pack| = 22-ish, nr = 18, nu = 7, +1 IndOrd — assert
   the computed numbers); ground/s6 regressions unchanged.
10. `t_ord_soundness` — `soundness` of the ordinal env: closed, exact ∀A
    statement (exercises all seven `discharge_def`s via the hand rows, the
    pack discharges, and the IND-ORD discharge).
11. `t_ord_defs_derive` — `derive_def` for `O-P`/`O<` (exact Def-clause
    encodings); a ground `⊢ Derivable ⌜(O-P '((1 . 2) . 0))⌝` via user-Comp +
    `ord_fold` + `equal-mp`/`truth` rows; transported ground control
    `⊢ olt (aint 1) ⌜ω⌝ = t` via `transport_equal`.
12. `t_transport_implies_open` — on a pack row instance with a known model
    answer (`plus-nonneg` — compare against its own `ModelImplies` source, the
    §S6-gate-№6 cross-check pattern); coverage negative control.

**G4 — IND-ORD end-to-end (the S5 gate):**
13. `t_ind_ord_soundness_controls` — mismatched premise order / wrong shape /
    non-ord env all error.
14. `t_acl2_count_admits` — `ACL2-COUNT` (§1.2-style body:
    `(IF (CONSP X) (BINARY-+ '1 (BINARY-+ (ACL2-COUNT (CAR X)) (ACL2-COUNT
    (CDR X)))) (IF (INTEGERP X) (IF (< X '0) (UNARY-- X) X) '0))`) admitted
    through **plain S4 `admit_defun`** (tree-recursive template ✓) on the
    ordinal env.
15. `t_count_obligations` — the two object derivations, exact `Derivable`
    statements:
    - `d ⌜(NATP (ACL2-COUNT X))⌝` by **S6 IND** (base: `cases` split on
      `(INTEGERP X)` then `(< X '0)`, branches via Def(ACL2-COUNT) +
      `if-true`/`if-false` + `neg-nonneg`/ground `'0` computation +
      `equal-mp`; step: Def + `integerp-plus`/`plus-nonneg` through the NATP
      Def, IHs weaving via `equal-mp`/`contra`), then
      `d ⌜(O-P (ACL2-COUNT X))⌝` via the object lemma
      `(IMPLIES (NATP U) (O-P U))` (cases on `(CONSP U)`: cons arm
      contradicts through `integerp-not-consp` + `contra`; atom arm
      Def(O-P) + `if-false` + `equal-mp`).
    - `d ⌜(IMPLIES (CONSP X) (O< (ACL2-COUNT (CDR X)) (ACL2-COUNT X)))⌝ `
      (Def-unfold under the guard, `NATP`-facts for both counts →
      `integerp-not-consp` → O< Def's finite-finite branch → `lt-plus-one`).
16. `t_app_assoc_by_measure` — **THE GATE**: app-assoc re-derived via
    `derive_ind_ord` (`f := ⌜(EQUAL (APP (APP X Y) Z) (APP X (APP Y Z)))⌝`,
    `v := "X"`, `m := ⌜(ACL2-COUNT X)⌝`, `q := ⌜(CONSP X)⌝`,
    `t₁ := ⌜(CDR X)⌝`; base/step premises = the committed S6 hilbert scripts
    with the unused car-IH dropped), projected, `transport_equal_open` →
    `⊢ ∀x y z. app (app x y) z = app x (app y z)`; asserted to agree
    (instantiated, β-reduced) with the committed S6 gate theorem.

## 12. Risk register

| risk | mitigation |
|---|---|
| `main_ord` (the triple-nested proof) stalls | the honesty ladder (§0.4): L0 commits alone ("below ω"); a direct lex-`int×int` ω² slice is independent of `main_ord`; every gate asserts only what is proved; SKELETONS entry per open rung |
| pair-paramorphism def-eq proofs drift from `model_image` output (the §3.1 contract, now for hand rows) | build the define bodies *by calling* `model_image` where possible (§2.1) and pin §2.2's RHS to `model_image` output in the test; drift = `discharge_def` kernel error, never unsoundness |
| `olt_cons_inv` / `op_cons` unfolding volume (≈6 nested guard splits each) | decision-free; one shared `aif`-chain splitter helper (the `implies_holds` pattern); budget as S5b's mechanical hotspot |
| int.rs bridge (quotient recon plumbing for `int_nonneg_nat`) | recon layer already does exactly this for the lt lemmas; if it fights, the fallback is proving the bridge in `int.cov` via the script surface — flagged, not designed |
| `Terms` rebuild + 85-ish-clause soundness cost (7 new rows + pack + IndOrd) | ONE batch rebuild (§3); one `LazyLock` session shared across G3/G4 tests (committed pattern); `family_soundness` stays the recorded escape hatch; measure before optimizing |
| G4 obligation scripts blow up the deduction compiler (nested `cases` splits) | compile per-branch lemmas separately and compose via `cases`+MP (`Fact` imports); if still walled, land G1–G3 + №13 and SKELETONS the end-to-end gate (wall discipline) — `wf` (G2) does NOT depend on G4 |
| pack-row list churn during G4 | rows are data + one-line discharges; ±2 additions of the same three kinds are pre-authorized, recorded in the §17 implementation report |
| free-name capture across three nested induction drivers | `__o*`-prefixed frees + the S4 formal-name restriction already excludes user collisions; drivers re-close eagerly (committed pattern) |
| `fold_ground` fed an ord head by a future caller | fails safe today (unknown-head error path); `ord_fold` documented as the supported engine; optional dispatch hookup noted in SKELETONS |

## 13. Out of scope (SKELETONS entries on landing)

- **S7 proper**: measured/mutual/deep-descent defuns, the wf-recursion
  construction (§10.4), multi-case IND-ORD shapes, tupled measures.
- **`o<` order theory beyond wf** (trans/irrefl/trichotomy on `o-p`s) — not
  needed by the proof (§0.6); add when a book states them.
- **Ordinal arithmetic** (`o+`, `o*`, `omega`-constructors) — book-driven.
- **`= `/`eql` faithful completion** (`FIX`-based) — §1.1 deviation stands.
- **`lambda` pseudo-terms** — unchanged fragment.
- **Rationals** (S8) — unaffected by S5 (ordinals are integer-leaved).
- Wiring `lang/lisp` surface `defthm :hints (:induct …)` onto IND-ORD.

## 14. Order of work (implementation agents; commit per slice)

1. **S5a** — `prims.rs::lt_lit`, `ordinal.rs` §2 (constants, paramorphisms,
   laws, def-eqs, `alt_iff`, `ord_fold`, `ht`), G1. Commit.
2. **S5b(i)** — `int.rs` bridge + `nonneg_si_on` + `Acc`/rules + inversion
   kit + **L0** (G2 №5–7). Commit ("below ω" milestone).
3. **S5b(ii)** — `main_ord`, `graded_wf`, `wf`, `wf_induct` (G2 №8). Commit.
4. **S5c** — `install_user_rows`, `with_ordinals`, pack + `ModelImplies`,
   `transport_implies_open`, G3. Commit.
5. **S5d** — IND-ORD (clause family, `derive_ind_ord`, discharge), G4
   №13–16 (acl2-count, obligations, THE gate). Commit; update SKELETONS
   (delete the S5 half of the "S5/S7 not started" severe entry, the
   "`alt` laws" and "IMPLIES-form transport" and "no classical axiom"
   minors as filled; add §13); append a §15 implementation report **here**
   recording deviations, per the running discipline.

## 15. Implementation reports

### 15.1 S5a + S5b — landed (2026-07-16, agent)

**Complete: §14 slices 1–3.** `init/acl2/ordinal.rs` (+ `prims.rs` `<`-seam,
`init/int.rs` bridge). All gates G1 №1–4 and G2 №5–8 pass with closed exact
statements; **THE S5 theorem is proved at full ε₀** —
`wf : ⊢ ∀x. ¬(op x = anil) ⟹ Acc x` for all CNF notations, plus `main_ord`,
`graded_wf`, `wf_induct`, and the ground composition `Acc ⌜ω·2⌝`. The
honesty ladder was **not needed** (L0 also landed separately as designed,
`Ordinals::l0_finite_wf`). Test wall-time for the whole wf chain ≈ 5 s.

**What is where:**

- `prims.rs`: `lt_eq` retained; `alt_unfold` (crate) + `lt_lit` + `alt_iff`
  (+ `alt_iff_at`); gate `t_lt_lit_alt_iff`.
- `int.rs`: `n2i_unfold`/`n2i_succ` (via `recursion::rec_holds_proof_at(int)`
  — `natToInt`'s recursion equations at result type `int`), `n2i_mk`
  (component form `natToInt n = MK n 0`, `nat_induct` through
  `lit0_mk`/`succ_mk`), `n2i_lt_iff` (two-way order coherence; stronger than
  the designed one-way lemma, kept `pub(crate)` as the driver seam), and the
  three designed `pub` lemmas `nat_to_int_nonneg` / `nat_to_int_lt` /
  `int_nonneg_nat`; gate `t_nat_int_bridge`.
- `ordinal.rs`: §2 model layer (constants, `OLT`/`OP`/`HP` paramorphisms,
  per-constructor laws, folding lemmas by `cases()`, both ACL2 defining
  equations, `ord_fold`, `ht`), §5 `Acc`+rules, the L0 slice of the
  inversion kit (`natp_inv`, `olt_fin_inv`, `posp_open`, `consp_open`,
  `op_cons_open`, `op_fe`, `aequal_nil`/`aequal_holds`, `aif_ne_split`),
  `nonneg_si_on`, `acc_induct`, `l0_finite_wf`, `main_ord` (§6.3 verbatim:
  `ME` + `Q` coefficient induction + inner `acc_induct` on the rest, the
  4-way inversion inlined as guard splits), `graded_wf`/`wf`/`wf_induct`.

**Deviations from the design (all proof-content-preserving):**

1. **Inversion kit is continuation-passing, not packaged ∃-statements** for
   the cons-side lemmas: `op_cons_inv`/`olt_cons_inv`/`consp_inv`/`posp_inv`
   became Rust openers (`op_cons_open`, `aif_ne_split` + inline splits,
   `consp_open`, `posp_open`) that hand the continuation the same component
   facts as theorems — same proofs, no ∃-elimination plumbing at every use
   site. `natp_inv` and `olt_fin_inv` (used through `∃` anyway) kept the
   designed quantified forms.
2. **Def-eqs by `cases()`, not induct-with-unused-IHs** (§2.2 note said
   cases suffice; the committed-driver-shape argument lost to simplicity).
   The `O<` equation needed the (anticipated) inner case split on `y` in the
   cons arm; `O-P`'s needed none.
3. **`olt_cons_inv` is not a standalone lemma**: the 4-way split lives
   inline in `n_case` (the `N`-closure body) as two nested `aif_ne_split`s
   over the pre-rewritten cons/cons `olt` law — each arm closes exactly per
   §6.3 (1: `finite_acc` via `natp_inv`+L0; 2: `ME`; 3: `posp_open` +
   `alt_iff` + IH_c; 4: `below`-fold + IH_r).
4. **`n2i_lt_iff` extra seam lemma** (see above); order reflection is its
   backward reading rather than a trichotomy argument.
5. **Driver β-discipline**: `nonneg_si_on` keeps motive instances in
   *applied* form for the IH and returns the β-reduced final statement
   (single-top contractions only — full `beta_nf` must be avoided wherever
   `mk_int` class bodies can appear; this bit once, in `n2i_mk`).
6. `Prims` gained the stored `lt_eq` (was discarded); no interface changes
   elsewhere. `is_value` treats the constant `t` as a value (guard results
   flow back into `ord_fold` folds).
7. Fresh-name/tag discipline extended: `by_cases`/openers take a tag
   (`__c<tag>{b,h,t}`, `__k<tag>{w,s}`), `acc_induct` takes explicit
   binder names — required by the *nested* acc-inductions in `main_ord`
   (`__we`/`__wy1` outer, `__wr`/`__wy2` inner).

**Not started (S5c/S5d, §14 slices 4–5)** — tracked in
`init/acl2/SKELETONS.md`: `install_user_rows`, `with_ordinals` + the seven
`UserRow`s (their `def_eq_model`s = the proved §2.2 equations, still to be
pinned against `model_image` output), the §8 axiom pack + `ModelImplies`,
`transport_implies_open`, the IND-ORD clause family + §7.3 discharge, and
the G3/G4 gates (`ACL2-COUNT`, obligations, app-assoc-by-measure). The §7.3
discharge's substrate (`wf_induct`) is proved and gate-tested.

### 15.2 S5c — landed (2026-07-17, agent)

**Complete: §14 slice 4** (env integration; §3 + §8 + §9, gates G3 №9–12).
The ordinal env exists: `with_ordinals(s6_env)` = 22 axioms (10 S6 + the
12-row S5 pack) + 18 table rows (11 prims + the 7 ordinal rows) + 7 user
rows = **86 clauses**, and its full soundness metatheorem proves (closed,
exact ∀A statement) in ≈ 9 s release — exercising all seven hand-row
`discharge_def`s, the four new schema arms, and the three `ModelImplies`
discharges. All G3 tests are `check()`-style (hyps-free + exact terms)
with negative controls.

**What is where:**

- `derivable.rs`: `install_user_rows` (the §3 hand-row/S7 seam; ONE
  `Terms::build_with` rebuild per batch) **with a fail-safe pin**: each
  row's `def_enc` must be exactly `⌜(EQUAL (f X⃗) body)⌝` and its
  `def_eq_model` must be closed with exactly
  `∀x⃗. f_model x⃗ = model_image(body)` over the *extended* table — drift
  errors at install, before `soundness` would catch it anyway (a
  strengthening of §3's "callers are responsible", per the §12 risk row).
  `Discharge::ModelImplies` + `model_implies_target` (+ the shared
  `strip_implies`/`parse_equal`/`implies_img`/`peel_implies_img`
  parsers), the `ModelImplies` discharge arm (antecedents assumed and
  `imp_elim`-checked, `implies_holds`-nested back up), the four §8
  schema arms in `discharge_schema` (`cases` = one boolean `lem` on
  `eval X σ = anil`; `equal-mp`/`contra`/`truth` as designed), and
  `transport_implies_open` (§9: `transport_equal_open` skeleton +
  `fire_implies` down the image spine, antecedent/rest terms peeled
  structurally off the evaluated image so they match the chain by
  construction; `EQUAL`-headed conclusions land through `equal_holds`,
  others stay holds-form).
- `ordinal.rs`: `Ordinals::user_rows` (the seven §1.2 bodies encoded;
  `def_eq_model` = `apply_def`+`all_intro` for the five plain constants,
  `olt_def()`/`op_def()` for the recursive pair), `Ordinals::axiom_pack`
  (each model row **self-checked** against its `model_*_target` before
  install), the eight §8 model theorems (`consp-plus`/`consp-neg` via a
  new `Prims::plus_unfold`/`neg_unfold` seam, `integerp-plus`/`-neg`,
  `integerp-not-consp` by carrier cases, `plus-nonneg`/`lt-plus-one`/
  `neg-nonneg` through `alt_iff_at` + the `init/int.rs` order kit), a
  small int-order helper layer (`le_add_mono_at`, `not_lt_of_ge`,
  `alt_nil_of_not_lt`/`not_lt_of_alt_nil`, `not_transport`,
  `zero_add_at`), and `pub fn with_ordinals`.
- `defun.rs`: `check_names`' core factored to `pub(crate) check_new_row`
  (shared with the install seam).

**Deviations from the design (recorded):**

1. **`ind_ord` is NOT wired** — `with_ordinals` installs rows + pack only;
   the `Acl2Env.ind_ord` field, the §7.2 clause, `derive_ind_ord`, and the
   §7.3 discharge are S5d (§14 slice 5), per the slice split. The G3 №9
   clause count is therefore 86 (not 87); `with_ordinals` must set
   `ind_ord = vec![1]` when S5d lands (SKELETONS severe entry).
2. The `cases`/`equal-mp`/`contra` axioms are spelled over object
   variables `X`/`Y` (the §8 sketch used `Q`/`P`); statements otherwise
   verbatim, and variable names are immaterial (instances flow via INST).
3. `install_user_rows` additionally rejects `rec_formal: Some(_)` on hand
   rows (that metadata is for the S4 template engines only).
4. Pack-row count: exactly the §8 list (8 model rows + 4 schemas — the
   ±2 allowance was not needed). `integerp-not-consp`'s conclusion is
   stated `EQUAL`-form as designed; its `ModelImplies` theorem's cons
   case refutes the premise (no payload split needed — `consp_atom`
   covers both atom payloads).
5. G3 №11's ground `⊢ Derivable ⌜(O-P '((1 . 2) . 0))⌝` needed an
   `equal-symm` INST step between the computation clause
   (`(EQUAL (O-P 'v) 'T)`) and `equal-mp` (which wants
   `(EQUAL 'T (O-P 'v))`) — three MPs total, as the §8 machinery
   intends.
6. `t_transport_implies_open` also asserts the reverse negative controls
   (EQUAL-form rejected by the IMPLIES transport *and* IMPLIES-form
   rejected by `transport_equal_open`) plus a positive
   `transport_equal_open` control on the projected `consp-plus` row.

### 15.3 S5d — landed (2026-07-17, agent). **S5 COMPLETE.**

**Complete: §14 slice 5** (IND-ORD; §7 + §11 G4 №13–16). The clause
family, its `wf_induct`-routed soundness discharge, and the full G4 gate
all landed; **the §7.3 discharge skeleton closed first-try, exactly as
written** (the design's "structurally simpler than IND" claim held — no
carrier induction, and the only delicate move really was the verbatim
`ih_transport` valuation identification at an opaque `tᵢ`).

**What is where:**

- `derivable.rs`: `Acl2Env::ind_ord: Vec<usize>` (empty on ground/s6
  envs — committed layouts unchanged; every constructor threads it),
  `ClauseKind::IndOrd(s)` appended after the Def block per §7.1
  (`n_clauses += ind_ord.len()`), `ind_ord_encs` (the §7.2 encodings,
  `subst` subterms unreduced, shared clause-builder/discharge — the
  `ind_encs` precedent), the clause template in `acl2_rule_set`
  (premise order measure → decreases ascending → base → step, ∀-order
  `f v m q t₁…t_k`), `derive_ind_ord` (transports the caller's reduced
  decrease/step premises backward along the `subst_ground` fold
  equations at the literal `v` — see deviation 5), and
  `discharge_ind_ord` (§7.3 verbatim: motive
  `P := λa. ∀σ. eval m σ = a ⟹ ¬(eval f σ = anil)`, boolean `lem` on
  `eval q σ = anil`, per-IH `subst_sema` + pointwise-`lem`-`fun_ext`
  identification `σc = upd (eval tᵢ σ) σ`, decrease+measure →
  `below (eval m σᵢ) a` → motive IH at `σᵢ` with refl, `(k+1)`-deep
  `fire_implies` on the step; close at `x := eval m σ`). The discharge
  demands the env's `O-P`/`O<` rows be THE ordinal model constants
  (checked up front; `ordinal.rs::below_intro` is the `below`-fold
  seam).
- `ordinal.rs`: `with_ordinals` now sets `ind_ord = vec![1]` — the
  ordinal env is **87 clauses** (G3 №9 updated; `IndOrd(0)` at index
  86); its soundness (G3 №10) exercises the IND-ORD discharge and still
  proves in ≈ 10 s release.
- `gate_s5d.rs` (new, `#[cfg(test)]` module): the G4 gate. Session =
  ordinal env + `ACL2-COUNT` (plain S4 `admit_defun` — tree recursion
  fits the template) + `APP` = **95 clauses**. The §11 №15 obligation
  scripts live here as reusable script-level helpers over the S5 pack
  (`detach`/`eq_mp_u`/`contra_u`/`cong1_u`/`if_true_u`/`if_false_u`/
  `natp_intro_u`/`transfer_natp`, hyp-free `by_cases` composition of
  `derive_under` arm lemmas, `fact_inst` = INST for non-axiom facts)
  plus the object lemmas `natp_nonneg`/`natp_integerp`/
  `not_consp_of_natp`/`natp_op`.
- `hilbert.rs`: the S6 gate's test scaffolding factored into
  `#[cfg(test)] pub(crate) mod scripts` (the `B` builder + the
  app-assoc scripts), `app_assoc_step` parameterized by `car_ih: bool`
  — the S5d gate reuses the committed base script and the car-IH-free
  step verbatim.

**Gates (all `check()`-style — hyps-free + exact statements):**

- №13 `t_ind_ord_soundness_controls` — `derive_ind_ord` on a non-ord
  env errors (no registered shape); a hand-registered `ind_ord` on
  `ground_env` **fails the soundness build** (the discharge demands the
  ordinal rows — fail-safe, no metatheorem minted, nothing projects).
- №14 `t_acl2_count_admits` — `ACL2-COUNT` admitted through the plain
  S4 template on the ordinal env; exact Def-clause encoding; 95-clause
  layout asserted; re-admission collides.
- №15 `t_count_obligations` — the exact `Derivable` statements:
  `⊢ D ⌜(NATP (ACL2-COUNT X))⌝` (S6 IND; base = `cases` on
  `(INTEGERP X)` then `(< X '0)` with `integerp-neg`/`neg-nonneg`/
  ground-`'0` branches, step = `integerp-plus` + `plus-nonneg` twice
  through the NATP Def, IHs woven by the elimination lemmas),
  `⊢ D ⌜(O-P (ACL2-COUNT X))⌝` (the `(IMPLIES (NATP X) (O-P X))`
  object lemma INSTed at the count), and
  `⊢ D ⌜(IMPLIES (CONSP X) (O< (ACL2-COUNT (CDR X)) (ACL2-COUNT X)))⌝`
  (O< Def to its finite-finite `<` branch via `integerp-not-consp`-
  derived non-consp facts, closed by `lt-plus-one`).
- №16 `t_app_assoc_by_measure` — **THE GATE**: `derive_ind_ord` at
  `m := (ACL2-COUNT X)`, `q := (CONSP X)`, `t₁ := (CDR X)` with the
  committed hilbert scripts (car-IH dropped), projected through the
  95-clause soundness, `transport_equal_open` →
  `⊢ ∀x y z. app (app x y) z = app x (app y z)` (exact); cross-checked
  by re-running the committed **S6 structural-IND route on the same
  env** (same model constant) — conclusions equal exactly. Kernel-level
  negative controls: swapped base/step, wrong premise in the decrease
  slot, non-decreasing descent `t₁ := X`, wrong induction variable,
  unregistered shape `k = 2` — all error, nothing minted.

**Deviations from the design (recorded):**

1. `derive_ind_ord` drops the explicit `k` parameter of the §7.2
   signature sketch — `k = ts.len()` (same information; the shape is
   looked up by IH count).
2. The §11 №16 cross-check is against the S6 route **re-run on the G4
   env** rather than the literal committed S6-gate theorem object: the
   two sessions mint distinct `APP` model constants (`Thm::define` per
   admission), so cross-session conclusion equality is not the honest
   comparison; same-env route-vs-route equality is (and also
   regression-covers `derive_ind` on the extended env). The committed
   S6 gate itself still runs unchanged (its step script now spelled
   `app_assoc_step(env, t, true)`).
3. №13's "non-ord env" `derive_ind_ord` control errors at the
   shape-lookup (empty `ind_ord`), not at a kernel step — the
   kernel-level controls are №16's (b)–(e). The soundness-side
   fail-safe control uses `ground_env` (cheap) rather than `s6_env`.
4. The №15 obligation derivations and their script helpers are
   test-only (`gate_s5d.rs`), not library surface — S7's admission
   machinery will generate per-defun obligations itself and is the
   right home for a library-grade version (SKELETONS S7 entry).
5. **`derive_ind_ord`'s fold is NOT the `derive_ind` whole-theorem
   `rewrite`** (the §7.2 sketch's "rewritten backward by
   `subst_ground` folds"): the reduced measure image
   `(ACL2-COUNT (CDR X))` occurs *verbatim inside the measure defun's
   own Def clause* of the `Closed d` conjunction, so rewriting the
   packaged `∀d. Closed d ⟹ d ⌜A⌝` premise corrupts its antecedent
   (caught by the gate — it fails safe, the fire's `imp_elim` errors).
   Instead the constructor inlines `derive_via_closed` and transports
   each opened `{Closed d} ⊢ d ⌜A_red⌝` consequent to `d ⌜A_unred⌝`
   by `cong_arg` at the assumed `d` on the fold equation
   `⊢ ⌜A_unred⌝ = ⌜A_red⌝` (`refl` + `rw_all`). Same fail-safety
   (`eq_mp`/`imp_elim` re-check everything), surgical scope. The same
   latent sharpness exists in `derive_ind`'s step fold (it would
   error, never mis-derive, if an IH formula ever occurred inside a
   clause); left as-is since no current caller can hit it.
