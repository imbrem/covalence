+++
id = "N0026"
status = "draft"
review = "unreviewed"

[[contributions]]
role = "author"
actor = "agent:claude"
at = "2026-07-14T20:09:33+01:00"
source = "legacy"
agent = "claude"
harness = "claude"
+++

# Verifying simple Lisp programs via SMT

*Direction, 2026-07-14. The goal: prove `∀`-properties of simple Lisp programs,
with a **proper reduction relation** giving the programs their semantics and the
**SMT tactic** discharging the arithmetic/decidable leaves. Grows toward simple
WASM programs (same shape, WASM step relation as the semantics).*

## Where we actually are (grounded)

- **Execution, not verification.** `covalence-lisp` proves `{defs} ⊢ program =
  value` for *closed, ground* programs (equational; `defun`-as-hypothesis for
  recursion). It's a *function* — needs a concrete value. No `∀`-reasoning.
- **A denotational island exists but is off to the side.** `init::lisp` defines
  `len`/`append` via the carved `sexpr` **recursor** and *already proves*
  `append_assoc` and `len_append` by structural induction (`carved.rs`,
  `lisp.rs:369-437`). But: it's recursor-functions (denotational, not an
  operational reduction relation), it isn't surfaced to a user tactic, and it
  touches **no** SMT.
- **No arithmetic in Lisp.** Numerals lower to raw-byte `atom`s; there is no
  `+`/`-`/`*`/`<`. So today there is *nothing arithmetic to hand to SMT*.
- **The SMT tactic is QF_UFLIA.** `goal_to_problem` (proof/alethe) translates
  `Bool` + `Int` + `TFree` uninterpreted sorts, the connectives, and `+ - * < <=`;
  free vars of base type become uninterpreted functions. It **rejects** arrows,
  binders, and *derived types* — so `sexpr` terms can't currently cross into SMT.
- **Induction is public.** `sexpr_inductive().induct(motive, cases)`
  (`carved.rs:873`, atom/snil/scons → `⊢ ∀s. P s`) and `nat_induct(base, step)`
  (`ext.rs:761`). Both usable from a tactic.

## The object we're missing: a proper reduction relation

The equational `⊢ input = output` can't express `∀`-specs or divergence. The
right semantics is a **small-step relation reified in HOL** — an inductive
predicate, built the way the CFG stratum builds `Derives` and the reified ladder
builds `Derivable_R` (impredicative least fixpoint):

```
Step a b   := ∀S. clauses(S) ⟹ S a b          -- one clause per reduction rule
Reduces a b := ∀R. (∀x. R x x)
                 ∧ (∀x y z. Step x y ⟹ R y z ⟹ R x z) ⟹ R a b   -- Step*
```

Clauses (grown incrementally): primitive `car/cdr/cons/if/cond`; integer ops on
literals; `defun`-unfold `(f ā) → body[ā]` (from the assumed equation); and
congruence (reduce a redex in context). `Reduces` is discharge-free / a genuine
least fixpoint, so it needs no new trusted rule — it rides the same machinery as
`Derives`.

Why a *relation* and not the recursor-functions: the program is what the user
**wrote** (`defun`), the relation gives it meaning **operationally**, divergence
is expressible, and `∀ inputs. Reduces(prog(inputs), r) ⟹ P` is a statable
theorem. (Recursor-functions stay useful as the denotational model to *validate*
the relation against.)

## The verification loop (where SMT lives)

```
∀x. P(x, f x)                Reduces(f(x), r)                VC: QF-LIA + UF
  spec       ──unfold the──►  symbolic value r    ──strip ∀──►  0≤x ⟹ x ≤ x+x  ──►  (#by smt)  ⊢
             relation                              +VC-gen                          refute_chain / Farkas
```

SMT is the **leaf discharger**. After unfolding the relation (and, for recursion,
applying induction), the residue is a quantifier-free arithmetic + UF goal —
exactly what `(#by smt)` / `refute_chain` handle.

## Staged plan

- **S0 — Lisp arithmetic → kernel `int`.** Add numerals + `+`/`-`/`*`/`<`/`<=`
  to the Lisp semantics, lowering to the kernel `int` theory the SMT tactic
  already speaks. (The `numeral-literals` branch has the numeral half.) *Without
  this there is no arithmetic for SMT to verify.*
- **S1 — the reduction relation.** `Step`/`Reduces` as above; minimal clause set
  first (defun-unfold + int ops + congruence, enough for straight-line
  arithmetic), reusing the CFG/`Derivable_R` fixpoint + soundness machinery.
- **S2 — spec surface + VC-gen.** State `∀ inputs. P`; symbolically evaluate the
  relation for the program's structure to emit the VC; `all_intro`/`imp_intro`
  the quantifiers/hypotheses away to a QF goal.
- **S3 — SMT discharge.** Point the VC at `refute_chain`/`(#by smt)`. Arithmetic
  VCs work today; broaden `goal_to_problem` to carry `sexpr` as an uninterpreted
  sort (+ `len`/`cons` as UF) for list VCs.
- **S4 — induction.** `sexpr_inductive().induct` / `nat_induct` to reduce
  `∀ recursive-input. P` to base+step; unfold under the IH; SMT the leaves.

## Milestones

1. **Straight-line arithmetic (S0-S3, no induction).**
   `(defun (f x) (+ x x))` ⊢ `∀x. 0 ≤ x ⟹ x ≤ (f x)`: `Reduces (f x) (x+x)`
   (one unfold), VC `0 ≤ x ⟹ x ≤ x+x` → `refute_chain`. The "hello world" — proves
   the spine (relation → VC → SMT) with nothing recursive.
2. **Recursive + induction (S4).** `(defun (sum n) (if (= n 0) 0 (+ n (sum (- n 1)))))`
   ⊢ a bound like `∀n. 0 ≤ (sum n)`, or a `len`/`append` arithmetic property —
   induction + SMT on the arithmetic leaves.
3. **WASM (later).** Same loop, the semantics being the WASM step relation
   (the CFG stratum already parses WASM binaries kernel-checked; a small-step
   `Step_wasm` is the analog of `Step_lisp`).

## First build

S0 (Lisp arithmetic) + a minimal S1 relation for straight-line programs, to land
milestone 1 end-to-end. Small-step (not big-step): it's the object that survives
divergence and is the honest operational semantics.
