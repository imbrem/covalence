# Skeletons — `covalence-init/src/peano`

Open work in the Peano-arithmetic deep embedding. See `CLAUDE.md` § Skeletons, the
[crate index](../../SKELETONS.md), and the [root index](../../../../../../SKELETONS.md).
Build plan:
[`notes/vibes/peano-arithmetic-plan.md`](../../../../../../notes/vibes/peano-arithmetic-plan.md).

## Severe

- **Derivation constructors for the quantifier/equality clauses** (specialise /
  induction / Leibniz / generalise). The closure clauses are present and proved
  sound, but constructing `⊢ Derivable_PA ⌜A⌝` *through* them (e.g. `∀x. x+0=x` by
  induction-on-derivations) is not landed. *Blocker:* the fold-level motive
  `Q:'t→'r` makes soundness automatic, but a concrete `q` mentioning the
  arithmetic handlers leaves them un-captured under `all_elim`; the naive
  "carrier-term motive" fix is **unsound** (breaks the soundness proof). The real
  fix parameterizes the motive over an explicit handler environment — a
  co-evolution of clause, soundness discharge, and constructor. Also needs the
  **propositional Hilbert schemas** (à la `prop.rs`) so the induction step is
  itself derivable (the 11 clauses have no deduction theorem / `⟹`-intro).
- **Headline `∀x. x+0=x` as a Metamath `$p` proof script.** The induction
  *mechanism* lands the headline via `mm_replay::induct_via_replay`; what is
  unauthored is the Hilbert-style `.mm` script deriving base + step inside
  `mm_pa`. *Blocker:* proper term-substitution `[t/x]ph` (`[/]` operator + `sb*`
  axioms + equality calculus + propositional schemas) is not in `mm_pa.rs` (kept
  minimal). The end-to-end `ax.mp` `.mm` proof is blocked the same way (currently
  exercised via `mp_via_replay` on real kernel theorems).

## Minor

- **`RuleSet`-from-`Database` / `#logic` correspondence.** Connecting a
  `metamath::Database` to the impredicative `metalogic` engine + the
  `∃ValidProof ⟺ Church-Derivable` equivalence — not built. Also tracked in
  `metalogic/SKELETONS.md`. North stars beyond: `S`-transport
  `Derivable_L1(A) ⟹ Derivable_L2(S(A))` and the two-direction
  `Metamath-PA ≅ our-PA` representation-equivalence metatheorem.
- **`LockstepDerivation` constructors.** Declared (a `Fol` + its `⊢ ⟦A⟧`) but has
  no constructors — secondary convenience path; add axiom/rule constructors if
  wanted. Primary path is `Derivable_PA` + `project`.
- **`.cov` surface (Phase C).** PA not exposed through the `.cov` script language.
  Missing elaborator features (also in `prop.cov`): a `(pa-induct …)`
  rule-induction tactic (`inst d := P` + `Closed P` discharge), and **β/η-aware
  `#concl` matching** for statements over a bound variable (every `∀x. …`).
