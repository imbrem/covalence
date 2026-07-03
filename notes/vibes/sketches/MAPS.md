# Theory maps / interpretation transport (raw sketch)

> Notes behind `notes/vibes/metatheory.md`'s "two pillars": derivation-soundness +
> theory transport across PA/HOL/ZFC, with WASM/Isabelle as oracle frontends.

(
theory of peano arithmetic
)

(
theory of PA _derivations_
)

- Prove PA is sound under standard denotation: if \exists derivation, then true

- Expose LCF style API for building derivations in some system Thry _in_ our HOL

- HOL(A); PA(A); ZFC(A)

- PA(A) => HOL(A) => ZFC(A)

- WASM(P, D, A) => \exists D' . ZFC(D', A)

- Isabelle[THRY](A) => THRY(A)

- GT3(A) -- locale stuff, context stuff, ...

- Nat -> ZFSet
