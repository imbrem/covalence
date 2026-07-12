-- Dialect THEOREMS whose statements are EQUATION expressions (not types),
-- with their proofs supplied SEPARATELY in `nat_theorems.proof` and linked by
-- name. See `notes/vibes/proof-format.md`.
--
-- A theorem states an equation in the same expression grammar a definition's
-- `lhs = rhs` uses; free variables are implicitly universally quantified and
-- ∀-closed by the typed backend into a HOL `Term : bool`. The proof file drives
-- the abstract `Hol` / `Nat` inference rules to build a `Thm` whose conclusion
-- is checked against the lowered statement.

-- Reflexivity: `∀a. a = a`. Proved by (refl a) then generalising `a`.
theorem refl_a. a == a

-- The left-unit recursion equation for `+`: `∀m. 0 + m = m`. This is exactly
-- the `Nat` accessor `add_base`, so the proof just cites it as a lemma.
theorem add_base_thm. 0 + m == m

-- A theorem with NO proof in the file — reported as an unproven HOLE, not an
-- error.
theorem add_comm_thm. a + b == b + a
