+++
id = "N005F"
status = "draft"
review = "unreviewed"
[[contributions]]
role = "author"
actor = "agent:gpt-5.6-sol"
at = "2026-07-20T00:00:00+01:00"
source = "repository-snapshot-cd384d36"
agent = "gpt-5.6-sol"
harness = "codex"
+++

# SMT and SAT at `cd384d36`

## SAT

Implemented: generic lowering/backend/replay traits, HOL and sequent clause
backends, genuine RUP reconstruction from LRAT antecedents, DIMACS/LRAT format
integration, CaDiCaL/sequent end-to-end tests, and an UNSAT example.

Open: RAT steps, hint-free DRAT, further interning, exact empty-clause
accounting, and the intended first-class bitvector/bitblasting API.

## SMT

Implemented: exact rational linear combinations, a backend-independent Farkas
checker for an Alethe `la_generic`-shaped fragment, rule policies, and initial
chain/cycle replay. The older `crates/proof/alethe` remains the working concrete
HOL bridge.

Open: generic Alethe dispatch, target-Int term normalization, general
scale-and-sum replay, more linear-arithmetic rules, and coefficients beyond
`i128`.

## Substrate role

Solver proofs are ideal untrusted DBs. Clause/antecedent and linear-combination
tables can be filtered by trusted joins and replay, retaining only checked
conclusions. SAT stresses millions of narrow rows; SMT stresses typed exact
numeric columns and proof-policy scopes.

