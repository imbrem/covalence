# covalence-numerals skeletons

## Severe

- **`Wasm` backend is a stub** (`src/backend/wasm.rs`) — builds kernel terms
  (via `Symbolic`) but every `prove_*` returns `None`. The intended
  verified-WASM-trace certification path (run a trusted arithmetic component
  over the literal payloads, admit the output trace) is not wired.

## Minor

- **`ground_f32` enclosure certificate unproven** (`src/backend/symbolic.rs`,
  `src/lit.rs`) — `NumeralBackend::ground_f32` returns `FloatCert32::Unproven`
  for the kernel backends: there is no proof that the chosen `f32` bit pattern
  is the nearest representable float to the decimal (a rounding-enclosure
  `⊢ lo ≤ toRat d ≤ hi` around the two adjacent floats). No axiom is admitted;
  the theorem is simply left unproven. The kernel-free `RatBackend` computes the
  bits without a proof (`FloatCert32::Bits`).
- **`prove_to_rat` only covers the `Decimal` rung** (`src/backend/symbolic.rs`)
  — it discharges the proved `toRat (mkDec m k)` injection lemma. `Nat`/`Int`/
  `Rat` rungs have no `toRat` proof yet (they need the `int ↪ rat` / `nat ↪ int`
  embedding lemmas chained), so `prove_to_rat` returns `None` for them.
- **`prove_lt` only covers the `Nat` rung** (`src/backend/{symbolic,builtin}.rs`)
  — decided by `nat.lt` reduction. `Int`/`Decimal`/`Rat` ordering (via
  `int.lt` / cross-multiplied `rat.le`) is not implemented.
