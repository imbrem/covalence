# covalence-types skeletons

## Minor

- **`Decimal::from_parts` spec discrepancy** — the numeral-literals-api spec
  writes `1.5e3 -> Decimal(15000, 0)`, which denotes `15000 ≠ 1.5e3`. We
  implement the arithmetically-correct value (`m = 1500, k = 0`) to keep
  `to_rat` sound; reconcile the spec figure (or add the intended alternate
  normal form) when the numeral grammar / kernel `mkDec` builder lands.
