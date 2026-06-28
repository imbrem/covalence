# Skeletons — covalence-acset

## Minor

- **Only Δ (pullback) migration.** `Instance::pullback` implements the
  pullback functor `Δ_F`. The left/right adjoints **Σ_F / Π_F** (the other two
  functorial-data-migration operations) are not implemented.
- **Pullback skips attributes.** `pullback` migrates objects and morphisms but
  not attribute columns, so a migrated instance over a schema with attributes is
  attribute-undefined. Add an attribute map to the `Functor`.
- **String-only attribute values.** Attribute values are `String`; there is no
  typed `AttrVal` (int / bytes / hash). Equality (injectivity) is string
  equality.
- **Compile-time names only.** Objects/morphisms/attributes are `&'static str`,
  so schemas are static. Dynamic / runtime-loaded schemas would need owned
  names.
- **No limits/colimits or schema composition.** Pure instance machinery — no
  query (conjunctive-query) layer, no schema colimits, no validation of
  acyclicity as a schema-level law (it is an instance-level check the caller
  invokes).
