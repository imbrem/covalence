# covalence-opentheory — SKELETONS

Open work only. Severe first.

## Minor

- **`.int` interpretation files parsed but not applied**
  (`resolve.rs::apply_interpretation`). Umbrella packages that rename
  types/constants across a dependency (e.g. `word`→`byte`) rely on deep NameId
  renaming of theorem terms, which is not yet implemented, so such packages
  may over-report assumptions. Does not affect `base` (verifies whole).

- **Offline vendored corpus is a subset.** `assets/opentheory/gilith/std/` is
  missing a few base packages, so `list`/`natural`/`base`/… need the online
  path (`bun run opentheory`, which fetches + caches). Verified offline today:
  ~20 packages. Vendor the rest if a fully-offline `base` is wanted.
