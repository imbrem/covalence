# OpenTheory articles

Layout:

```
assets/opentheory/
  *.art           # original test articles (this repo)
  gilith/         # vendored from opentheory.gilith.com
    std/
    axiom-*-1.0/
    bool-def-*-1.0/
    unit-*-1.0/
```

Each subdirectory holds the articles downloaded from a single upstream
source. Add a new sibling (e.g. `cakeml/`, `hol-light/`) when vendoring
from a different source so the provenance stays clear.

## Original (covered by the repo's `0BSD OR CC0-1.0` license)

Hand-written minimal articles used as kernel and interpreter test
fixtures. They exercise individual stack-machine commands and are
heavily commented with the expected trace.

| Path | Purpose |
|---|---|
| `assume.art` | proves `{p} \|- p` — `assume` command |
| `beta.art`   | β-reduction smoke test |
| `refl.art`   | proves `\|- x = x` — `refl` command |

## `gilith/` — vendored from opentheory.gilith.com

Mirrored from <https://opentheory.gilith.com/> (Joe Leslie-Hurd). Do not
edit in place; refresh from upstream when bumping versions.

- `gilith/std/` — the `std` package tree (axioms, base, bool, byte,
  function, list, …) in the combined article format.
- `gilith/{axiom,bool-def,unit}-*-1.0/` — individual package directories
  pulled in at the versions named in the directory.

**License (upstream):** OpenTheory does not publish an explicit license
on <https://www.gilith.com/opentheory/> or
<https://opentheory.gilith.com/>. We treat these articles as
**third-party content with license-to-be-confirmed** rather than as
code contributed to this repository — the repo-level `0BSD OR CC0-1.0`
grant in [`../../CONTRIBUTING.md`](../../CONTRIBUTING.md) does **not**
extend to them. If you depend on these articles for downstream
redistribution, confirm terms with the upstream maintainer first.

### Refresh procedure

Articles are produced with the `opentheory` CLI from gilith.com. The
typical incantation for a stdlib package:

```sh
cd assets/opentheory/gilith
opentheory info --article <pkg>-<ver> > <pkg>-<ver>/<pkg>.art
```

After refreshing, re-run `cargo test -p covalence-opentheory`.
