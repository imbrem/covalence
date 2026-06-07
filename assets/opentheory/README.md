# OpenTheory articles

This directory mixes **original** test articles written for Covalence
with **vendored** content mirrored from upstream OpenTheory packages.

## Original (covered by the repo's `0BSD OR CC0-1.0` license)

Hand-written minimal articles used as kernel and interpreter test
fixtures. They exercise individual stack-machine commands and are
heavily commented with the expected trace.

| Path | Purpose |
|---|---|
| `assume.art` | proves `{p} \|- p` — `assume` command |
| `beta.art`   | β-reduction smoke test |
| `refl.art`   | proves `\|- x = x` — `refl` command |

## Vendored from upstream OpenTheory

Mirrored from <https://opentheory.gilith.com/> (Joe Leslie-Hurd). Do not
edit in place; refresh from upstream when bumping versions.

- `std/` — the `std` package tree (axioms, base, bool, byte, function,
  list, …), as published by upstream.
- `axiom-*-1.0/`, `bool-def-*-1.0/`, `unit-*-1.0/` — individual package
  directories pulled in at the versions named in the directory.

**License (upstream):** OpenTheory does not publish an explicit license
on <https://www.gilith.com/opentheory/> or
<https://opentheory.gilith.com/>. We treat the articles as **third-party
content with license-to-be-confirmed** rather than as code contributed
to this repository — the repo-level `0BSD OR CC0-1.0` grant in
[`../../CONTRIBUTING.md`](../../CONTRIBUTING.md) does **not** extend to
them. If you depend on these articles for downstream redistribution,
confirm terms with the upstream maintainer first.

## Refresh procedure

Articles are produced with the `opentheory` CLI from gilith.com. The
typical incantation for a stdlib package:

```sh
opentheory info --article <package-name>-<version> > <package-name>-<version>/<package-name>.art
```

After refreshing, record the upstream commit / package version next to
the file and re-run `cargo test -p covalence-opentheory`.
