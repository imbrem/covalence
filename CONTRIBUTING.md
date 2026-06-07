# Contributing to Covalence

Covalence is offered to the public domain to the maximum extent legally
possible. The default license is the [BSD Zero Clause License](./LICENSE)
(`0BSD`); a [CC0 1.0 Universal](./LICENSE-CC0) public-domain dedication
is also offered as an alternative (`CC0-1.0`). Downstream users may pick
either — the SPDX expression is `0BSD OR CC0-1.0`.

## Inbound = outbound

By submitting a contribution (pull request, patch, issue attachment,
commit, etc.) you agree that your contribution is licensed under **both**
`0BSD` **and** `CC0-1.0`, matching the project's outbound license. You
retain copyright in your contribution; you are only granting these
licences.

If you cannot make this grant for some part of a change (for example
because your employer holds rights that have not been cleared), do not
submit that part.

No CLA, no DCO sign-off, no copyright reassignment — submitting the PR
*is* the grant.

## Vendored third-party code

Code or data copied in from an external project is **not** subject to the
inbound-grant above. It keeps its upstream license. When vendoring:

1. Place the files under a clearly-scoped subdirectory (e.g. inside
   `assets/<source>/`, `crates/<crate>/vendor/`, or similar).
2. Add a short `README.md` next to the files recording:
   - upstream repository URL,
   - pinned commit / version,
   - the SPDX license identifier of the upstream code,
   - refresh procedure if applicable.
3. Include the upstream `LICENSE` file verbatim in the same directory
   when the upstream license requires it (BSD, MIT, Apache, MPL, …).
   `0BSD`/`CC0-1.0`/public-domain upstreams do not require this but it
   is still nice to include.
4. Do not modify vendored files in-place beyond what's necessary; record
   any patches separately so they can be re-applied on refresh.

See [`assets/spectec/README.md`](./assets/spectec/README.md) for a
worked example (BSD-3-Clause-licensed corpus vendored from
`Wasm-DSL/spectec`).

## File-level SPDX headers

New source files **may** carry an SPDX header to make automated scanners
happy:

```
// SPDX-License-Identifier: 0BSD OR CC0-1.0
```

This is encouraged but not required — the root `LICENSE` files already
cover the whole tree.

## Questions

Open an issue if anything about the licensing setup is unclear before
you contribute.
