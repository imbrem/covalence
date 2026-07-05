# Skeletons — covalence-core `thm/`

See the [crate index](../../SKELETONS.md). These are the `covalence-pure` mint-gate
future seams left open by the core-on-pure port.

## Minor

- **Permanent structural toHOL unfolding rules not yet admitted.**
  `ToHolNatZero`/`ToHolNatSucc`, `ToHolBytesNil`/`ToHolBytesCons`, `ToHolIntMk`
  land only at kernel-literal deletion: the `tohol_unfolding_rules_are_exclusive`
  guard (rules.rs) forbids co-admitting them with the transitional `*Val` rules
  (contradictory `toHOL` denotations at the `Term` sort). Same-commit swap.
- **The `*Val` rules + the family certs' `Lit::to_term` are TRANSITIONAL.**
  `ToHolNatVal`/`ToHolIntVal`/`ToHolBytesVal` and `certs::Lit::to_term` reify to
  kernel literals (`Term::nat_lit` & co.); at literal deletion only the reify
  target flips (consumers don't move).
- **Per-op symbolic certs cover nat.add only.** The never-materialize tier
  (`NatAddCert`-style symbolic conclusions) grows per-op rules as big-value use
  cases arrive; the per-family certs conclude the reified `CoreProp` shape.
  Also open: the remaining HOL term formers (const/abs) as base ops.
- **No native pure-HOL embedding.** `IsThm` carries `(Ctx, Term)` as opaque `Val`
  leaves. Future: `HasTy` judgement Op; a native pure-HOL theory.
- **`UnfoldTermSpec` survives to the defs re-home.** Sound definitional
  unfolding tied to `TermKind::Spec`; deletes with `TermKind::Spec` when the
  `defs/` catalogue re-homes as ordinary `define`d constants.
- **`_with` interning is post-hoc.** The cons-aware `*_with` methods mint via the
  base rule (canonical build) then deep-intern the result conclusion into the
  caller's `TrustedCons` (`intern_concl`). This populates the cons table for
  downstream sharing but walks the conclusion twice on the `_with` path; a
  zero-extra-walk path would need cons threaded into `decide` (blocked: `decide`
  only sees `&CoreLang`, and a cons-generic rule would fragment the admit set).
- **No `Sigma<A, P>`.** A proof-carrying value (an `Expr<A>` bundled with a theorem
  about it) — deferred.
