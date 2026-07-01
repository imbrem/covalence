# Skeletons — covalence-core `thm/`

See the [crate index](../../SKELETONS.md). These are the `covalence-pure` mint-gate
future seams left open by the core-on-pure port.

## Minor

- **No native pure-HOL embedding.** `IsThm` carries `(Ctx, Term)` as opaque `Val`
  leaves. Future: `HasTy` judgement Op; a native pure-HOL theory; `NatToHol:
  Op<In=Nat,Out=Hol>` + `CanonRule`/`Rewrite` reductions (e.g.
  `NatToHol(Add(n,m)) => HolApp(HolAdd(NatToHol n, NatToHol m))`) — added as extra
  admitted rules in `rules::core_rules!`.
- **Builtins computation not offloaded to pure.** `ReducePrim` / `UnfoldTermSpec`
  keep the `builtins` evaluator in-TCB inside their `decide`. Offload to `CanonRule`
  impls admitted by `CoreLang` (the `Evaluate` seam) once it lands — distinct from
  the admitted-rule surface; the evaluator stays trusted for now.
- **`_with` interning is post-hoc.** The cons-aware `*_with` methods mint via the
  base rule (canonical build) then deep-intern the result conclusion into the
  caller's `TrustedCons` (`intern_concl`). This populates the cons table for
  downstream sharing but walks the conclusion twice on the `_with` path; a
  zero-extra-walk path would need cons threaded into `decide` (blocked: `decide`
  only sees `&CoreLang`, and a cons-generic rule would fragment the admit set).
- **No `Sigma<A, P>`.** A proof-carrying value (an `Expr<A>` bundled with a theorem
  about it) — deferred.
