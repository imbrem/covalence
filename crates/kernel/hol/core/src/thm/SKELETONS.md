# Skeletons — covalence-core `thm/`

See the [crate index](../../SKELETONS.md). These are the `covalence-pure` mint-gate
future seams left open by the core-on-pure port.

## Minor

- **toHOL tier is one slice deep.** `crate::tohol` + the `raw`/`canon` sections of
  `rules::core_rules!` cover only nat.add (`ToHolNatVal`/`PairVal`/`NatAddCert`/
  `HolApp`). Open: `ToHolInt`/`ToHolBytes` unfolding + certificate rules, the
  permanent structural unfolding rules (`toHOL 0 = ⌜zero⌝`, `toHOL (n+1) =
  S (toHOL n)`, bytes cons), the per-family certs (NatArith/IntArith/Bytes/
  FixedWidth/LitEq/Coercion), and the remaining HOL term formers (const/abs).
- **`ToHolNatVal` is TRANSITIONAL.** It reifies to `Term::nat_lit` literals; at
  kernel-literal deletion it is deleted and the permanent structural rules take
  over (only the reify target flips; consumers don't move).
- **toHOL driver lives in `core::proofs`.** `nat_add_thm` + `reify_app` are
  untrusted and move to the dedicated `covalence-hol-eval` crate next stage.
- **No native pure-HOL embedding.** `IsThm` carries `(Ctx, Term)` as opaque `Val`
  leaves. Future: `HasTy` judgement Op; a native pure-HOL theory.
- **Builtins computation not offloaded to pure.** `ReducePrim` / `UnfoldTermSpec`
  keep the `builtins` evaluator in-TCB inside their `decide` (the toHOL cert path
  covers nat.add only so far). Re-route to the `covalence-pure-eval` `CanonRule`s
  as the per-family certs land; the legacy evaluator stays trusted until then.
- **`_with` interning is post-hoc.** The cons-aware `*_with` methods mint via the
  base rule (canonical build) then deep-intern the result conclusion into the
  caller's `TrustedCons` (`intern_concl`). This populates the cons table for
  downstream sharing but walks the conclusion twice on the `_with` path; a
  zero-extra-walk path would need cons threaded into `decide` (blocked: `decide`
  only sees `&CoreLang`, and a cons-generic rule would fragment the admit set).
- **No `Sigma<A, P>`.** A proof-carrying value (an `Expr<A>` bundled with a theorem
  about it) — deferred.
