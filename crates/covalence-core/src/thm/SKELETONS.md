# Skeletons — covalence-core `thm/`

See the [crate index](../../SKELETONS.md). These are the `covalence-pure` mint-gate
future seams left open by the core-on-pure port (`thm/lang.rs`).

## Severe

- **Soundness is NOT yet admits-only — it rests on the private-field barrier.**
  `MintRule::decide` is a rubber-stamp: it stamps `IsThm(Γ, φ)` for *any* well-typed
  `(Γ, φ)`, so it is not a sound rule (a sound admitted rule yields a true conclusion
  on *every* input). Under admits-only semantics `pure::Thm<CoreLang, IsThm(Γ,φ)>` is
  thus derivable for any well-typed `(Γ,φ)` — vacuous. What actually prevents a forged
  `core::Thm` today is the **private newtype field** (only core's rule methods reach
  `build`), i.e. visibility, plus core's ~55 rule methods being the sole callers. The
  admits-only milestone (soundness carried by `admits()` alone, nameability
  irrelevant): replace the catch-all `MintRule` with the **actual HOL inference steps
  as sound `Rule<CoreLang>`s** — each `decide` takes premise `pure::Thm`s and derives
  its conclusion, so every firing on any input is true — with per-rule `RuleRecord`s
  so the manifest enumerates each HOL rule. `thm/lang.rs`.

## Minor
- **No native pure-HOL embedding.** `IsThm` carries `(Ctx, Term)` as opaque `Val`
  leaves. Future: `HasTy` judgement Op; a native pure-HOL theory; `NatToHol:
  Op<In=Nat,Out=Hol>` + `CanonRule`/`Rewrite` reductions (e.g.
  `NatToHol(Add(n,m)) => HolApp(HolAdd(NatToHol n, NatToHol m))`) — added as extra
  admitted rules alongside `MintRule`, MintRule path untouched.
- **Builtins computation not offloaded to pure.** `builtins::eval_prim`/`PRIM_TABLE`
  still compute in core; offload to `CanonRule` impls admitted by `CoreLang` (the
  `Evaluate` seam) once it lands.
- **No `Sigma<A, P>`.** A proof-carrying value (an `Expr<A>` bundled with a theorem
  about it) — deferred.
