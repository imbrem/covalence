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
- **Symbolic-conclusion mechanism (`Thm<L, C>`): remaining float ops.**
  The additive `Thm<L, C = Val<Term>>` + `from_pure_sym` mechanism (EG1;
  `notes/vibes/literal-endgame-design.md`) covers **nat** (`nat_add`), **int**
  (`int_add`/`int_mul`/`int_neg`), **bytes** (`bytes_cat`/`bytes_len`) and now the
  bit-level **float** binaries (`f32.addBits`/`mulBits`, `f64.addBits`/`mulBits`)
  via symbolic landers in `covalence-hol-eval::tohol`. Landers transport the
  concrete family cert onto the symbolic `ToHol*` shape with the `ToHol*Val` reify
  rules + base `eq_mp`; float needed the two newly-admitted
  `ToHolF32Val`/`ToHolF64Val` reify rules (the ONLY EG2 base delta). Still open:
  the remaining float ops (`sub`/`div`/`min`/`max`/`copysign`, the unaries
  `sqrt`/`abs`/`neg`/rounding, comparisons, `promote`/`demote`/`truncSat`/`convert`)
  have no symbolic lander yet — recorded in `eval/SKELETONS.md`. Also open: the
  remaining HOL term formers (const/abs) as base ops.
- **`from_pure_sym` trusts the mint (no non-forcing floor).** It cannot re-run
  the concrete sequent floor (that would materialize the operand). A
  non-forcing decode — a `Term` skeleton typed at the declared `toHOL` sort
  without expanding — was the design's audit-cleanliness preference but is
  orphan-rule-blocked (a `SymConcl` trait would span core and base's `App`,
  neither local to eval where the `toHOL` shapes live). Soundness rests on
  `admits()` alone regardless (only sound cert rules mint an `IsThm`-headed
  prop); the never-materialize well-typedness is machine-checked in eval's
  `nat_add_symbolic` test.
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
