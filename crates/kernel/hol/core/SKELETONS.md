# Skeletons — covalence-core

See [`CLAUDE.md`](../../../../CLAUDE.md) § Skeletons and the [root index](../../../../SKELETONS.md).

Module-local skeletons: [`src/thm/SKELETONS.md`](src/thm/SKELETONS.md) (the
`covalence-pure` mint-gate future seams).

## `defs/` residue — dies with the literal leaves (D3)

The term-op catalogue moved to `covalence-hol-eval::defs` (stage E2 of
`notes/vibes/handoff/defs-out-of-core.md`). What remains in `src/defs/` is the
**D3 transitional residue**: the spec machinery (`spec`/`symbol`/`canonical`/
`quotient`/`macros`/`helpers`/`sigs`) plus the structural TYPE chain the literal
leaves' `type_of` forces — `bits` (`u8`…`s512`), `int`, `bytes`, `unit` and
their carrier closure (`prod`/`coprod`/`option`/`list`/`stream`/`fail`/`cond`,
the `logic` connectives their bodies quantify with, and the residue term ops
`nat.{succ,pred,add,le,lt,rec}`/`iter`/`nil`/`cons`/`listFoldr`/`listLength`/
`finite` + stream accessors). It all leaves core when the literal
`TermKind::Nat/Int/SmallInt/Blob` variants die in favor of the lazy toHOL base
expressions (S10/S11); until then every remaining `defs/` file is this one
skeleton. (`hol.rs` builders and `logic.rs` stay for the same reason: the
connective/quantifier *rules* left the kernel in stage L2 — they are
`covalence-hol-eval::derived` derivations now — but the staying axiom rules
(`succ_inj`/`zero_ne_succ`/`select_ax`/`spec_ax`/`spec_rep_abs_*`/
`new_type_definition`) still *state* their conclusions with `imp`/`not`/`or`/
`exists`/`and`/`forall`, and the residue type bodies quantify with them, so the
*definitions* remain core residue until the literal-leaf endgame. Note the
derived rules live at the eval tier only: `⊢ T` has no `Thm<CoreLang>`
derivation while `T` is an undefined literal.)

## Hash-consing not on-by-default

`Ctx` has no owned interner, `hol.rs` builders construct plain, `TermInfo::Wf(Type)` cached
types are freshly allocated, and the script/init consumers do not thread a cons
(only the metamath replay path in `metalogic/mm_database.rs` does) — so replay
proofs still don't share one interner end-to-end. Making it on-by-default would
cut the ~29% allocation dominating the list-bootstrap profile. Soundness
unaffected either way.

## Name-only `subst::close` should move out of the TCB

`subst::close(t, name)` is a trusted construction convenience that doesn't belong
in the kernel (rules taking arbitrary theorem terms already use the type-aware
`close_var` / `subst_free` / `has_free_var_typed`). It remains only because many
`init/` construction sites in `covalence-init` call it. Eventually reimplement in
userspace (`TermExt`) or migrate the call sites to `close_var(&Var::new(...))`.
Deferred for call-site churn.

## `_with` rules intern post-hoc, not through construction

The cons-threaded `_with` rule variants build via the plain rule then
`intern_concl`/`intern_thm` (table-priming only — the returned theorem keeps its
own `Arc`s). The stranded 9d3673f9 design instead threaded `cons` through term
*construction* (`hol_and_with`-style builders in `hol.rs`), so the theorem itself
holds interned nodes. Pure perf nuance, no soundness role; revisit if profiles
show residual alloc churn on the replay paths.
