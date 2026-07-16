# covalence-hol-api — skeletons

- **Consumer migration not done.** The `Hol`/`Nat` traits + the end-to-end
  demo (`tests/through_the_api.rs`) landed, but no *real* external consumer is
  migrated onto them yet: `lang/haskell`, `proof/alethe`, `proof/egglog`,
  `server/core` still build terms via `covalence_core::Term`/`TermKind`
  directly. Migration order + the swap-the-backend argument:
  `notes/vibes/backend-decoupling.md`. Inventory: `bun scripts/backend-coupling.mjs`.
- **`HolOmega` is TYPE-only + on the REFLECTED rep.** `src/omega.rs` exposes the
  reflected HOL-ω *type* layer (`tyop_var`/`ty_app`/`ty_all` + kind/rank checking
  via `canon(KindOf/RankOf/RankLe)`), demoed in `tests/monad_omega.rs`. Two gaps:
  (1) `TyRep = TyC` is the base's *demo* flat rep, NOT the trusted `Hol::Type` —
  bridging a reflected HOL-ω type into a trusted kernel type/term is unbuilt and
  gated on the middle `TyInst` rule + the Homeier consistency proof (vs
  `SelectAx`/`bool`) before any higher-rank rule may enter `CORE_MANIFEST`
  (`notes/vibes/tcb-holomega-roadmap.md`). (2) No TERM layer: `HolOmega` builds
  and kind-checks types only; typing HOL-ω *terms* (a `return`/`bind` term of the
  polymorphic type) still needs the trusted bridge.
- **Trait family incomplete.** `Hol` + `Nat` + `Int` + `HolOmega` exist. Planned
  peers: `LinArith` (the Farkas proof primitives over `Int` — scale-nonneg,
  add-inequalities, integer-strengthen, closed-literal refute — consumed by
  `covalence-kernel-smt`; blocked on missing `int` lemmas, see
  `notes/vibes/logics/smt-import-architecture.md`), `Inductives` (declare type +
  recursor + induction, fronting `covalence_inductive::InductiveBackend`), and
  further theory traits (`List`/`Bool`) mirroring `Nat`/`Int`.
- **`SuccHol`/`SuccDischarger` are nat-only.** `src/succ.rs` lands the
  eval-TCB-free `succ`-tower `LinOrder` + [`Discharger`] (closes `5 ≤ 2` by pure
  induction; e2e in `kernel/smt/tests/succ_e2e.rs`). It carries **no negative
  literals**: `lit(n<0)` clamps to the `0` tower and `close` fails to refute a
  comparison it cannot express (never mints an unsound `⊢ ⊥`). A signed twin
  (a `succ`/`pred`-tower or object-level `int` order) is unbuilt.
- **`Hol` error type not associated.** Fixed to `covalence_core::Result`
  (inherited from the trait's origin in the inductive engine); a fully
  backend-agnostic surface makes `Error` an associated type. Deferred until a
  second backend needs a different error.
