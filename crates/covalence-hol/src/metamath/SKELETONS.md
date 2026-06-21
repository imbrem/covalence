# Skeletons — `covalence-hol::metamath`

Intentional placeholders and deferred work in the Metamath **substitution
engine** (the expression model, substitution, frame/database model, and RPN
proof checker). The `.mm` *reader* deferrals (compressed proofs, `$[ $]`
inclusion, `set.mm` scale) live in the separate `covalence-metamath` crate's
[`SKELETONS.md`](../../../covalence-metamath/SKELETONS.md). See the repo
[`CLAUDE.md`](../../../../CLAUDE.md) § Skeletons for the policy.

## Deferred features (north stars)

- **The `#logic` / `Derivable_L` / `S`-transport correspondence layer.** The
  point of housing this engine in `covalence-hol`: a Metamath database *is* a
  logic (`docs/theories-models-and-logics.md` §5.6, `docs/surface-compiler.md`
  §3.0.5) — axioms and rules as substitution schemas. The layer that turns a
  [`Database`](./database.rs) into a first-class Covalence `#logic` (with a
  `Derivable_L` judgement and the `S`-transport correspondence into our HOL /
  locally-nameless syntax) is **not built yet**. This is the next phase, after
  the relocation here and after the PA deep embedding (`src/peano/`) lands.
  Nothing in this module wires `#logic` today — it is a pure, theory-agnostic
  checker.

- **`covalence-hol` import tactic + representation-equivalence metatheorem.** A
  bridge that **replays** an (untrusted) Metamath proof and **kernel-rechecks**
  it — the same untrusted-frontend → kernel-recheck pattern as
  `covalence-alethe`. **A first concrete instance now exists for PA**:
  `peano/mm_pa.rs` (the PA database) + `peano/mm_replay.rs` (the
  `∃P.ValidProof ⟹ ⊢⟦S⟧` replay) re-derive every PA proof step in the kernel
  (axioms → `init::nat`, MP → `imp_elim`, gen → `all_intro`, induction →
  `Thm::nat_induct` on the concrete denoted motive). The **general,
  theory-agnostic** import tactic and the **representation-equivalence
  metatheorem** ("Metamath-PA ≡ our PA", relating the Metamath representation to
  our locally-nameless syntax) remain future work — the PA replay is a worked
  instance, not yet the generic layer. The engine here stays independent of the
  HOL kernel rules.

- **Structured-tree (grammar-parsed) expression encoding.** Expressions are
  encoded as *faithful flat sequences* (`[typecode, sym, sym, ...]` `SExpr`
  lists) — see [`mod.rs`](./mod.rs) for the rationale. A grammar pass turning
  those flat lists into structured trees (`(-> ph ps)`) would be nicer for the
  metatheory work above, but reintroduces grammar ambiguity and is therefore
  deferred to the bridge layer, where the grammar is part of the (untrusted)
  representation, not the checker.

- **`set.mm` scale & performance.** The model uses `String` symbols and
  `HashMap` label/symbol tables with no interning or arenas — fine for the
  hand-encoded example theories, not for the ~40 MB `set.mm`. Symbol interning,
  a flat statement arena, and incremental construction are deferred. (The
  reader-side performance concerns are tracked in the `covalence-metamath`
  crate.)

## Notes

- No `unsafe` (project rule).
- The checker performs **genuine** checking: substitutions, typecodes, and `$d`
  distinct-variable conditions are all re-derived and re-verified
  ([`verify.rs`](./verify.rs)); the inline unit tests cover the expression and
  substitution core. End-to-end theory tests (good + bad proofs across four
  hand-encoded theories) drive the engine through the reader and live in
  `covalence-metamath/tests/theories.rs`.
