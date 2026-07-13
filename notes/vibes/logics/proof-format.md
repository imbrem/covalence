# A separate, name-linked proof format for the Haskell dialect

*Status: design + working prototype landed on branch `proof-format`
(`crates/lang/haskell`, `hol-typed` feature). Sibling of
[`init-in-dialect.md`](./init-in-dialect.md) and
[`backend-decoupling.md`](../observers/backend-decoupling.md).*

The dialect ([`init-in-dialect.md`](./init-in-dialect.md)) can already state and
lower **terms** — definitions like `map f x = bind x (\y -> ret (f y))` — into
real HOL through the `Hol`/`Nat` traits. This note adds the missing half: a way
to state **theorems** and supply their **proofs**, with the proofs living in a
**separate file** linked to the theorem **by name** and replayed through the
same abstract trait surface.

## The load-bearing idea: a theorem statement is an EQUATION, not a type

The single most important framing decision. A theorem's **statement is a
term-level equation / proposition**, written in the *same expression grammar* a
definition's `lhs = rhs` uses — e.g.

```
add (succ n) m == succ (add n m)
```

with free variables (`n`, `m`) implicitly universally quantified. It is **not**
a `::` type signature (`::` means "has type" — a different thing entirely).

This exposes a clean symmetry between the two kinds of top-level equation:

| Form        | Written as                | Meaning                                         |
|-------------|---------------------------|-------------------------------------------------|
| definition  | `f p… = rhs`              | an equation that **introduces** `f` as a *new* constant |
| theorem     | `theorem NAME. lhs == rhs` | an equation **proved** from what already exists |
| axiom       | `axiom NAME. lhs == rhs`   | an equation **postulated** (no proof)           |

Both are equations. Both lower through the typed backend into a HOL `Term`. A
definition's LHS head becomes a fresh constant; a theorem's equation is
∀-closed over its free variables into a proposition (`Term : bool`) that a proof
must conclude with. A future dialect module carries **both** definitions and
theorem-equations together, with the proofs supplied externally.

### The chosen surface syntax

```
theorem NAME. <equation>
axiom   NAME. <equation>
```

- `theorem` / `axiom` are new keywords; `NAME` is the link key.
- A `.` separates the name from the statement. `.` is otherwise unused in the
  dialect (no qualified names, no composition operator), so it does not collide
  with definitions (`=`) or type signatures (`::`), and does not read as a type.
- The `<equation>` is parsed with the **existing expression grammar** — `==` is
  the existing equality operator, so `0 + m == m` parses as the `BinOp("==", …)`
  a definition body could also contain. No new expression syntax.
- An optional preceding `NAME :: Ty` signature attaches (as it does for
  definitions) so a typed backend can type the statement's variables.

Lowering (`typed::lower_statement`): lower the equation expression to a `bool`
term through `Hol`/`Nat`, then ∀-close its implicitly-universal free variables
(sorted, deterministic order) into `∀…. lhs = rhs`. Which free variables are
quantified vs. left as ambient theory constants (`ret`, `bind`, …) is a
caller-supplied set — the theory signature stays free, the statement variables
get bound.

## The separate proof file (S-expression, keyed by name)

Proofs live in their **own file**, in the S-expression interchange format
(reusing [`crate::sexpr`](../../../crates/lang/haskell/src/sexpr.rs)). One
`(proof NAME step+)` form per theorem, matched to the dialect `theorem NAME` by
name:

```
(proof add_base_thm
  (lemma add_base))

(proof refl_a
  (refl (var a nat))
  (all-intro #1 a nat))
```

A **step** is a single inference-rule application over the `Hol`/`Nat` trait
methods. Steps are numbered `1, 2, …` in order; a step cites an earlier one with
the reference atom `#K`; the **last** step's theorem is the proof's result. The
prototype covers:

```
(refl term) (assume term) (lemma NAME)
(sym #K) (trans #J #K) (eq-mp #J #K) (beta-conv term)
(inst #K NAME term) (all-elim #K term) (all-intro #K NAME type)
(imp-intro #K term) (imp-elim #J #K)
```

with compact term / type sub-grammars (`(nat N)`, `(var NAME type)`,
`(app f x)`, `(+ a b)`, `(== a b)`; `nat`, `bool`, `(tvar N)`, `(-> a b)`) — all
built through the traits. `(lemma NAME)` cites a `Nat` accessor (`add_base`,
`add_comm`, …) or a prior dialect theorem from a name-keyed lemma table.

## The linker / checker

For each dialect `theorem NAME`:

1. lower its statement to a HOL proposition (∀-closed);
2. find `(proof NAME …)` in the proof file — **missing ⇒ an unproven HOLE**,
   reported, not fatal;
3. replay the proof through `H: Hol + Nat` to produce a real `Thm`;
4. check the produced conclusion **α-equals** the lowered statement. A wrong
   proof (valid derivation, wrong conclusion) or a replay failure ⇒ **rejected**
   (`Mismatch`); a match ⇒ **`Proved`** with the checked theorem.

An `axiom` declaration short-circuits to `Axiom` (no proof consulted).

α-equality is just the backend `Term`'s `PartialEq`: the native kernel's terms
are locally-nameless (de Bruijn `Abs`, no stored binder name), so structural
equality *is* α-equality and the quantifier's display name is irrelevant.

## Why this shape

- **Separate file, linked by name.** The statement is the stable interface; the
  proof is the swappable implementation — an interface/implementation split. A
  theorem's users depend on its *statement*, never its proof. This is also the
  "even a different format" the maintainer suggested: a proof can come from a
  third-party producer (or a future tactic engine) that emits the S-expr format
  and never touches Haskell syntax.
- **S-expressions.** Interchange-friendly, reuses the existing `sexpr` IR and
  reader/printer, and lets proofs be produced/consumed decoupled from replay
  (parse once, replay against any backend).
- **Replay through the `Hol`/`Nat` traits.** The replayer and linker name **no**
  backend type except through the `H: Hol + Nat` bound (verified: the only
  concrete `NativeHol` mention is where a caller picks `H`). Swapping the TCB is
  a trait-impl swap; the format, the replayer, and every proof are untouched.

## TCB story

**Zero TCB delta.** All new code is in the untrusted `covalence-haskell` crate
(dialect + a checker over the `Hol` trait). The checker trusts **only** the
`Hol` trait: each replay step is a genuine inference rule, so the produced `Thm`
is sound by construction (its private mint is unreachable from here), and the
linker's *sole* remaining obligation is the conclusion/statement α-check. The
trusted `covalence-core` / `-eval` manifests are byte-identical.

## Alternatives considered

- **Inline dialect tactics** (proof steps written in Haskell-ish syntax in the
  same file). Rejected for the prototype: it couples the statement surface to
  one proof language and loses the third-party-producer / interchange property.
  The separate S-expr file can still be *generated* from a future inline tactic
  language — they are not exclusive.
- **Reuse OpenTheory / Metamath** (`crates/proof/*`) as the proof format. Viable
  and complementary for *importing* external proofs; heavier than needed for a
  dialect-native format, and it would still be replayed through a trait surface.
  The name-linked S-expr format is the minimal native on-ramp.

## Prototype status (what is genuinely checked)

Landed and green (both `default` and `hol-typed` feature configs):

- `theorem` / `axiom` declarations parse (statement = equation expression);
- statement lowering ∀-closes free variables into a HOL `Term : bool`;
- the S-expr proof format parses; the replayer drives the trait rule methods;
- the linker reports `Proved` / `Axiom` / `Hole` / `Mismatch`.

End-to-end demo (`examples/nat_theorems.{hs,proof}`, `tests/proof_linker.rs`):
`refl_a` (`∀a. a = a`, via `refl` + `all-intro`) and `add_base_thm`
(`∀m. 0 + m = m`, via `(lemma add_base)`) are **genuinely checked** — the
produced `Thm`'s conclusion α-equals the lowered statement. `add_comm_thm` (no
proof in the file) is a **hole**. A deliberately wrong proof (proving `∀a. a = a`
against `add_base_thm`'s statement) is **rejected**.

## Deferred

- A richer / multi-step equational demo and the `monad.rs` `map_ret` proof
  (assume-left-id → instantiate → β-reduce → discharge) as a dialect theorem.
- A full tactic language (the S-expr steps are a low-level rule kernel; a
  higher-level tactic surface compiling to it is future work).
- Broader rule coverage (`exists_*`, `cong_app`, `false_elim`, rewriting) — the
  trait exposes them; the replayer wires a workable subset.
- Type inference for statement variables (the demo types all free variables as
  `nat`; there is no inference, matching the rest of the typed backend).
- Wiring the linker into a whole-module driver that walks a `ThmModule` +
  proof file and produces a proved/hole/rejected report per theorem.
