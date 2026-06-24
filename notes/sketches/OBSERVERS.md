# Observers & validators (raw sketch)

> Brainstorm behind `notes/observers.md`. The observer substrate
> (`Observer` + `ObsEq`/`ObsTrue`/`ObsImp`) exists in the kernel today; the
> validator / precondition layer below is still proposed.

Three metavariable layers (cf. Isabelle): Schemavars/types, Metavars/types,
Vars/types (the current logic). Goal: replace oracles with a "{given these
facts} ⊢ I see this fact" judgement.

## Observer

An observer asserts facts — it can say a thing is *true*, never *false*:

```rust
trait Observer { fn assert(&self, fact: Fact); }
```

`Γ ∪ observer ⊢ thing  ≡  Γ ∪ {facts…} ⊢ thing` (the observer stands for the
set of facts it asserts).

## Validator (trusted, per observer type)

Each extension to the core kernel is a **validator** — trusted *for one
observer type*. The observer (untrusted) takes arbitrary, possibly interactive
witnesses and asks its validator to:

- **Add a fact** — validator may reject. Policies range over: accept none;
  accept all of a fixed shape (e.g. `{a₁…aₙ} ⊢ myConst e = myConst' e'`); or
  **accept anyway and record it as a precondition** for anything not fully
  accepted.
- **Add a constant to the model** (`myNewConst : someType`) — e.g. efficient
  byte storage.

The validator can be queried for: the current model `M`, the current
preconditions `P`, and whether either is *frozen*. Invariant:
`precon(o) ⊢ P  ⟹  observer ⊢ P`. Trusted state is the tuple
`(M, P, mFrozen, pFrozen)`.

```
WITNESS ⟹ OBSERVER ⟹ VALIDATOR ⟹ FACTS (HOL model)
```

## Examples

- **Efficient bytes** — a validator presenting a constant per byte-vector plus
  constants for builtin catenation, len, …
- **Efficient nats** — analogous.

Validators compose: `V1 : O1`, `V2 : O2`, `(V1, V2) : (O1, O2)`.
