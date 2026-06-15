-- metatyvars

\alpha -- distinct from HOL types

-- first order derivation trees on this

{a1,...,an} |- conc

-- three layers:

- Schemavars/Schematypes (Isabelle)

- Metavars/Metatypes (HOL)

- Vars/Types (current logic)

-- how do we get rid of the oracles:

|> "i saw that"

{given these inputs} |> "i see this"

your metalogic: {given these facts} |> "i see this fact"

"fv a = \empty"

--

- observer: something which can assert facts

  observerIsConsistent |> whatTheObserverAsserts

Literally

```rust
trait Observer {
    // an observer can't say something is false, only that it's true!
    fn assert(&self, fact: Fact) {

    }
}
```

```
struct FactsIsAsserted {
  Vec<Fact>
}
```

```
\Gamma \cup observer |> thing
===
\Gamma \cup {facts...} |> thing
```

```
trait Validator<O : Observer> {
  fn register(fact: Fact) {
    ...
  }

  fn validate(facts: &Facts) -> bool {
    ...
  }
}
```

```
impl ITrustTheWasmSpec<MyTrustedWASMExecutor> {
  fn validate(facts: &Facts) {
    // you can assert that things following from the spec freely
  }

  fn substituteModel() {
    // ...
  }
}
```

```
impl ITrustTheBytesObserver<BytesSystem> {

}
```

```
impl BytesSystem {
  fn observe(&self) -> Facts {
    ...
  }
}
```

- (Observer [untrusted], Validator [trusted _for an observer type_])

- The user gives arbitrary, potentially interactive witnesses to the observer

- The observer can ask the validator to:

  - Add a fact (validator may reject)

    - Accept no facts

    - Accept all facts as long as they're of the form {a1,...,an} |- myOwnedConst e = myOwnedConst' e'

    - For any fact that we don't _fully_ accept -- accept it anyways and add it to our _precondition_

  - Add a constant to the model (myNewConst : someArbitraryType)

    - Efficient byte storage is

  - The validator (trusted) can be asked for:

    - The current model

    - The current preconditions

    - Whether the model or the preconditions are _frozen_

      - You can always go: precon(o) |- P => observer |- P

    - (M, P, mFrozen, pFrozen) trusted V

WITNESS ==> OBSERVER ==> VALIDATOR ==> FACTS (hol model)

Each extension to the core kernel is a _validator_

- Efficient bytes is a validator presenting a constant for each bytevector
  - constants for builtin byte catenation, len, etc.

- Efficient nats is ...
  - constants for ...

- V1: O1, V2: O2, (V1, V2) : (O1, O2)
