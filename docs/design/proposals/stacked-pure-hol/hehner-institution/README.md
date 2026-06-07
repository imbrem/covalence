# Pure/HOL Through Hehner and Institution Theory

> **STATUS: EXPLANATORY COMPANION TO A PROPOSED STACK.**
>
> These notes restate the
> [stacked Pure + HOL MVP](../README.md)
> using two vocabularies:
>
> - Eric Hehner's [`aPToP`](https://www.cs.toronto.edu/~hehner/aPToP/) /
>   bunch-theory distinction between **collection** and **packaging**
> - the repo's existing
>   [institution-theoretic map](../../../../institution-map.md)

This subdirectory is for readers who already understand Covalence's broad
direction but want a sharper answer to:

1. What is the **Pure layer** if I think in Hehner's style?
2. What is the **HOL layer** if I think in institution theory?
3. How do these readings fit together without changing the actual design?

## Scope

These docs are intentionally narrow:

- They explain the **Pure** and **HOL** layers first.
- They only sketch later layers at the end.
- They are a **crosswalk**, not a replacement notation for the rest of the repo.

Two cautions matter:

- "Bunch theory" here means **Hehner's `aPToP` usage**, not BI / bunched logic.
- Covalence is **not** being refounded on Hehner's formal system wholesale. The
  bunch vocabulary is an explanatory lens for scoping, collection, and
  packaging.

## Reading Order

1. [00-crosswalk.md](./00-crosswalk.md) for the shared vocabulary.
2. [01-pure-layer.md](./01-pure-layer.md) for the Pure/LF reading.
3. [02-hol-layer.md](./02-hol-layer.md) for the HOL reading.
4. [03-next-layers.md](./03-next-layers.md) for the forward map.

## One-Screen Summary

| Covalence layer | Hehner / `aPToP` reading | Institution-theory reading |
|---|---|---|
| Pure | The disciplined place where we form expressions and reason from a **bunch of assumptions** without confusing that bunch with a packaged artifact. | A candidate **meta-institution**: signatures, sentences, and proof rules for hosting object logics. |
| HOL | The first major **packaged theory of truth-valued predicates** built over that framework. | The default **object institution** hosted over Pure. |
| Oracles / store / translations | Extra sources of facts, packaging, and transport that must remain explicitly scoped. | Theory extensions, transports, and institution morphisms around the core, not part of the core logic itself. |

The central alignment is this:

- Hehner helps explain **why we keep collections and packaged artifacts apart**.
- Institution theory helps explain **why we keep logic, theory, proof format, and translation apart**.

Those are the same architectural instinct applied at two different scales.
