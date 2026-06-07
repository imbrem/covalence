# Gentle Intro

This folder is a **current-code-oriented** introduction to the logical parts of
the repo.

It is intentionally not a proposal document. It describes the code that exists
today, especially:

- [`crates/covalence-pure`](../crates/covalence-pure/)
- [`crates/covalence-hol`](../crates/covalence-hol/)
- [`crates/covalence-opentheory`](../crates/covalence-opentheory/)

The goal is to give a reader two things at once:

1. a gentle explanation of what the current Pure and HOL code is doing
2. a translation of that code into Hehner `aPToP` and institution-theory
   language

## Important scope note

These notes are about the **current tree**, not the fully-adopted target
architecture.

That distinction matters because the current repository has:

- a live `covalence-pure` crate that already looks like a Pure-style framework
- a separate live `covalence-hol` crate that is still its own HOL-Light-shaped
  kernel
- proposal documents that describe a future tighter Pure-over-HOL or HOL-over-
  Pure factoring, but that factoring is not yet the current architecture

So the right current-code summary is:

- `covalence-pure` and `covalence-hol` are both real code today
- they are **conceptually related**
- they are **not yet the one settled stacked kernel architecture**

## Reading order

1. [current-pure-and-hol.md](./current-pure-and-hol.md)
2. [hehner-and-institutions.md](./hehner-and-institutions.md)

## One-screen summary

Today the repo has at least three logic-facing pieces in play:

- `covalence-pure`: a small Isabelle/Pure-shaped framework with meta-level
  implication, universal quantification, equality, and observation hooks
- `covalence-hol`: a separate HOL-Light-shaped arena kernel with the standard
  10 primitive inference rules plus definitions
- `covalence-opentheory`: a transport/import layer that drives `covalence-hol`

The Hehner lens is useful here because it helps separate:

- the **collection of assumptions/facts**
- the **packaged artifact** that stores or transports them

Institution theory is useful here because it helps separate:

- the **logic/framework**
- the **object logic**
- the **proof/package format**
- the **translation/import path**

Those separations are already visible in the current code even though the final
architecture is still in motion.
