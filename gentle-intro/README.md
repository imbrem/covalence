# Gentle Intro

This folder introduces the logical parts of the repo from the current code.

It describes the code that exists now, especially:

- [`crates/covalence-pure`](../crates/covalence-pure/)
- [`crates/covalence-hol`](../crates/covalence-hol/)
- [`crates/covalence-opentheory`](../crates/covalence-opentheory/)

It does two jobs:

1. a gentle explanation of what the current Pure and HOL code is doing
2. a translation of that code into Hehner `aPToP` and institution-theory
   language

These notes are about the **current tree**, not the target architecture in the
proposal docs.

The current repository has:

- `covalence-pure`, a live Pure-style framework crate
- `covalence-hol`, a live HOL-Light-shaped kernel crate
- proposal docs for a cleaner future factoring

Keep those levels separate. The code comes first.

## Reading order

1. [current-pure-and-hol.md](./current-pure-and-hol.md)
2. [hehner-and-institutions.md](./hehner-and-institutions.md)

## One-screen summary

The repo has three main logic-facing pieces:

- `covalence-pure`: a small Isabelle/Pure-shaped framework with meta-level
  implication, universal quantification, equality, and observation hooks
- `covalence-hol`: a separate HOL-Light-shaped arena kernel with the standard
  10 primitive inference rules plus definitions
- `covalence-opentheory`: a transport/import layer that drives `covalence-hol`

The Hehner lens separates:

- the **collection of assumptions/facts**
- the **packaged artifact** that stores or transports them

Institution theory separates:

- the **logic/framework**
- the **object logic**
- the **proof/package format**
- the **translation/import path**

Those separations are already visible in the code.
