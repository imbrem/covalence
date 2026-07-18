+++
id = "N000D"
status = "draft"
review = "unreviewed"

[[contributions]]
role = "author"
actor = "agent:claude"
at = "2026-07-13T20:42:09+01:00"
source = "legacy"
agent = "claude"
harness = "claude"
+++

We have the following high-level goals:

- Get a full implementation of the K framework inside covalence -- especially:
  - The ability to define syntax and generate parsers as relations and as functions
  - The "simple matching fragment" -- with just constant reductions vs. symbolic reductions
  - The "full matching fragment"

We also want the following low-level atoms:
- natural literals:
  - binary digits + binary 0b
  - decimal
  - octal digits + octal 0o + zero-prefix
  - hexadecimal digits + hexadecimal 0x/0h
  - mixed (e.g. 0xABC and 123 and 0b101 as a single relation)
  - base{32, 58, 64} -- variants
  - binary: LEB128
  - binary: fixed width LE/BE
- integer literals:
  - nat + sign
  - fixed width from nat/int

In terms of semantics, we want to start building up subsets of WASM as we go towards the full thing
-- as well as subsets of SpecTec, e.g. for WASM's grammar.
