# covalence-grammar skeletons

## Minor

- **Numeral atom zoo deferred** (`src/numeral.rs`) — only dec/oct/hex/bin
  radices ship. base32 / base58 / base64 alphabets and the LEB128 varint
  encoding (the "atom zoo") are not implemented; add them as further
  `digit_class`/`Numeral`-style families with their own accept/deparse.
- **Numeral grammars are description-only** (`src/numeral.rs`) — each family
  exposes a `Regex<char>` artifact, but recognition uses hand-written
  recursive-descent `parse` fns (this crate ships no regex matcher). A regex
  engine driving the grammars directly (so the `Regex` *is* the acceptor) is
  future work.
- **Spec numeral slips** (`src/numeral.rs` tests) — the numeral-literals-api
  spec writes the binary form of 2748 as `0b101011111100` (= 2812) and
  `1.5e3 -> Decimal(15000,0)` (= 15000 ≠ 1500). Tests use the
  arithmetically-correct forms (`0b101010111100`, `1500`); reconcile the spec
  figures when the kernel `mkDec` builder lands (see covalence-types SKELETONS).
