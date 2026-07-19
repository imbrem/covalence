+++
id = "N0016"
status = "draft"
review = "unreviewed"

[[contributions]]
role = "author"
actor = "agent:claude"
at = "2026-07-13T21:25:20+01:00"
source = "legacy"
agent = "claude"
harness = "claude"
+++

# Numeral-literal API: grammars, digit/decimal types, and a generic backend trait

Status: design note (vibes). Companions: [`literal-endgame-design.md`](./literal-endgame-design.md),
[`eg5-preflight.md`](./eg5-preflight.md), the parsing plan
[`../../lisp/initial-ideas/parsing-relations.md`](../../lisp/initial-ideas/parsing-relations.md),
and the three-axis reduction design
[`../../lisp/initial-ideas/parametric-reduction.md`](../../lisp/initial-ideas/parametric-reduction.md)
which this mirrors for literals.

The user's five questions, then the target design, then a fan-out plan.

---

## Part 1 — Answers (what exists today, cited)

Citations are `report:field` / `file:line` drawn from recon reports A (kernel repr), B
(grammars/parsing), C (numeric types).

### Q1 — Is there a grammar with full support for `0xABC` and `12423`, built compositionally from decimal-digit / hex-digit / hex-integer grammars?

**No — neither the surface parsing nor a compositional numeral grammar exists.** What
exists is the *raw material*, not the numerals:

- `covalence-grammar` ships a full generic regex algebra `Regex<A>` (`Lit`, `Class`,
  `Concat`, `Alt`, `Star`, `Plus`, `Opt`, `Rep`) over any alphabet, plus `parse_regex` /
  `parse_regex_u8` surface parsers with `[...]` classes, `|`, `{n,m}`, escapes
  (report B, `regex.rs:1-1469`). You *can compose today* e.g.
  `Concat([Lit('0'), Lit('x'), Plus(hexdigits)])` and `Alt([decimal, hex, binary])`
  (report B answers, "Examples that compile today"). But these are **syntax-only DFAs** —
  there is no numeric *value lifting* (`0xFF → 255`); "Numeric interpretation must be
  implemented above" (report B answers).
- No literal frontend parses `0xABC` at all. The only decimal path is Forsp's
  `s.parse::<i32>()` (report B, `forsp/src/read.rs:144`), and it is i32-only. S-expr atoms
  keep numbers as `Atom::Symbol(SmolStr)` — `"42"`, `"0xFF"`, `"0b101"` are all plain
  symbols (report B, `sexp/src/types.rs:14-22`). Hex is only recognized as 64-char content
  hashes (`O256::from_hex`), never as a numeric literal (report B answers).
- At the *kernel* level there is decimal-only string parsing via `Nat::from_str` and a
  radix-parametric `Nat::from_str_radix(text, radix: u32)` for radix 2..=36
  (report A, `nat.rs:33-37,164-166`; report C). And there are HOL-level positional parsers
  `parseNatR : string → option(nat × string)` built on a `nat_of_digits` left fold
  (report A, `init/nat_parse.rs:14-36`). These are values-only: **radix is discarded at
  the parse boundary** — `12423`, `0x308F`, `0b…` all collapse to the same `Nat(2747…)`
  and are indistinguishable in the kernel (report A, "Base/Radix survival"; report B
  what_is_missing "Multi-radix agnostic parser").

So: the *ingredients* for a compositional grammar are present (regex algebra + relation
calculus `compose/join/meet/transpose` in `rel.rs`), and the plan
[`parsing-relations.md`](../../lisp/initial-ideas/parsing-relations.md) sketches exactly
the compositional pipeline (`ParseNat_dec`, `ParseNat_hex`, mixed via `∪`, deparse via
transpose). **None of it is built.** (report B what_is_missing.)

### Q2 — Are there TYPES for octal / decimal / hexadecimal digits?

**No.** "No `OctalDigit`, `DecimalDigit`, or `HexDigit` types exist. Unified parametric
parsing via `Nat::from_str_radix(text, radix)` for radix 2-36" (report C answers,
`nat.rs:33-37`). Digits are `char`/`u8` filtered through a range class; there is no
kernel or Rust type carrying "this is a base-16 digit in 0..=15".

### Q3 — Is there support for lowering fractions (`a/b`) and scientific notation (`1.5e3`) to rationals?

**Partially, at the value level; not at the surface.**

- A full `Rat` type exists — Grothendieck quotient `(int × int.pos)/~` by cross-mult, with
  ring ops on representatives and cross-mult comparison (report C, `rat.rs`). So a fraction
  *value* `a/b` has a home.
- Float parsing already produces an **exact rational**: `floatval := int × int` denoting
  `m · 10^e`, assembled as `±(ip·10^k + fr) · 10^(ex−k)` (report A, `float_parse.rs:19-59,
  222-226`; report C). Scientific notation's `e3` is exactly the `10^e` exponent — so
  `1.5e3` is representable as `(15, 2)` = `15·10^2`.
- But there is **no surface parser** for `3/4` or `1.5e3` (report B what_is_missing:
  "Rational/fraction (3/4) parsing", "Floating-point (1.5, 1.5e3, scientific) parsing"),
  and "No explicit fraction+scientific notation lowering API (chains parse→floatval→
  reduce)" (report C what_is_missing). The lowering exists as scattered value plumbing, not
  as a callable literal API.

### Q4 — Is there an explicit type for POSITIVE decimals and for arbitrary (finite) decimals, distinct from general rationals?

**No.** "No `FiniteDecimal` or `PositiveDecimal` types; all decimals lower to general
`Rat`" (report C summary + what_is_missing). Finite decimals *are* exact rationals of the
special shape `n / 10^k`, but that shape is not reified as its own type — it is immediately
collapsed into `Rat`, losing the "denominator is a power of ten" invariant.

### Q5 — How are float literals grounded today, and could a proper decimal-literal theory ground float parsing more strictly?

**Today floats are grounded only as opaque IEEE bit-patterns; the decimal→f32 rounding is
un-proved and deferred.**

- A float literal never enters the kernel as a float. `F32::new(x).to_bits()` gives a
  `u32`, materialized as `Term::u32_lit(bits)` (report A, `rules.rs:257-260`); the kernel
  sees only `0x3FC0_0000`, never "1.5" (report A, "FOR f32"). Float *semantics* are pure
  bit-op `CanonRule`s (`F32Add`, `F32Mul`, … `float.rs:260-275`), dispatched by `ptr_id()`
  under the `Float` family (report C, `certs.rs:70-87`).
- The reify rules `ToHolF32Val`/`ToHolF64Val` stay as unstructured toHOL **leaves** post-
  EG5 — floats never get `Zero`/`Succ` structure (report A EG5; `eg5-preflight.md:25,119`).
- The gap: parsing yields an *exact* decimal `(m, e)`, but "conversion to canonical IEEE
  f32/f64 with grounded correctness proof is DEFERRED" (report A what_is_missing;
  `float_parse.rs:24-25`). There is **no proof** that `f32::from_str("1.5")` returns the
  correctly-rounded bit pattern — we trust Rust's parser.

**Yes, a strict decimal theory would ground it.** If `1.5` first becomes a
`Decimal = 15 / 10^1` kernel value (exact, no rounding), then "round to f32" becomes a
*checkable* relation: pick candidate bits `b`, and prove the **enclosure**
`f32_pred(b) ≤ Decimal < f32_succ(b)` (or the round-to-nearest-even tie rule) using exact
`Rat`/`Decimal` arithmetic. That replaces `f32::from_str` (trusted) with a
`FloatCert : Decimal → u32bits` accompanied by a kernel `Thm` witnessing correct rounding —
untrusted search (even the Rust parser) proposes the bits; the kernel *checks* the
enclosure. This is the decimal analogue of the "gas function as untrusted witness,
relational spec trusted" pattern from
[`parsing-relations.md`](../../lisp/initial-ideas/parsing-relations.md).

### One-screen summary

| Q | Answer | Evidence |
|---|--------|----------|
| 1. Compositional `0xABC`/`12423` grammar | **No** — regex algebra + relation calculus exist, no numeral grammar, radix erased at parse | B `regex.rs`; A `nat.rs:33-37` |
| 2. Oct/dec/hex digit types | **No** — parametric `from_str_radix` only | C `nat.rs:33-37` |
| 3. Fraction / scientific → rational | **Value-level only** (`Rat`, `floatval = m·10^e`); no surface parser or lowering API | C `rat.rs`, A `float_parse.rs:19-59` |
| 4. Positive/finite decimal type | **No** — all decimals collapse to `Rat` | C what_is_missing |
| 5. Float grounding | Opaque IEEE bits; decimal→f32 rounding un-proved, deferred; **decimal theory would make it a checkable enclosure** | A `rules.rs:257-260`, `float_parse.rs:24-25` |

---

## Part 2 — Design: a generic trait-based numeral-literal API

The requirement: **everything behind a generic trait so backends swap.** Mirror the
three-axis structure of [`parametric-reduction.md`](../../lisp/initial-ideas/parametric-reduction.md).
There, reduction is parametric in Representation × Semantics × Strategy. Here, numerals are
parametric in **Representation × Grammar × Backend**, and the load-bearing swap is the
**backend axis** (how a literal is represented *and how equalities/orderings on it are
proved*).

### 2.1 The backend axis (the swap the user wants)

A `Backend` is "how a numeral is represented in the kernel, and how you get a `Thm` about
it." Three instances, ordered by TCB cost — directly analogous to the Strategy axis
(symbolic-chain vs proven-WASM-oracle):

| Backend | Repr of a numeral | How `prove_eq`/`prove_lt` works | TCB cost |
|---|---|---|---|
| **`Symbolic`** | structural (`Zero`/`Succ` binary nat, `mkInt` pair, decimal = `mkDec(n,k)`) — the EG5 target (report A EG5) | **tactics that unfold**: prove `0xABC = 2748` by evaluating both digit folds to the same normal form and chaining kernel equations. No new axioms. | none / tiny |
| **`Builtin`** | native leaf (`TermKind::Nat`, `SmallInt` bits) + `CanonRule` families (`NatArith`/`IntArith`/`Float`, report C `certs.rs:70-87`) | **certificate-backed reduction**: one `ptr_id`-dispatched rule computes the answer in Rust and mints the `Thm`. Fast. | one audited rule per family (already the model today) |
| **`Wasm`** | same as `Builtin` at the boundary, but the reducer is a **verified WASM** digit-fold / rounding routine whose trace is certified | run a proven WASM numeral evaluator, certify its trace as the equation chain (the parsing-relations "executor pattern") | the WASM verification, not the host |

The consumer is generic over `B: NumeralBackend`. `Symbolic` is the honest default (proves
`0xABC = 2748` by unfolding, no extra trust); `Builtin` is the fast drop-in; `Wasm` is the
"verified fast" endgame. Swapping is a type parameter, exactly like swapping a `Strategy`.

### 2.2 Compositional grammars (home: `covalence-grammar`)

Follow [`parsing-relations.md`](../../lisp/initial-ideas/parsing-relations.md): each grammar
is a **parse relation** `⊆ bytes × value` carrying its transpose (a deparser). Build bottom-up;
`covalence-grammar`'s `Regex<A>` gives the syntax, the relation calculus (`compose`/`join`/
`transpose`) gives the semantics.

```
digit grammars          DecDigit  '0'..'9' → 0..9      (Class [0-9])
                        OctDigit  '0'..'7' → 0..7
                        HexDigit  [0-9a-fA-F] → 0..15
        ↓ Plus + left-fold with base
radix numerals          Numeral_dec  12423        (base 10 fold of DecDigit+)
                        Numeral_hex  ABC          (base 16 fold of HexDigit+)
                        Prefixed     0x… 0o… 0b…  (prefix ∘ Numeral_base)
        ↓ join
        Nat_any = Numeral_dec ∪ Prefixed_hex ∪ Prefixed_oct ∪ Prefixed_bin   (mixed base)
        ↓ optional sign prefix
        Int_any = opt('-'|'+') ∘ Nat_any
        ↓
        Frac    = Int_any ∘ '/' ∘ Nat_pos          → Rat
        Decimal = Int_any ∘ '.' ∘ DecDigit*         → Decimal   (n / 10^k)
        Sci     = Decimal ∘ ('e'|'E') ∘ Int_any     → Decimal   (scale exponent)
        ↓ join
        Literal = Nat_any ∪ Int_any ∪ Frac ∪ Decimal ∪ Sci   -- the whole literal grammar
```

Each node is a `Regex`/relation *plus* a value-lift `fold`. Because the whole thing is a
join, `Literal°` (transpose) is a **deparser/printer for free** — round-tripping
`12423 ↔ "12423"`, `2748 ↔ "0xABC"` (per chosen base). Base is a parameter of the fold, so
`Numeral<Base>` is one generic combinator instantiated at 2/8/10/16 (and later 32/58/64,
LEB128 — the "literal atom zoo" of `notes/plans/atoms.md`, report B).

### 2.3 Digit types

Propose small newtypes carrying the "digit in a base" invariant, at both the Rust surface
and (structurally) the kernel:

```rust
/// A digit valid in `BASE` (compile-time), value in 0..BASE.
pub struct Digit<const BASE: u32>(u8);          // invariant: self.0 < BASE
pub type OctDigit = Digit<8>;
pub type DecDigit = Digit<10>;
pub type HexDigit = Digit<16>;

impl<const BASE: u32> Digit<BASE> {
    pub fn from_char(c: char) -> Option<Self>;   // '0'..,'a'..'f' (hex)
    pub fn value(self) -> u8;                     // 0..BASE
    pub fn to_char(self) -> char;                 // deparse
}
```

A numeral is a digit sequence + a base: `nat_of_digits(base, [d…])` = left fold
`acc*base + d.value()` (exactly the existing `nat_of_digits` shape, report A
`init/nat_parse.rs`). In the kernel, `Symbolic` backend represents each `Digit<BASE>` as a
bounded `Nat` (`Succ^k Zero`, k<BASE) so the fold is a chain of `natAdd`/`natMul`
equations, and `0xABC = 2748` is *proved* by reducing both folds. `Builtin`/`Wasm` just
carry the `u8` and let the arithmetic family close the equation.

### 2.4 A `Decimal` type (between `Int` and `Rat`)

Reify the shape that `Rat` currently loses:

```rust
/// Finite decimal  m / 10^k   (k ≥ 0). Distinct from a general Rat.
pub struct Decimal { m: Int, k: u32 }            // value = m * 10^(-k)
pub struct PosDecimal(Decimal);                  // invariant: m > 0

impl Decimal {
    pub fn from_parts(int: Int, frac: &[DecDigit], exp: Int) -> Self; // 1.5e3 → m/10^k
    pub fn to_rat(self) -> Rat;                   // canonical injection Decimal ↪ Rat
    pub fn normalize(self) -> Self;               // strip trailing-zero powers of ten
}
```

Where it sits:

```
Nat  ⊂  Int  ⊂  Decimal (= Int / 10^k)  ⊂  Rat (= Int / Int_pos)  ⊂  Real (Dedekind, report C)
```

`Decimal` is the *exact* landing zone for both scientific notation and finite fractions
whose denominator is a power of ten. Lowering:

- `1.5e3` → `Sci` fold → `Decimal { m: 15, k: 0 } · 10^3` → `Decimal { m: 15000, k: 0 }`.
- `3/4` → `Frac` fold → **not** a `Decimal` (denominator 4) → lands directly in `Rat`.
- `0.75` → `Decimal { m: 75, k: 2 }` (and `= 3/4` as a *provable* `to_rat` equation, not a
  representational identity).

So the lowering target is: try `Decimal` first (powers-of-ten denominators, exact, cheap);
fall back to general `Rat` when the denominator isn't `10^k`. `PosDecimal` gives the
positive-only surface the user asked for (mantissas of magnitudes, unsigned literals).

### 2.5 Float grounding via `Decimal` + `FloatCert`

Replace the trusted `f32::from_str` with a **checked enclosure** (answer to Q5, made
concrete):

```rust
/// A proved rounding of an exact Decimal to IEEE f32 bits.
pub struct FloatCert32 { bits: u32, thm: Thm }   // thm : ⊢ rounds_to_nearest_even(dec, bits)

fn ground_f32<B: NumeralBackend>(b: &B, dec: Decimal) -> FloatCert32;
```

Mechanism (untrusted witness / trusted check, the executor pattern):

1. An *untrusted* proposer (even `f32::from_str`) suggests `bits`.
2. Decode `bits` to its exact value `v = decode_f32(bits)` as a `Decimal`/`Rat`
   (IEEE mantissa·2^exp — exact, `F32` already stores the bit pattern, report A `float.rs`).
3. Prove the enclosure with exact `Decimal`/`Rat` arithmetic:
   `|dec − v| ≤ |dec − v'|` for the two neighbours `v' = decode(bits±1)`, plus the
   round-half-to-even tie rule. All cross-mult comparisons the `Rat` layer already supports
   (report C `rat.rs:2326-2404`).
4. Emit `FloatCert32 { bits, thm }`.

Now the kernel never trusts a decimal→float parser: it *checks* that the chosen bits are
correctly rounded. Under the `Symbolic` backend this is pure unfolding (no new TCB); under
`Builtin`/`Wasm` a fast rounding routine proposes and a verified checker confirms. This is
the strict decimal-literal theory the question asks for.

### 2.6 The trait surface (Rust sketch)

```rust
/// A literal-numeral backend: representation + how to prove facts about it.
pub trait NumeralBackend {
    type Repr;                                    // kernel Term (structural) or leaf, per backend
    type Thm;                                     // kernel theorem for this backend

    // ---- construction (base-aware, digit-sequence based) ----
    fn nat(&self, digits: &[Digit<0>], base: u32) -> Self::Repr;   // Digit erased to value+base
    fn int(&self, sign: Sign, mag: Self::Repr) -> Self::Repr;
    fn decimal(&self, m: Self::Repr /*int*/, k: u32) -> Self::Repr;   // m / 10^k
    fn rat(&self, num: Self::Repr, den: Self::Repr) -> Self::Repr;    // num / den
    fn f32_bits(&self, bits: u32) -> Self::Repr;                      // opaque IEEE leaf

    // ---- proof obligations (the swap point) ----
    fn prove_eq(&self, a: &Self::Repr, b: &Self::Repr) -> Option<Self::Thm>;  // e.g. 0xABC = 2748
    fn prove_lt(&self, a: &Self::Repr, b: &Self::Repr) -> Option<Self::Thm>;
    fn prove_to_rat(&self, dec: &Self::Repr, rat: &Self::Repr) -> Option<Self::Thm>; // 0.75 = 3/4
    fn ground_f32(&self, dec: &Self::Repr) -> FloatCert32;            // §2.5
}

/// The parsing front: bytes → typed literal value (backend-agnostic).
pub trait LiteralGrammar {
    fn parse(&self, input: &[u8]) -> Option<(Lit, &[u8])>;   // Lit = Nat|Int|Decimal|Rat|Float
    fn deparse(&self, lit: &Lit, style: NumStyle) -> Vec<u8>; // transpose: value → bytes (base/notation)
}

/// Glue: parse with a grammar, build with a backend.
fn lower<G: LiteralGrammar, B: NumeralBackend>(g: &G, b: &B, src: &[u8]) -> Option<B::Repr>;
```

`Symbolic`, `Builtin`, `Wasm` are three `impl NumeralBackend`. A tactic library, a printer,
and the surface reader all program against `NumeralBackend`/`LiteralGrammar` and never name
a concrete backend — the user's "everything behind a generic trait" requirement.

---

## Part 3 — Parallel implementation plan (for a follow-up ultracode run)

Crates touched:

- **`covalence-grammar`** — home for digit/numeral/fraction/scientific parse relations +
  transposes (already flagged for kernel-lift, report B).
- **new `covalence-numerals`** (proof/ or lang/ tier) — `NumeralBackend`/`LiteralGrammar`
  traits + `Symbolic`/`Builtin`/`Wasm` impls + `Digit<BASE>` newtypes.
- **`covalence-types`** — add `Decimal`/`PosDecimal` value types (peer of `Rat`, report C).
- **kernel `init`** — structural `Decimal = mkDec(int, nat)` builder + `to_rat` injection
  lemma + `FloatCert` enclosure theorem (`init/decimal.rs`, beside `rat.rs`/`float_parse.rs`).

The fan-out — each item is independent, ships a test, and adds a SKELETONS entry in the file
nearest its code:

| # | Work item | Crate | Test | SKELETONS |
|---|---|---|---|---|
| W1 | `Digit<BASE>` newtypes + `from_char`/`value`/`to_char` | numerals | round-trip all bases 2/8/10/16 | numerals |
| W2 | `DecDigit`/`OctDigit`/`HexDigit` grammars (`Regex` + fold) | grammar | `0..9`, `0..7`, `0..f` classes accept/reject | grammar |
| W3 | `Numeral<Base>` combinator (`Plus digit` + base fold) | grammar | `12423`→12423, `ABC`→2748 | grammar |
| W4 | Prefixed `0x`/`0o`/`0b` + `Nat_any` join (mixed base) | grammar | `0xABC`=`2748`=`0b…` all parse equal | grammar |
| W5 | Signed `Int_any` (sign prefix ∘ Nat_any) | grammar | `-42`, `+7` | grammar |
| W6 | `Frac` grammar `a/b` → `Rat` | grammar | `3/4` → Rat(3,4) | grammar |
| W7 | `Decimal`/`PosDecimal` value types + `to_rat` | types | `0.75.to_rat() == 3/4` | types |
| W8 | `Decimal` grammar `n.m` and `Sci` `1.5e3` fold | grammar | `1.5e3`→`Decimal(15000,0)` | grammar |
| W9 | Deparser via `transpose` for each family | grammar | round-trip parse∘deparse for W2–W8 | grammar |
| W10 | `NumeralBackend` trait + `Symbolic` impl (unfold tactics) | numerals | `prove_eq(0xABC, 2748)` returns Thm | numerals |
| W11 | `Builtin` impl (ptr_id CanonRule families) | numerals | `prove_lt` via NatArith, matches Symbolic | numerals |
| W12 | kernel `Decimal = mkDec(int,nat)` + `to_rat` lemma | init | `⊢ mkDec(75,2) = 3/4` (structural) | init/literals |
| W13 | `FloatCert32` enclosure + `ground_f32` (checked rounding) | init/numerals | `1.5`→`0x3FC0_0000` with enclosure Thm; adversarial off-by-one bits rejected | init/literals |
| W14 | `Wasm` backend (verified digit-fold trace) — endgame | numerals | trace certifies same eq as Symbolic | numerals |

Dependencies: W1→W2→W3→{W4,W5}; W6/W8 depend on W3+W7; W9 depends on W2–W8; W10/W11
depend on W1+W3; W12→W13; W14 mirrors W10. W2–W9 (grammar) and W7/W12 (types/kernel) are
largely independent tracks that can run concurrently; W10–W14 (backend) join at the end.

Do **not** couple this to the irreversible EG5 leaf deletion (`eg5-preflight.md`): the
`Builtin` backend keeps working over today's `TermKind::Nat`/`SmallInt` leaves, and the
`Symbolic` backend over the EG3 `Zero`/`Succ` structure — both compile pre- and post-EG5,
so the numeral API is orthogonal to the leaf-deletion schedule.
