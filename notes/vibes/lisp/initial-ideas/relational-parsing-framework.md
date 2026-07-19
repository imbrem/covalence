+++
id = "N0022"
status = "draft"
review = "unreviewed"

[[contributions]]
role = "author"
actor = "agent:claude"
at = "2026-07-14T18:38:20+01:00"
source = "legacy"
agent = "claude"
harness = "claude"
+++

# Relational parser combinators + a first-class S-expression parsing framework

Status: design note (vibes), agent-authored, **not committed / no code**. Sits on top of
[`parsing-relations.md`](./parsing-relations.md) (parsers as relations, transpose =
deparse, the compose/join/meet/star calculus), reuses the numeral grammars of
[`../../kernel/literals/numeral-literals-api.md`](../../kernel/literals/numeral-literals-api.md),
lifts `covalence-grammar`'s `Regex<A>` (`crates/lang/grammar`), and connects to
`covalence-sexp`'s event API (`SExpVisitor`/`SExpBuilder`/`parse_with`,
`crates/lib/sexp`). It is the *third* relation in the three-theorem REPL pipeline
(`Parses ; Reduces ; Parses°`) from
[`reduction-relations-and-state.md`](./reduction-relations-and-state.md) — here we design
the `Parses` end.

The thesis in one line: **a parser is a relation `bytes × value`, and one relation object
carries both directions — forward = parse, `transpose` = deparse/print.** You never write
two things. The whole S-expr reader/printer, and the whole literal-atom zoo, are then just
the relation calculus applied to syntax.

---

## 0. The core object: a relation carrying two directions

```rust
/// A parser IS a relation  ⊆ bytes × value.  Forward = parse (consume a prefix of the
/// input, produce a value + rest).  Transpose = deparse (render a value to bytes).  ONE
/// object; the two directions are the two ways of reading it.
pub trait Parser {
    /// The value this parser reads / writes.
    type Value;

    /// Forward direction: match a prefix of `input`, returning (value, rest).
    /// `None` = this relation does not relate `input` to any value here (stuck / no witness).
    fn parse<'a>(&self, input: &'a [u8]) -> Option<(Self::Value, &'a [u8])>;

    /// Transpose direction: a *rendering* of `value` — bytes `b` with `parse(b ++ rest)`
    /// yielding `value`.  Deparse is a chosen SECTION of the converse (see §5): the parser
    /// may accept many renderings; the printer picks one canonical `b`.
    fn deparse(&self, value: &Self::Value, out: &mut Vec<u8>) -> Result<(), Undeparsable>;
}
```

Two facts pin the design:

- **`parse` is functional-ish but `deparse` is genuinely relational.** Parsing S-exprs is
  deterministic text→struct; but many texts denote one struct (whitespace, redundant
  parens, base of a numeral). So the *converse* `Parser°` is a real relation (one value,
  many byte strings) and `deparse` is the section of it we *choose* — exactly the
  invertible-syntax / `transpose`-section story of `parsing-relations.md` §"deparser for
  free".
- **Positive-only, by design.** `parse` witnesses "these bytes DO parse to X"; it never
  witnesses "these bytes do NOT parse" — that negative fact is an axiom/derivation on the
  grammar relation, not something running the matcher can produce (`parsing-relations.md`
  §executor). So `None` means "no witness here", not "provably unparsable".

Everything below is combinators that build bigger `Parser`s from smaller ones, mirroring
the base relation calculus `compose`/`join`/`meet`/`transpose`/`star` one-for-one.

---

## 1. The combinator algebra (relation calculus applied to syntax)

Each combinator is a relation op; each carries its transpose for free (the deparse column).

| Combinator | Relation op | Forward (parse) | Transpose (deparse) |
|---|---|---|---|
| `seq(p, q)` | `compose` (thread `rest`) | parse `p`, then `q` on the leftover; value = `(a, b)` | deparse `a` then `b` |
| `alt(p, q)` | `join` (union) | try `p`, else `q` | deparse via whichever branch `value` inhabits |
| `intersect(p, q)` | `meet` | both must match the same prefix (and-predicate / lookahead) | either section (agree by construction) |
| `star(p)` | least fixpoint | zero-or-more `p`, value = `Vec` | deparse each element in order |
| `plus`, `opt` | derived (`star`, `alt ε`) | one-or-more / zero-or-one | as above |
| `map(p, f, g)` | compose with a bijection/partial-iso | apply `f: A → B` to the value | apply `g: B → A` before deparsing `p` |
| `converse(p)` | `transpose` | *is* the deparse direction reified as a parser of the dual | swaps roles |
| `sep_by(p, s)` | `p (s p)*` derived | list with separators | interleave separator on print |

Concrete signatures (all total constructors; the work is in `parse`/`deparse`):

```rust
pub fn seq<P: Parser, Q: Parser>(p: P, q: Q) -> Seq<P, Q>;          // Value = (P::Value, Q::Value)
pub fn alt<P: Parser, Q: Parser<Value = P::Value>>(p: P, q: Q) -> Alt<P, Q>;
pub fn intersect<P: Parser, Q: Parser<Value = P::Value>>(p: P, q: Q) -> Meet<P, Q>;
pub fn star<P: Parser>(p: P) -> Star<P>;                            // Value = Vec<P::Value>
pub fn opt<P: Parser>(p: P) -> Opt<P>;                              // Value = Option<P::Value>
pub fn map<P, B>(p: P, iso: PartialIso<P::Value, B>) -> Map<P, B>;  // carries BOTH f and g

/// A partial isomorphism: the map+unmap pair a `map` combinator needs to stay bidirectional.
pub struct PartialIso<A, B> { pub fwd: fn(A) -> Option<B>, pub bwd: fn(B) -> Option<A> }
```

`map` takes a `PartialIso` (not a bare `Fn`) precisely so the transpose survives a value
transformation — this is what lets a digit-run become a `Nat` *and* a `Nat` render back to
a digit-run. The value-lifts in `numeral-literals-api.md` §2.2 are exactly these isos.

**Relation to `Regex<A>`.** `covalence-grammar`'s `Regex<A>` (`Lit/Class/Concat/Alt/
Star/Plus/Opt/Rep`, `crates/lang/grammar/src/regex.rs`) is the *syntax half* — a value-less
recognizer. A `Parser` is a `Regex<u8>` (or a richer grammar node) **paired with a
`PartialIso` value-lift**: `Concat↦seq`, `Alt↦alt`, `Class↦a byte→value leaf`,
`Star↦star`. So combinators are "Regex + fold", and the executable regex matcher becomes
the certified accelerator (§3). We do not throw `Regex` away; we decorate it.

---

## 2. Grammar as a whole object

A `Grammar` is a named, possibly recursive bundle of productions — what you need for
S-exprs (list references expr, expr references atom-or-list). It is the fixpoint that
`star` is a special case of.

```rust
/// A (possibly recursive) grammar producing `Value`.  Recursion = a named nonterminal that
/// may reference itself (S-expr's expr ⇄ list); realized as a least fixpoint, the same
/// impredicative-relation shape as `star` and the kernel `Graph`.
pub trait Grammar {
    type Value;
    fn start(&self) -> &dyn Parser<Value = Self::Value>;
    /// Optional: name → sub-parser, so extensions (§4) can splice into a nonterminal.
    fn nonterminal(&self, name: &str) -> Option<&dyn Parser>;
}
```

Every `Parser` is trivially a `Grammar` with one production; the trait exists so the S-expr
grammar can expose its `atom` nonterminal as a **join point** for pluggable atom
extensions (§4).

---

## 3. The executable matcher as certified accelerator (execute pattern)

The declarative relation is the spec; a **gas/PEG matcher** is the fast oracle, bridged by
`execute` (`parsing-relations.md` §executor). This is the same untrusted-witness /
trusted-check split as the numeral backends' `Wasm` oracle.

```rust
/// A compiled, executable form of a Parser: a gas-bounded PEG/regex matcher.  Untrusted,
/// fast.  `run` returns a witness that CAN be certified against the HOL Parses relation.
pub trait Matcher {
    type Value;
    fn run<'a>(&self, input: &'a [u8], gas: Gas) -> MatchResult<'a, Self::Value>;
}

pub enum MatchResult<'a, V> {
    Ok { value: V, rest: &'a [u8] },   // positive witness → mint  ⊢ Parses input value  (execute)
    NoMatch,                            // NO witness (not a proof of unparsability)
    OutOfGas,                           // ran out of fuel (also not a negative fact)
}
```

- `Parser` (declarative) → `compile()` → `Matcher` (executable), analogous to
  `Regex → DFA`.
- Running the matcher and certifying its positive result is the `execute` seam: the printed
  value comes off a genuine `⊢ Parses …` Thm, never off the raw matcher output.
- **Gas, not a hang.** A left-recursive or adversarial grammar bounds out; matches the
  reduction-relation note's fuel philosophy (§reduction — non-termination is a status, not
  a freeze).

Three views of one grammar (mirrors `parsing-relations.md` §"three views"):
**spec** = the relation `Parser`/eventual HOL `Parses`; **executor** = `Matcher` (gas PEG);
**derived partial function** = `parse := ε o. Parses input o`, proved to agree with the
matcher on its domain via a determinism theorem (§6).

---

## 4. The S-expression parsing framework + pluggable atom extensions

The S-expr grammar is a `Grammar` whose productions are the combinators above. The *shape*
is fixed (whitespace, lists, quotes); the **atom parser is an extensible join**.

```
Sexpr   = ws* ∘ (List ∪ Quoted ∪ Atom) ∘ ws*
List    = '(' ∘ ws* ∘ star(Sexpr) ∘ ws* ∘ ')'          -- recursive: references Sexpr
Quoted  = ("'" ∘ Sexpr)  ∪  ("`" ∘ Sexpr)  ∪  (",@"? ∘ "," ∘ Sexpr)   -- quote/quasiquote
Atom    = Symbol  ∪  ⨆ enabled atom-extensions          -- THE plug point (a `join`)
ws      = star( space | tab | newline | comment )       -- trivia (dialect-configurable)
```

`Atom` is literally `join`-ed from an extension registry — each extension is an opt-in
`Parser` producing a typed atom value, spliced into the atom nonterminal:

```rust
/// One pluggable atom parser: bytes → a typed atom value, plus its printer (transpose).
pub trait AtomExtension: Parser<Value = AtomValue> {
    fn name(&self) -> &str;             // "string", "nat", "int", "decimal", "bytes", …
    fn priority(&self) -> u8;           // join order: earlier wins on overlap (see below)
}

/// The extensible atom value.  Symbol is always present; the rest are opt-in.
pub enum AtomValue {
    Symbol(SmolStr),
    Str { format: SmolStr, bytes: Bytes },   // "..."  /  b"..."
    Nat(NatLit),                             // 12423, 0xABC, 0o17, 0b101   (numeral grammars)
    Int(IntLit),                             // -42, +7
    Decimal(DecimalLit),                     // 1.5, 0.75, 1.5e3
    Rat(RatLit),                             // 3/4
    Bytes(Bytes),                            // b"...", or a hex/base64 bytes form
    // extensible: downstream adds variants behind their own AtomExtension
}

/// The registry: `Atom = ⨆ extensions` — enabling/disabling a literal syntax is a
/// join/un-join of the atom parser.  This is the "mixed base = join" idea of
/// numeral-literals-api.md §2.2 generalized to ALL atom kinds.
pub struct AtomRegistry { exts: Vec<Box<dyn AtomExtension>> }

impl AtomRegistry {
    pub fn minimal() -> Self;            // Symbol only (today's SmolStr behavior)
    pub fn with(mut self, ext: impl AtomExtension + 'static) -> Self;   // opt-in join
    pub fn atom_parser(&self) -> impl Parser<Value = AtomValue>;        // the joined relation
}

// Usage: build the atom vocabulary you want, then the sexpr grammar over it.
let atoms = AtomRegistry::minimal()
    .with(StringLit::default())
    .with(NatLit::radixes(&[2, 8, 10, 16]))   // reuse numeral grammars
    .with(IntLit::default())
    .with(DecimalLit::default())              // 1.5e3, 0.75  (Decimal, numeral-literals §2.4)
    .with(BytesLit::hex());
let sexpr = SexprGrammar::over(atoms, CovalenceDialect);
```

The atom extensions **are** the numeral-literal grammars of `numeral-literals-api.md`:
`NatLit` = the `Nat_any` join (`Numeral_dec ∪ Prefixed_hex ∪ …`), `IntLit` = sign ∘
`Nat_any`, `DecimalLit`/`RatLit`/`Sci` = the fraction/scientific relations. Each ships its
transpose = a base-aware printer (deparse `0xABC` vs `2748`). So enabling hex literals in
the reader *automatically* enables hex printing — one relation, both directions.

**Join/priority discipline.** Overlapping atoms (`123` is both a `Symbol` and a `Nat`)
resolve by `priority` — literals shadow bare symbols. This is an ordered `join` (leftmost
match wins), the same convention as `Alt`'s ordered choice in `Regex`. Ambiguity that
*isn't* resolved by priority is a grammar bug caught by the determinism proof (§6).

### Relation to `covalence-sexp`'s event API

`covalence-sexp` already has the SAX layer: `SExpVisitor` (events `open_list`/`close_list`/
`atom`/`string`/`quoted_symbol`) + `SExpBuilder` (bottom-up `build_atom`/`build_list`/…) +
`parse_with`. Two clean bridges, no rewrite of either side:

- **Adapter (near-term, cheap):** an `AtomExtension` implemented by *calling* the existing
  reader's atom tokenizer, or the whole relational `Parser` implemented as a
  `SExpVisitor` that fires `open_list`/`atom`/… events. So the relational front produces
  the same `SExpr` tree via `DefaultBuilder`, and everything downstream (Lisp reader,
  dialects) is unchanged. The event API is the *witness generator* (`execute`-style), the
  relation is the *stated proposition* — exactly `reduction-relations-and-state.md` §5
  ("`Parses` HOL relation, reader as its oracle").
- **Value enrichment:** today `build_atom` collapses everything to `Atom::Symbol(SmolStr)`
  (`sexp/src/builder.rs:26`), so `"42"`, `"0xFF"` stay symbols (per `numeral-literals-api`
  Q1). A relational atom registry lets a builder emit typed `AtomValue::Nat(…)` instead —
  the enrichment the numeral note wants, opt-in per dialect. `Dialect` (trivia + quoted
  delim) maps onto the `ws`/`Quoted` productions.

---

## 5. Deparse / printer as a chosen section

Printing is `deparse`, the transpose-section (`parsing-relations.md` §"deparser for free"):

```rust
/// A printer is a chosen functional section of Parser°: for each value, ONE canonical
/// rendering, proved to be accepted by the parser.  Styles pick among sections.
pub struct Printer<'g> { grammar: &'g dyn Grammar, style: PrintStyle }

pub struct PrintStyle {
    pub num_base: NumBase,      // print Nat as dec / hex / bin — a different section per base
    pub spacing: Spacing,       // minimal vs pretty (indented) whitespace
    pub abbreviations: bool,    // state-aware macro abbreviation (see below)
}
```

- The parser accepts many renderings; the printer *chooses* one (minimal parens, chosen
  numeral base, canonical whitespace) and the round-trip `parse(deparse(v)) = Some(v)`
  reduces to "the chosen rendering is in `Parser°ᵥ`" — small, canonical work.
- **State-aware printing (macro abbreviation)** is `reduction-relations-and-state.md` §4:
  `Parses` gains a `State` param (`Parses state bytes value`); the printer may render a
  value as a defined name `two` because `Parses defs "two" value` holds. Same relation in
  reader and printer ⟹ reader/printer can't drift. The `abbreviations` flag toggles this
  section family. (State-relative parsing is future; the API reserves the seam.)

---

## 6. The kernel story (eventual HOL lift)

Following `parsing-relations.md` §"what it would take", the layering carries straight into
the kernel; nothing above the trait surface moves when the spec upgrades from a Rust
relation to a HOL `Parses` relation (that is the point of separating spec / executor /
derived function).

1. **`Parses` as an inductive HOL relation** — `Parses ⊆ (State ×) bytes × value`, the
   impredicative least fixpoint (`∀R. Closed_grammar(R) ⟹ R …`), one closure clause per
   production (`(`, list tail, `)`, whitespace, each atom extension). Same `Graph`/`Wf`
   shape already in `covalence-init` (`init/inductive/graph.rs`); no new kernel machinery,
   and **no admitted defining equation** — the relation is *defined* by its introductions,
   not postulated. Start with a single numeral base (`ParseNat_dec`) as the high-signal
   first cut (numeral note W-series), then S-exprs, then the combinator layer.
2. **Deparse from transpose** — `Parses°` is the deparse relation; the concrete printer is
   a proved section `∀v. Parses° state (print v) v`. The relation calculus already has
   `transpose` as a primitive, so deparse is not a second definition.
3. **Determinism → partial-function lift** — prove right-uniqueness
   (`Parses inp o1 ⟹ Parses inp o2 ⟹ o1 = o2`; the `graph_det` technique, easy for the
   unambiguous S-expr / ordered-choice grammar) plus termination (well-founded on the
   consumed prefix), then lift to `parse : bytes → option value`. The priority/ordered-join
   discipline of §4 is what makes right-uniqueness hold despite `Symbol`/`Nat` overlap.
4. **Executor certified against spec** — the gas `Matcher` (§3) proved to agree with
   `Parses` on its domain via `execute`; it becomes the accelerator, not the definition.
   Negative facts ("does NOT parse") remain axiom/derivation-only (positive-only executor).

Combinators lift compositionally: `seq↦compose`, `alt↦join`, `intersect↦meet`,
`star↦least-fixpoint`, `converse↦transpose`, `map↦compose-with-a-proved-partial-iso`. So
the Rust `Parser` algebra and the HOL relation calculus are the same algebra at two levels
— the surface datatype and the semantics it lifts to.

---

## 7. Where it lives

- **Extend `covalence-grammar`** with the value-carrying combinator layer (`Parser`/
  `Grammar`/`Matcher`/`PartialIso`) directly on top of `Regex<A>`. The crate is already
  flagged "meant to be lifted into kernel-verified computations", is dependency-light,
  wasm-clean, and `#![forbid(unsafe_code)]` — the right home. The numeral atom grammars
  (`NatLit`/`IntLit`/`DecimalLit`) also live here (as `numeral-literals-api.md` §2.2/Part 3
  already places them).
- **A thin `covalence-parse` (lang tier)** *only if* the S-expr framework + `AtomRegistry`
  + the `covalence-sexp` bridge grow beyond what belongs in the grammar crate — it would
  depend on `covalence-grammar` (combinators) and `covalence-sexp` (event API / `SExpr`
  tree / dialects), gluing the relational front to the existing SAX reader. Default: keep
  the combinator algebra in `covalence-grammar`, put the sexp-specific `AtomRegistry` +
  visitor bridge in `covalence-sexp` (or that thin crate), so `covalence-grammar` stays
  syntax-generic and the sexp coupling is localized.
- Forbid `unsafe` throughout (kernel-liftable surface language, per the workspace rule).

---

## Summary (5 lines)

1. **One relation object `Parser` = `bytes × value`; forward = parse, `transpose`/`deparse`
   = print** — never two artifacts; the combinators `seq/alt/intersect/star/opt/map/
   converse` are the base relation calculus (`compose/join/meet/lfp/transpose`) applied to
   syntax, decorating `covalence-grammar`'s `Regex<A>` with value-lifts (`PartialIso`).
2. The **gas/PEG `Matcher` is the certified accelerator** (execute pattern): untrusted fast
   oracle whose positive matches mint `⊢ Parses …`; `None`/out-of-gas are non-witnesses,
   never proofs of unparsability (positive-only).
3. The **S-expr grammar is a recursive `Grammar`** with a fixed shape (ws/lists/quotes) and
   an **extensible atom join** — `Atom = Symbol ∪ ⨆ opt-in AtomExtensions` via an
   `AtomRegistry`, where string/bytes/nat/int/decimal/rat literals are the reused numeral
   grammars, each carrying its base-aware printer for free by transpose.
4. It **bridges `covalence-sexp`'s `SExpVisitor`/`SExpBuilder`** — the event API is the
   witness generator, the relation is the stated proposition; enables typed `AtomValue`s
   instead of collapsing every atom to `Symbol`.
5. **Kernel endgame:** `Parses` as an inductive HOL relation (no admitted equations),
   deparse from `transpose`, determinism+termination lifting to a partial `parse` function,
   executor certified against the spec — the third theorem of the `Parses ; Reduces ;
   Parses°` REPL pipeline. Home: extend `covalence-grammar`; sexp glue in `covalence-sexp`
   (or a thin `covalence-parse`).
