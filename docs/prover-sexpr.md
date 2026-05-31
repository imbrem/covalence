# S-Expression Debug Syntax

This document specifies a human-readable S-expression syntax for
the kernel's term and type language ([`prover-architecture.md`](./prover-architecture.md)
§3, [`prover-primops.md`](./prover-primops.md)). The syntax is for
**debugging and REPL use only** — it's *not* the wire format
(serialisation lives elsewhere) and the parser/printer live
**outside the kernel**, in `covalence-shell`, where they can be
audited and replaced freely.

The parser is built on `covalence-sexp` using the
`CovalenceDialect` (line comments `;;`, block comments `(; ;)`,
quoted symbols `|...|`). The printer emits the same dialect so
parse/print is a faithful round trip.

---

## 1. Conventions

- **Kebab-case** keywords (`nat-add`, `lift-op1`, …).
- **Lowercase** type and primop names matching the kernel's
  `TypeKind` / `TermKind` / `PrimOpN` enums.
- **Named binders for human readability**, even though the kernel
  uses de Bruijn indices internally. The parser walks the form and
  emits the correct `Bound(_)` indices; the printer chooses names
  to avoid capture.
- **Free variables** carry both a name and a type — `(var x bool)`
  binds the name `x` of type `bool` as a `TermDef::Free`.
- **Untrusted**: the parser uses kernel allocator primitives
  (`alloc_term`, `intern_string`, etc.) but doesn't depend on the
  kernel's internal layout. Replacing the parser cannot make the
  kernel unsound.

---

## 2. Types

```
;; primitive types — one keyword each
bool   bits   bytes
int    nat
u8 u16 u32 u64
i8 i16 i32 i64

;; function type α → β
(fun α β)

;; type variable
(tvar 'a)

;; user-declared type constructor; args is a possibly-empty list
(tyapp list (α))
(tyapp pair (α β))
(tyapp opt  (α))
```

The `'`-prefix on type-variable names is conventional, not parsed
specially — the kernel just sees a `StrId`.

---

## 3. Terms

### 3.1. Variables and constants

```
(var x α)      ;; free variable of name x, type α       → Free
(const c α)    ;; declared constant c at instance α      → Const
```

### 3.2. Application and abstraction

```
(comb f x)         ;; application f x                   → Comb
(lam (x α) body)   ;; λ x : α. body                     → Abs

;; named binders desugar to de Bruijn — the parser walks scopes
;; and emits Bound(depth) where depth = number of binders to skip
```

### 3.3. Booleans, equality, inequality

```
true            ;; literal True
false           ;; literal False
(eq a b)        ;; primitive Eq
(ne a b)        ;; primitive Ne (≠)
```

### 3.4. Quantifiers and choice

For readability the syntax allows the binder to fold *into* the
quantifier; the parser desugars it to a `(comb forall (lam ...))`
shape internally before allocating.

```
(forall (x α) body)   ;; ≡ (forall (lam (x α) body))
(exists (x α) body)   ;; ≡ (exists (lam (x α) body))
(eps    (x α) body)   ;; ≡ (eps    α (lam (x α) body))

;; bare forms (no binder fold) also accepted, useful when the
;; predicate is already a term
(forall p)
(exists p)
(eps α p)
```

### 3.5. Combinators and control flow

```
(id α)                 ;; Id α
(comp f g)             ;; Comp f g
(iter n f)             ;; Iter n f

(ite cond then)        ;; partial: (Ite cond then) — awaits else via comb
(ite cond then else)   ;; sugar for (comb (ite cond then) else)
```

### 3.6. Primops and lifting

Op1/Op2 use the kernel's primop names directly as keywords:

```
;; logical
(not x)              ;; Op1(LogicalNot, x)
(and x y)            ;; Op2(LogicalAnd, x, y)
(or  x y)
(xor x y)
(nand x y) (nor x y) (imp x y)

;; nat
(nat-succ n) (nat-pred n)
(nat-add x y) (nat-sub x y) (nat-mul x y)
(nat-div x y) (nat-mod x y) (nat-pow x y)
(nat-and x y) (nat-or  x y) (nat-xor x y)
(nat-shl x y) (nat-shr x y)
(nat-popcount n)
(nat-eq x y) (nat-lt x y) (nat-le x y)

;; int
(int-neg i) (int-not i)
(int-add x y) (int-sub x y) ...

;; fixed-width: T-Op naming, e.g.
(u32-add x y) (i64-shr x y) (u8-popcount x)

;; bytes / bits
(bytes-len bs) (bytes-head bs) (bytes-tail bs)
(bytes-cons b bs) (bytes-concat a b) (bytes-index bs i)
(bits-len w) ...

;; lifting primops to function values
(lift-op1 not)              ;; LiftOp1(LogicalNot)
(lift-op2 nat-add)          ;; LiftOp2(NatAdd)
```

### 3.7. Literals

```
;; booleans                       ;; (covered in §3.3)
;; fixed-width
(u8  42)
(u32 0xFFFF_FFFF)
(i64 -42)

;; arbitrary-precision; "n" = nat, "i" = int
(nat 42)
(nat 0x100000000)              ;; promoted to NatStored if > u64::MAX
(int -123456789012345)

;; bytes / bits literals (always stored)
(bytes #x"DEAD_BEEF")          ;; b"..." style — the dialect's
                                ;; "format" prefix carries through
(bits  #b"1010_0011")

;; hex / binary numeric literals use the dialect's atom-with-string
;; convention from covalence-sexp; the parser also accepts plain
;; decimal as `(nat 42)`, `(int -7)`, etc.
```

---

## 4. Reference grammar (excerpt)

```ebnf
term      ::= var | const | comb | abs | bool-lit | eq | ne
            | forall | exists | eps | id | comp | iter | ite
            | op1 | op2 | lift1 | lift2 | num-lit | bytes-lit

var       ::= "(" "var"   ident type ")"
const     ::= "(" "const" ident type ")"
comb      ::= "(" "comb" term term ")"
abs       ::= "(" "lam"  binder term ")"
binder    ::= "(" ident type ")"

forall    ::= "(" "forall" (binder | term) term? ")"
exists    ::= "(" "exists" (binder | term) term? ")"
eps       ::= "(" "eps" (type binder term | type term) ")"

;; ... and so on for the rest
```

The full grammar derives mechanically from the `TermKind` / `TypeKind`
enums; the parser/printer ship a unit test asserting every variant
round-trips.

---

## 5. Parser / printer crate location

The parser/printer live in `covalence-shell` (the untrusted wiring
crate; see [`prover-mvp-plan.md`](./prover-mvp-plan.md)). Module
sketch:

```rust
// crates/covalence-shell/src/sexpr.rs
pub fn parse_term(src: &str, arena: &mut Arena) -> Result<TermRef, ParseError>;
pub fn parse_type(src: &str, arena: &mut Arena) -> Result<TypeRef, ParseError>;

pub fn print_term(arena: &Arena, t: TermRef) -> String;
pub fn print_type(arena: &Arena, t: TypeRef) -> String;
```

- `parse_term` walks the S-expression tree (built by
  `covalence_sexp::parse`) and emits a `TermRef` by calling kernel
  allocators. Named binders are translated to de Bruijn during the
  walk; a `Vec<(SmolStr, TypeRef)>` scope stack tracks bindings.
- `print_term` recursively reconstructs an S-expression from a
  `TermRef`. Bound variables get *display hints* from
  `arena.abs_hints` when available, falling back to `x0`, `x1`, …
  with capture-avoidance.

**No kernel coupling.** Both functions go through public arena APIs.
Replacing the parser with a different concrete syntax doesn't touch
the kernel or its trust surface.

---

## 6. REPL integration

The Forsp postfix REPL ([`prover-mvp-plan.md`](./prover-mvp-plan.md)
Phase 8) exposes two primitives:

- `<string> parse-term`  — pushes a `TermRef` onto the stack
- `<term-ref> print-term` — pops a `TermRef`, prints its S-expression

Example session:

```
"(comb (lift-op1 not) (var p bool))" parse-term  ;; → TermRef on stack
dup print-term                                    ;; → prints back
```

The REPL also gets a convenience `:t` shorthand that takes the next
token as a literal string and parses it, but that's a REPL feature,
not a parser feature.

---

## 7. Round-trip tests

The parser/printer crate ships a test for every `TermKind` and
`TypeKind` variant:

1. Build the term programmatically in the arena.
2. `print_term` to S-expression.
3. `parse_term` back into a fresh arena.
4. Assert the two `TermRef`s are structurally equal (modulo arena
   identity).

This covers the catalogue mechanically; new primops added to the
kernel break this test until their syntax case is handled, which
is the desired forcing function.

---

## 8. What this syntax is **not**

- **Not a serialisation format.** The Prop serialisation of
  [`prover-mvp-plan.md`](./prover-mvp-plan.md) Phase 6 uses a
  binary table-based format keyed on hash, not text.
- **Not the proof script syntax.** Proof scripts (when we land
  them) drive *tactics*; this syntax names *terms*.
- **Not a stable user-facing language.** The kernel API and
  primop catalog still churn; this debug syntax tracks them, and
  may break between MVP iterations. A user-facing language is a
  later concern.
