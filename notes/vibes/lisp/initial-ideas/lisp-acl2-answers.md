# Lisp/ACL2 support — answers (discussion draft, agent-authored)

Draft answers to the Lisp/ACL2 questions in `notes/plans/sketch-separation.md`
(lines 71–81). Not committed; for us to refine, then fold the result back into the
sketch's §"What exactly is the current state of our Lisp/ACL2 support?".

---

## 1. Current state (what actually exists today)

Grounded in the code; file:line where it helps.

**The carved `sexpr` datatype — the linchpin.** `init/inductive/carved.rs`. A genuine
HOL *exact-type* inductive type (via `new_type_definition`), carved from a universal
domain `U := list bool → (bytes + unit + unit)`. It ships, all *proved*:
- constructors `atom : bytes → sexpr`, `snil`, `scons : sexpr → sexpr → sexpr`;
- extractors `car`/`cdr` with ACL2 defaults (`car (atom b) = car snil = snil`);
- structural `induct`, a **paramorphic** recursor `prec` (steps see raw arg + fold
  image — this is what powers `append`), injectivity at recursive positions,
  distinctness.
- Exposed to Rust via `carved()`, and as an `InductiveBackend<NativeHol>`
  (`carved_backend()`) with caps `mem_trivial=true, rec_injective=true, prim_rec=true`.

**The Lisp theory.** `init/lisp.rs`: `car`/`cdr`/`cons`, `consp`, `atom?`, `len :
sexpr → nat`, `append : sexpr → sexpr → sexpr` — all defined via `prec`, all with
proved computation laws — plus the two **ACL2 archetype theorems**: `append_assoc`
(structural induction on the first arg, tail IH only) and `len_append`
(cata/para/nat-induction mix). This is real, but it is *proof-of-concept groundwork*,
not production ACL2.

**Parsers (text/bytes → HOL).** `init/sexpr_parse.rs` — a fuel-bounded reader
`nat → bytes → option (sexpr × bytes)` producing carved terms, with proved step
equations + `parsed_cons_struct` (the parsed list's `consp`/`car`/`cdr` compute
right). `init/json_parse.rs` reuses it (JSON integer+array subset + the `same_json`
PER). **There is no deparse** (`sexpr → bytes`) anywhere.

**Several *distinct* S-expression representations already coexist:**

| Rep | Where | What | Parse / print |
|---|---|---|---|
| **Carved sexpr** | `init::inductive::carved` | HOL `Term`, exact inductive type (the ground truth) | `sexpr_parse` in; **no** deparse |
| **Church sexpr** | `init::sexpr` | HOL `Term`, impredicative `S⟨r⟩ := (bytes→r)→r→(r→r→r)→r` | embedding only |
| **covalence-sexp** | `crates/lib/sexp` | Rust enum, dialect-parametrized (SMT/wat/egglog/cov) | `parse*` + `prettyprint` |
| **covalence-haskell SExpr** | `crates/lang/haskell/src/sexpr.rs` | Rust enum `Sym\|Nat\|Str\|List`, arbitrary-precision `Nat` atoms, canonical printer | `parse_sexpr` / `to_text` |

Casts that exist: Haskell `Expr → SExpr` (`lower`), `SExpr → carved Term`
(`realize` + `HolBackend`), `SExpr ↔ text`. **Missing:** carved ↔ Church, Term →
Rust value ("parse out"), Term → text (deparse).

**Trait abstractions that already exist** (relevant to the carving question):
- `Realize` (`haskell/src/realize.rs`): `nat/string/symbol/list` — a *producer* of a
  backend value from the SExpr IR; `HolBackend` is the one impl (→ carved Term).
- `covalence-inductive`'s `Logic`/`LogicOps` + `InductiveBackend<L>` + `InductiveFacts<L>`
  — a **logic-neutral** datatype framework with a *membership-relativized* contract
  (`mem t ⟹ …`, discharged trivially by exact-type backends) so two backends can
  swap representations under one consumer API. Only the carved backend exists so far.
- The `Hol` trait (`init/inductive/hol.rs`) + `NativeHol` — the value-typed HOL surface
  the engines run on (also re-exported now as `covalence-hol-api`).
- There is a design sketch `acl2-lisp.md` (database `D_ACL2`, executor, faithfulness
  model) — not yet built.

**Bottom line:** we have a *sound HOL model of S-expressions and the Lisp core*, a
*verified reader*, a *logic-neutral inductive framework* that already anticipates
"swap the representation," and *two ACL2 induction theorems*. We do **not** have:
deparse, parse-out (Term → value), cross-representation casts, a reduction/evaluation
trait, a test Lisp interpreter, or a real ACL2 frontend.

---

## 2. The clean carving I'd propose

The three traits you named ("produce", "parse out", "reduce") fall out cleanly if we
first name the thing they all range over: **a representation of S-expressions**. That
one abstraction unifies the Rust interpreter, the carved HOL term, the Church term,
and any future rep — and makes casts and the parse/deparse pair fall out for free.

### 2a. `SExprRep` — the representation trait (the keystone)

```rust
/// One representation of S-expressions. `Repr` is a Rust value (a plain enum),
/// a carved HOL `Term`, a Church HOL `Term`, an egraph id, …
trait SExprRep {
    type Repr;
    type Error;

    // ---- CONSTRUCTION (the "produce" side; this is today's `Realize`) ----
    fn atom(&mut self, bytes: &[u8]) -> Result<Self::Repr, Self::Error>;
    fn nil(&mut self)               -> Result<Self::Repr, Self::Error>;
    fn cons(&mut self, h: Self::Repr, t: Self::Repr) -> Result<Self::Repr, Self::Error>;

    // ---- OBSERVATION (the "parse out" side; the missing inverse) ----
    fn view(&self, r: &Self::Repr) -> Result<SView<Self::Repr>, Self::Error>;
}

enum SView<R> { Atom(Vec<u8>), Nil, Cons(R, R) }
```

- **Producing S-expressions** = the construction half. `Realize` is *already* this,
  just phrased over the IR's `nat/string/symbol/list` rather than the ACL2-canonical
  `atom/nil/cons`; I'd rebase `Realize`'s backends onto `SExprRep` (symbol/nat/string
  all become `atom <bytes>` at the sexpr layer, which is what `HolBackend` already
  does) and keep the richer IR sink as a thin layer on top.
- **Parsing out** = the observation half (`view`). For the Rust reps it's a trivial
  `match`. For a HOL rep it must go through the kernel: `view(t)` computes
  `consp t`, and on a cons reads `car t`/`cdr t`; on a leaf it reads the atom's
  bytes. **Crucially it should be *certified*** (see §3) — that is exactly your
  "help us show we're proving what we think we're proving."

### 2b. Casts fall out for free

A cast is just observe-from-A, construct-in-B — one generic fold, works between *any*
two reps:

```rust
fn cast<A: SExprRep, B: SExprRep>(a: &A, av: &A::Repr, b: &mut B)
    -> Result<B::Repr, CastError<A::Error, B::Error>>
{
    match a.view(av)? {
        SView::Atom(bytes) => b.atom(&bytes),
        SView::Nil         => b.nil(),
        SView::Cons(h, t)  => { let h = cast(a, &h, b)?; let t = cast(a, &t, b)?; b.cons(h, t) }
    }
}
```

This gives us Church↔Carved, Rust-value→Term, Term→Rust-value, IR→Term, all from the
one trait — no bespoke converters. (The HOL→HOL casts should additionally emit an
equality `⊢ castA_to_B t = t'` if we want them inside proofs; see §3.)

### 2c. Parse / deparse as a pair, per rep

Add to (or beside) `SExprRep`:

```rust
trait SExprText: SExprRep {
    fn parse(&mut self, text: &[u8]) -> Result<Self::Repr, Self::Error>;   // exists for carved (sexpr_parse) + Rust reps
    fn deparse(&self, r: &Self::Repr) -> Result<Vec<u8>, Self::Error>;     // MISSING for HOL reps
}
```

- Rust reps: `parse` / `to_text` already exist (`covalence-haskell`, `covalence-sexp`).
- Carved HOL rep: `parse` = `sexpr_parse`; **`deparse` is the concrete missing HOL
  work** — a `sexpr → bytes` catamorphism plus the round-trip theorem
  `⊢ parse (deparse t) = some (t, nil)` (or the PER version). This is the "deparse
  tactic to go with the parse tactic" you flagged, and it is a *bounded, well-defined*
  chunk (a `prec`-defined function + one induction).

### 2d. Lisp / ACL2 term-work + reductions, generic over the rep

Put the Lisp semantics **on top of `SExprRep`**, generic over `Repr`, so the *same*
evaluator drives the test interpreter and the certified HOL term:

```rust
trait LispEval: SExprRep {
    fn consp(&self, r: &Self::Repr) -> Result<bool, Self::Error>;   // = matches Cons
    fn car(&self, r: &Self::Repr)   -> Result<Self::Repr, Self::Error>;
    fn cdr(&self, r: &Self::Repr)   -> Result<Self::Repr, Self::Error>;
    fn eval(&mut self, env: &Env<Self::Repr>, form: &Self::Repr) -> Result<Self::Repr, Self::Error>;
    // + apply, and the ACL2 primitive fns (equal, if, cons, +, ...)
}
```

- The `Lisp` theory (`len`, `append`, `consp`, …) is the HOL instance of the
  *forward* part; `eval` is the general reducer we don't have yet.
- The carved-HOL instance is *certified* (each step is a proved equation, à la
  `prec_eq`); the Rust instance is *fast and total* (a normal interpreter).

---

## 3. How this serves the three specific goals you called out

**(a) "The same trait usable by a test Lisp interpreter (for unit/integration tests +
fuzzing)."** The test interpreter is just `impl SExprRep + LispEval for TestLisp {
type Repr = RustSexpr; … }` — construction/observation/eval are a plain `match`. Then
**differential testing** is the payoff: for a random ground form, run `TestLisp::eval`
and the certified HOL `eval`, `cast` both to `RustSexpr`, and assert equality. That is
literally "showing we're proving what we think we're proving," and it fuzzes cheaply
because the Rust side is fast. (Property: `deparse(HOL_eval(t)) == to_text(TestLisp_eval(t))`.)

**(b) "Different HOL representations of S-expressions, with casts between them."** Carved
and Church are each an `impl SExprRep`; §2b's `cast` moves between them, and the
HOL→HOL casts can carry a certifying `Thm` so a proof can rewrite one rep into the
other. This is also the clean way to eventually let a *proof about the carved rep* be
transported to a proof about the Church rep (or a future egraph-backed rep).

**(c) "The 'parse out' bit needs a deparse tactic to go with the parse tactic."** Two
layers, and we should be explicit about which we mean:
- *Deparse to text* (`SExprText::deparse`) — the HOL `sexpr → bytes` function + the
  `parse ∘ deparse = id` theorem. The proper inverse of the reader.
- *Parse out to a Rust value* (`SExprRep::view`, recursively) — deconstruct a HOL term
  into a `RustSexpr`. For a test oracle this should return the value **with a
  certificate**: e.g. `observe(t) -> (RustSexpr, Thm)` where the `Thm` is
  `⊢ t = <the term rebuilt from the RustSexpr>` (built by `cast`-ing the RustSexpr back
  into carved and proving equality by computation). Then "we proved `P(t)`, and here is
  `t` observed as a concrete value with a proof they're the same term" — no gap.

---

## 4. Concrete missing pieces + a suggested build order

1. **`SExprRep` trait + rebase `Realize`/`HolBackend` onto it** (mechanical; unifies
   the producer story). Also gives `cast` immediately. — *small, high leverage.*
2. **`view`/observe for the carved HOL rep, certified** (`consp`/`car`/`cdr` compute +
   read the atom blob; return value + `Thm`). — *the "parse out" core.*
3. **Deparse: HOL `sexpr → bytes` + the round-trip theorem.** — *bounded HOL proof;
   this is the single most-requested missing artifact.*
4. **`TestLisp` (Rust interpreter) + a differential-test/fuzz harness** vs the certified
   HOL eval. — *the confidence multiplier; makes the sexpr layer trustworthy.*
5. **`LispEval::eval` (general reducer) in HOL** — the real step past `len`/`append`;
   needs the recursion/measure story (ordinals) that ACL2 uses. — *the ACL2 on-ramp.*
6. **Church backend as a second `InductiveBackend<L>` + carved↔Church cast** — proves
   the "swap the representation" claim on a real second backend. — *validates the API.*

Items 1–4 are the ones I'd do first: they make the S-expression layer *legible and
self-checking* without needing the full ACL2 metatheory, and they directly answer the
"produce / parse-out / reduce, over one trait, for both a test interp and multiple HOL
reps" question.

---

## 5. Open questions for us

- **Atom payload.** Atoms are `bytes` today. ACL2 atoms are richer (symbols with
  packages, numbers, characters, strings). Do we keep `atom = bytes` and layer a
  *typed* atom view on top (symbol/number/char/string as a parse of the bytes), or push
  the atom taxonomy into the carved type? I lean: keep `bytes` at the carved layer,
  add a typed-atom `SExprRep` view above it (so ACL2's atom zoo is another cast).
- **Certified vs trusting observation.** For fuzzing we may want a *fast, trusting*
  `view` (no `Thm`) and a *certified* `view` (with `Thm`) — probably two methods, or a
  `const CERTIFIED: bool`. Which is the default?
- **Where does `SExprRep` live?** It's logic-neutral like `covalence-inductive`, and
  wants to be usable by both the Rust interpreter (no kernel dep) and the HOL backends.
  I'd put the trait in a small logic-neutral crate (or in `covalence-inductive`), with
  the HOL impls in `init`. Does that fit the base/eval/top layering you want to rename?
- **Relationship to K's matching.** The `view`/`cast`/reduce shape is *also* what K's
  "simple matching fragment" (constant reductions) wants. Worth deciding early whether
  `SExprRep`+`LispEval` is a special case of the K matching machinery or a peer.
- **How much ACL2 do we actually want first?** The two induction theorems +
  `SExprRep`/deparse/test-interp give a compelling *Lisp* story. Full ACL2 (measures,
  ordinals, the axiom catalogue, book import) is a much bigger commitment — worth
  scoping as its own line rather than bundling into "Lisp support."
