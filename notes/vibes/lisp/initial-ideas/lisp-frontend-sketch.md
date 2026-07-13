# A bottom-to-top Lisp frontend + REPL (discussion sketch, agent-authored)

Sketch of a clean Lisp frontend parallel to `covalence-haskell`, plus the
"S-expressions first-class everywhere / tagged-S-expr IR / S-expr languages for
(mutually) inductive definitions" program. Design + a concrete REPL demo transcript.
Not committed; part of the `sketch-separation.md` discussion.

## 0. Why Lisp is the *dual* of the Haskell frontend (and why that's the point)

The two frontends demonstrate the two roles S-expressions play:

| | **Haskell frontend** (`covalence-haskell`) | **Lisp frontend** (`covalence-lisp`, new) |
|---|---|---|
| surface | its own syntax (`\x -> e`) | **is** S-expressions |
| the lowering | surface → SExpr IR (real work) | **identity** (surface = IR) |
| the interesting part | *parsing / desugaring* | *evaluation + metaprogramming* |
| what it shows | S-expr as a **compile target** | S-expr as a **native surface + a program you run** |
| shared | SExpr IR · `Realize` backends · the kernel bridge (`HolBackend`) · `covalence-hol-api` | same |

So Lisp reuses almost the whole Haskell stack below the surface and adds the two things
Haskell doesn't have: a **live evaluator** (Lisp is a programming language) and
**homoiconic metaprogramming** (code = data = the IR). That's exactly the
"user-interaction/debugging + metaprogramming" you want.

## 1. S-expressions first-class: one IR, tagged by preference

### The consolidation
Today there are ~4 S-expr representations (`inductive-support.md`/`lisp-acl2-answers.md`):
carved HOL `Term`, Church HOL `Term`, `covalence-sexp` (Rust, dialect-parametrized),
`covalence-haskell::sexpr::SExpr` (Rust, `Sym|Nat|Str|List`, canonical printer). To make
S-expr "first-class in general," pick **one canonical Rust IR** that every sublanguage
targets and every backend consumes. I'd promote `covalence-haskell::sexpr::SExpr` into a
tiny shared crate (`covalence-sexpr`, `crates/lib/sexpr` or fold into `covalence-sexp`)
— it already has arbitrary-precision `Nat` atoms + a canonical single-line printer +
round-trip. Then `covalence-haskell`, `covalence-lisp`, the grammar crate, SpecTec, K,
etc. all emit/consume it. **One human-readable IR to read, diff, and debug.**

### General vs *tagged* S-expressions (you prefer tagged — agreed)
- A **general** S-expr is untyped: `atom | (e …)`. Great for raw Lisp data; useless as a
  self-describing IR (you can't tell a lambda from a let from a call).
- A **tagged** S-expr fixes a *vocabulary*: the head symbol names the construct and
  determines the shape — `(lambda x body)`, `(let n v body)`, `(app f x)`, `(+ a b)`,
  `(data Nat () ((zero) (succ (Nat))))`. This is what `HolBackend` already emits
  (`(lambda x b)`, `(let n v b)`, `(f x)`).

Make "tagged" a real thing via a **schema layer**: each sublanguage declares a
`TagSchema` — a table of `tag → arity/shape` (fixed args, rec args, binders, keyword
args). Then:
- **Tagged S-expr ⇄ typed AST is a checked bijection per language** (parse a tagged node
  into the AST node for that tag; deparse the AST node back). This is *literally the
  parsing-relations idea* (`parsing-relations.md`) one level up: the schema is a
  relation between tagged S-exprs and typed nodes; `transpose` gives the printer.
- **Metaprogramming** = manipulate the tagged S-expr with the schema as the type
  discipline (a macro is a tagged-S-expr → tagged-S-expr function; hygiene later).
- **Debugging/interaction** = every layer can `deparse` its state to a tagged S-expr and
  every input can be a tagged S-expr — one uniform inspect/serialize surface.

Suggested rule for the whole project: **every sublanguage MUST have a `to_sexpr`
(tagged) and SHOULD have a `from_sexpr`; general (untagged) S-expr is the fallback only
where a construct genuinely has no fixed shape (raw Lisp quote/data).**

## 2. The bottom-to-top layering (the "clean bottom-to-top" ask)

```
L4  REPL / web /lisp        interactive read–eval–print + :commands (drives L0–L3)
L3  kernel bridge           tagged S-expr → kernel: defun→HOL def, data→inductive type,
                            defthm→theorem+proof (via covalence-hol-api + the inductive
                            engine + the proof-format linker)
L2  Lisp evaluation         SExpr → value; special forms (quote/if/cond/let/lambda/defun);
                            car/cdr/cons/eval; the `LispEval` trait over `SExprRep`
                            — TWO instances: TestLisp (fast Rust) + CertifiedLisp (carved
                            HOL, each step a proved equation), differential-tested
L1  tagged schemas          SExpr ⇄ typed AST per construct (the tag vocabulary +
                            parse/deparse relation; the Realize backends live here)
L0  reader / printer        bytes/text ⇄ SExpr  (today: covalence-sexp / haskell reader;
                            eventually the *relational* parser — parsing-relations.md —
                            so parse/deparse come from one grammar relation)
```

Each layer is independently useful and testable, and each is *mostly already present*
(L0 readers exist; L1 `Realize`+`HolBackend` exist; L2's `LispEval` is the trait from
the Lisp/ACL2 answers + the `Lisp` HOL theory; L3 has `covalence-hol-api` + the inductive
engine + the proof linker). The new crate mostly *wires* them and adds the interpreter +
special forms + the REPL.

## 3. Crate architecture

- **`covalence-sexpr`** (`crates/lib/sexpr`, or reuse `covalence-sexp`) — the canonical
  first-class S-expr IR + reader/printer. Kernel-agnostic, wasm-clean.
- **`covalence-lisp`** (`crates/lang/lisp`, parallel to `crates/lang/haskell`):
  - `reader` — S-expr in (reuse `covalence-sexpr`).
  - `ast` — the tagged special-form AST (`Quote/If/Cond/Let/Lambda/Defun/App/Data/…`) +
    the `TagSchema` and the `to_sexpr`/`from_sexpr` pair.
  - `eval` — the `LispEval`/`SExprRep` interpreter (TestLisp).
  - `lower` — tagged AST → SExpr (identity-ish) and → kernel via the shared `HolBackend`
    (feature `hol`), reusing the Haskell path.
  - `hol` (feature) — the kernel bridge (L3): `defun`→def, `data`→inductive, `defthm`→
    linker. Uses `covalence-hol-api`.
- **`covalence-lisp-repl`** (`crates/app/lisp-repl`, or a `cov lisp` subcommand) — the
  CLI REPL (L4).
- **web `/lisp`** — the browser REPL, parallel to `/haskell` (via `covalence-web-kernel`,
  a `lisp_eval`/`lisp_lower` wasm fn like `haskell_to_sexpr`).

Everything below L3 is zero-TCB (surface + interpreter). L3 is the only kernel-touching
part, and it goes through the *trait* (`covalence-hol-api`), so "change the TCB ⇒ change
the trait impl" holds, same as Haskell.

## 4. The traits (reuse, don't reinvent)

- `SExprRep` + `LispEval` (proposed in `lisp-acl2-answers.md`) — the interpreter is
  `impl LispEval for TestLisp` (Rust value) and `impl LispEval for CertifiedLisp`
  (carved HOL term, each step a `prec_eq` equation). The REPL runs TestLisp for speed
  and can `:certify` a form by re-running it certified and showing the `Thm`.
- `Realize` (existing) — tagged AST/SExpr → backend (`SExprLower` for pretty text,
  `HolBackend` for kernel terms).
- `TagSchema` (new, small) — the tag vocabulary + the tagged⇄AST bijection; shared shape
  so Haskell, Lisp, SpecTec, K all declare their vocabularies the same way.

## 5. S-expression languages for (mutually) inductive definitions

A **tagged-S-expr DSL that lowers to the inductive engine.** One `data` form per type; a
list of them for mutual recursion:

```lisp
; a single inductive type
(data sexpr ()
  ((atom  (bytes))
   (snil)
   (scons (sexpr) (sexpr))))

; mutually inductive (a toy expr/stmt pair)
(data* ((expr ()  ((lit (nat)) (var (sym)) (add (expr) (expr))))
        (stmt ()  ((assign (sym) (expr)) (seq (stmt) (stmt))))))
```

- `data`/`data*` parse (via the schema) to `covalence_inductive::InductiveSpec` (single)
  or a mutual bundle, then `realize` through a backend (carved/church/…) to get the
  kernel type + constructors + recursor + freeness/induction (§the inductive engine).
- **This is the S-expr surface for the inductive engine** — user-facing type definitions
  *and* the metaprogramming target (generate `InductiveSpec`s programmatically, print
  them back as `data` forms for inspection). Mutual recursion is "just a list of specs"
  once the engine grows a mutual bundle (currently a v1 skeleton — see
  `inductive-support.md` §7.6).
- Because it's tagged S-expr, the *same* form is the debug view, the serialization, and
  the metaprogram input — the homoiconic win.

(Analogously: `defun` → a HOL definition via the recursion engine + measures; `defthm
name stmt proof` → the proof-format linker; `deftype`/`data` → the inductive engine. The
Lisp frontend is the *union surface* over the kernel's definitional forms.)

## 6. The REPL demo (concrete)

A read–eval–print loop over tagged S-exprs, with `:commands` that expose each layer. It
runs TestLisp by default (fast), and reaches the kernel on demand.

```text
covalence-lisp REPL — type S-expressions; :help for commands
λ> (cons 1 (cons 2 nil))
(1 2)                                  ; L0–L2: read, eval, deparse (tagged)
λ> (append (list 1 2) (list 3 4))
(1 2 3 4)
λ> :sexpr (lambda (x) x)
(lambda x x)                           ; L1: the canonical tagged S-expr IR
λ> :lower (lambda (x) x)               ; L3: same input as a real kernel Term
⊢ carved: scons (atom "lambda") (scons (atom "x") (scons (atom "x") snil)) : sexpr
λ> :certify (append (list 1) (list 2)) ; L2 certified: re-run in the kernel
⊢ append (scons 1 snil) (scons 2 snil) = scons 1 (scons 2 snil)   [genuine Thm]
λ> (data nat () ((zero) (succ (nat))))  ; L3: define an inductive type
defined nat : {zero, succ} — recursor + induction + freeness available
λ> :thm len_append                     ; a theorem already in the Lisp theory
⊢ ∀ y x. len (append x y) = len x + len y
λ> (defthm rev-rev (== (rev (rev xs)) xs)   ; state + prove (proof linked by name)
     :proof rev-rev.proof)
rev-rev: HOLE (no proof found for rev-rev)   ; honest: statement stands, proof pending
λ> :deparse (scons (atom "a") snil)    ; parse-out: kernel Term → text (needs deparse)
(a)
λ> :quit
```

Command set: bare form = eval+print; `:sexpr` (show tagged IR), `:lower` (kernel Term),
`:type`/`:kind` (HOL type of the lowered term), `:certify` (certified eval + `Thm`),
`:deparse` (kernel Term → text — the deparse gap from `parsing-relations.md`),
`:thm`/`:defthm`/`:check` (theorems via the linker), `:data`/`:defun` (definitions),
`:load file`, `:trace`, `:help`. The web `/lisp` page is the same loop in the browser.

**Note:** the demo is *honest about the gaps* — `:certify`/`:lower` work today (carved +
`HolBackend`), `:deparse` needs the deparse function, `:defthm` needs the linker + more
rule coverage, `defun`→HOL-def and non-toy `data` need the generic carver + measures.
The REPL is exactly the surface that makes those gaps *visible and demoable*.

## 7. What's reusable vs new (so this is small)

- **Reuse (already built):** the S-expr reader/printer; the `SExpr` IR; `Realize` +
  `HolBackend` (S-expr → carved Term); the `sexpr` type + the `Lisp` theory
  (`car/cdr/cons/consp/atom?/len/append`, `append_assoc`, `len_append`);
  `covalence-hol-api`; the proof-format linker; the web-kernel wasm plumbing.
- **New (the actual work):** the `TestLisp` interpreter (special forms + `eval`); the
  `TagSchema` + tagged⇄AST bijection; the `data`/`defun`/`defthm` forms → engine/linker;
  the REPL loop (CLI + web). Most of this is L1/L2 surface work, zero-TCB.
- **Depends on the discussion items:** `SExprRep`/`LispEval` (the Lisp/ACL2 note), the
  deparse function (parsing-relations note), the generic carver + mutual recursion
  (inductive note), measures for `defun` (inductive note §7.10).

## 8. Suggested build order

1. **Promote the canonical `covalence-sexpr` IR** + the `TagSchema` layer (unblocks
   "first-class S-expr everywhere," and Haskell adopts it too).
2. **`covalence-lisp` L0–L2**: reader + tagged AST + `TestLisp` interpreter (car/cdr/
   cons/if/cond/let/lambda/defun-as-closure/quote). Pure surface, zero-TCB.
3. **REPL (CLI) + `/lisp` web page** over L0–L2 — a *live Lisp* demo immediately, parallel
   to `/haskell`. `:lower`/`:certify` reuse `HolBackend` for the kernel bridge.
4. **`data` → inductive engine** (single type first; mutual after the engine grows it).
5. **`defthm` → linker**, **`deparse`**, **`defun` → HOL def (measures)** — as the
   underlying gaps land.

Steps 1–3 give a compelling parallel-to-Haskell **live Lisp REPL (browser + CLI)** on
top of what already exists, and make S-expressions first-class as the shared tagged IR —
without needing the deeper kernel work first.

## 9. Open questions for us

- **Consolidate to one `SExpr` IR now, or keep per-crate?** I lean: one shared
  `covalence-sexpr` (with tagged-schema support) that Haskell + Lisp + grammar + SpecTec
  all use — it's the "first-class" ask, and it kills the 4-representations sprawl.
- **How much Lisp semantics** — a clean small Scheme-ish core (the demo above), or aim at
  ACL2's evaluation model (applicative Common-Lisp subset, `equal`, guards)? I'd do the
  small core first and let ACL2 be a *dialect* (a `TagSchema` + a stricter eval) on top.
- **Tag schema formalism**: is a `TagSchema` just a Rust table, or itself an S-expr
  language (a schema written as tagged S-exprs, so schemas are metaprogrammable too)?
  The latter is very on-theme (schemas-as-data) but a step further.
- **REPL evaluation trust**: default to `TestLisp` (fast, untrusted) and make `:certify`
  the opt-in kernel path — or always run certified? I'd default fast, certify on demand,
  and differential-test the two in CI (the fuzzing story from the Lisp/ACL2 note).

## 10. A *real* standard Lisp + theorems about it + proptest-as-theorem + ACL2-inside

The sections above treat Lisp mostly as a homoiconic surface over the kernel's
definitional forms. The additional ask is stronger and, I think, the actually-exciting
version: **a genuine standard-Lisp REPL you run real programs in, *plus* the ability to
state and prove theorems about those programs, with property-based testing that
*upgrades into* theorems — and eventually our ACL2 living inside that Lisp.** This is the
ACL2 architecture exactly (a Lisp that is also a logic), rebuilt on our substrate. Here's
how the pieces line up with what we already have.

### 10.1 Two evaluators, one language — the load-bearing distinction

The whole design rests on the `TestLisp` / `CertifiedLisp` split from
`lisp-acl2-answers.md`, promoted to first-class:

| | **TestLisp** (the *runtime*) | **CertifiedLisp** (the *logic*) |
|---|---|---|
| what it is | a fast native Rust interpreter of standard Lisp | the same semantics as HOL equations over `sexpr` |
| speed | full native speed (this is the "real REPL") | kernel-speed, per-step proved |
| role | run programs, fuzz properties, interactive dev | *prove* equalities/properties as `Thm`s |
| trust | untrusted | TCB-bridged via `covalence-hol-api` |
| bridged by | differential testing + `execute`-style certified-run | — |

The key claim (ACL2's founding trick): **for the applicative/total fragment, these two
agree**, and that agreement is what makes "run it" and "prove things about it" the same
language. TestLisp is what you type at; CertifiedLisp is what `defthm` reasons in;
`execute` (base relation calculus) mints `Eval(prog, input, output)` witnesses from
running TestLisp so a concrete run *is* a positive kernel fact.

### 10.2 A standard Lisp, concretely (which Lisp?)

I'd target an **applicative Common-Lisp subset = essentially ACL2's ground language**,
because it is *designed* to be a logic:

- pure, total, first-order-ish (functions over the `sexpr` universe: symbols, numbers,
  conses, characters, strings), no destructive ops, no unbounded side effects;
- `defun` (total recursive functions with an admitted termination measure), `defconst`,
  `cond`/`if`/`let`/`let*`, `quote`, backquote, the `sexpr` primitives
  (`car cdr cons consp atom eq equal + * < …`) — this is exactly the `Lisp` HOL theory
  (`init/lisp.rs`) extended;
- *stretch* (Scheme-ish): first-class closures/`lambda` at runtime — TestLisp handles
  these natively; CertifiedLisp only needs them for the fragment you prove about.

Start with the **ACL2 ground fragment** (it's the sweet spot: real programs, and every
`defun` already carries the measure discipline the recursion engine wants). "Full Common
Lisp" (macros expanding to it, packages, mv/values) is a later dialect layer. This makes
§9's "small Scheme core vs ACL2 model" question concrete: **the standard Lisp *is* the
ACL2 ground language; Scheme-y closures are a superset TestLisp runs but we don't (yet)
prove about.**

### 10.3 Theorems about Lisp programs (`defthm`)

Once `defun` lands a function as a HOL definition (via the recursion engine + measure —
`inductive-support.md` §7.10), a theorem about it is *just a HOL goal over carved
`sexpr`*, discharged through the proof-format linker. This already exists in embryo:
`init/lisp.rs` proves `append_assoc` and `len_append` — the ACL2 archetypes — by hand.
`defthm` is the surface that lets a user state one:

```lisp
(defun app (x y) (if (consp x) (cons (car x) (app (cdr x) y)) y))
(defthm app-assoc (equal (app (app x y) z) (app x (app y z)))
  :proof app-assoc.proof)          ; proof = replayed script (untrusted data, kernel-checked)
```

The `defthm` → linker path is the same one Haskell's proof format uses. The measure on
`app` is what makes `app` a legitimate HOL function; the theorem is then ordinary
equational HOL reasoning + `list`/`sexpr` induction (which the inductive engine provides).

### 10.4 proptest-as-theorem — the piece I'm most excited about

This is a **ladder from cheap evidence to proof**, with the runtime and the logic being
the same language so nothing is re-encoded:

```lisp
(defproperty app-assoc (x y z)              ; a property = a boolean Lisp term over vars
  (equal (app (app x y) z) (app x (app y z))))

λ> (check app-assoc)          ; RUNG 1: fuzz with TestLisp (proptest), gather counterexamples
checked 10000 random cases — no counterexample            [evidence, not proof]

λ> (check app-assoc :exhaustive :depth 4)   ; RUNG 2: bounded-exhaustive over small sexprs
all 3720 cases ≤ depth 4 pass                              [bounded verification]

λ> (prove app-assoc)          ; RUNG 3: discharge the ∀ as a genuine Thm via the kernel
⊢ ∀ x y z. app (app x y) z = app x (app y z)               [proof — a real Thm]
```

The three rungs share **one property object** (`(x y z) ⊢ boolLispTerm`):

- **RUNG 1 — proptest.** Generate random `sexpr`s (the repo already has
  `kernel-proptests`), run the property under **TestLisp**, minimize counterexamples.
  Fast, finds bugs, no kernel. A *failure* here is itself a certifiable fact: `execute`
  turns the failing run into `⊢ ¬ (property witness)` — a **counterexample theorem** (a
  concrete refutation is a positive `Eval` fact, hence kernel-mintable; this is the
  "positive-only execute" story from `parsing-relations.md` used for disproof).
- **RUNG 2 — bounded-exhaustive.** Enumerate all `sexpr`s up to a depth and check. Still
  TestLisp; still not a ∀-proof, but a *complete* check of a finite subdomain — and each
  case is `execute`-certifiable, so "bounded-verified" can be a real (finite conjunction)
  `Thm`, not just a test.
- **RUNG 3 — prove.** The property is a HOL `∀` over `sexpr`; discharge it with
  induction + the linker. The *same S-expr* that was fuzzed is now the theorem statement.

The upgrade path is the point: **the property never changes form** as it climbs from test
to theorem. That's "proptest-as-theorem" — proptest is rung 1 of a ladder whose top rung
is a kernel `Thm`, and the substrate makes the rungs literally the same object at
different trust levels (TestLisp evidence → `execute`-certified finite facts → HOL ∀).
This is a genuinely novel demo: *a property-based test you can click "prove" on.*

(Design note: `check` should also record its evidence as a first-class artifact — "fuzzed
10k cases, seed S, no counterexample" is a content-addressable claim, weaker than a `Thm`
but signable/storable. That's the `develop`-branch green-evidence tier vs the `main`
sound-`Thm` tier from `sketch-separation-thoughts.md`, expressed *inside* the Lisp.)

### 10.5 ACL2 *inside* the Lisp — as a dialect, not a port

ACL2 is "an applicative Common Lisp + a first-order inductive logic + a proof
automation loop." We already have the first two as the standard-Lisp REPL (§10.2) + the
kernel. So **ACL2-inside-the-Lisp is a dialect layer**, not a separate system:

- **`defun` with the ACL2 discipline** — a `defun` that *requires* an admitted measure
  and admits the function to the logic (not just to TestLisp). This is the standard Lisp's
  `defun` with the recursion-engine termination obligation made mandatory. A plain
  TestLisp `defun` is "runtime only"; an ACL2 `defun` is "runtime + logic."
- **`defthm` + the waterfall** — ACL2's proof automation (simplification, induction
  heuristics, generalization) becomes a **tactic/handler stack over our kernel** — the
  "reasoning as environment-dispatched handlers" seed (`env-rewrite-reduce-deadlock`,
  the async-prover `Env`). The ACL2 waterfall is one such handler bundle; the proof it
  produces is replayed as untrusted script data through the linker. **We get ACL2's
  automation without trusting ACL2** — it proposes, our kernel checks.
- **`the-method` / proptest first** — ACL2 practice is "test before you prove"; §10.4's
  `check`→`prove` ladder *is* the-method, built in.
- **surface** — ACL2 is `TagSchema_acl2` (its `defun`/`defthm`/`defstobj`/`encapsulate`
  vocabulary) + a stricter evaluator (guard verification, the applicative restriction) on
  top of the standard Lisp. Our existing ACL2 work (`init/lisp.rs`, the ACL2 archetype
  theorems, the planned `logics/acl2` object logic from `sketch-separation-thoughts.md`)
  becomes *the dialect definition*, and it runs in the same REPL: you type standard Lisp,
  `(in-package "ACL2")` (or a `:acl2` mode) turns on the discipline.

So the layering is: **standard Lisp (TestLisp runtime + CertifiedLisp logic)** at the
base, **ACL2 = a dialect** (mandatory measures + guard discipline + the waterfall handler
stack + its tag vocabulary) on top, and **proptest-as-theorem = the-method** wired
through both. This is ACL2's own architecture — a Lisp that is also a theorem prover —
reconstructed so the trusted core is *our* kernel, not the Lisp implementation.

### 10.6 What this adds to the build order (§8)

Insert after step 3 (once the live TestLisp REPL exists):

- **3a. `defproperty` + `(check …)`** — proptest over TestLisp (reuse `kernel-proptests`).
  Cheapest high-value demo: property-based testing in the REPL, zero kernel. Record
  green-evidence artifacts.
- **3b. `execute`-certified runs** — a concrete `(app '(1) '(2))` run becomes an
  `⊢ Eval …` fact; counterexamples become refutation `Thm`s. First real kernel touch for
  the runtime.
- **After step 5 (`defun`→HOL def + `defthm`→linker): `(prove …)`** — the top rung; the
  property proved as a ∀-`Thm`. Then the ACL2 dialect (mandatory measures + waterfall
  handler + `TagSchema_acl2`) as its own milestone.

### 10.7 Open questions (additions to §9)

- **Runtime/logic agreement scope.** TestLisp = CertifiedLisp only for the total
  applicative fragment. Where's the boundary (bignums yes; floats/chars edge cases;
  runtime closures no)? The differential-test CI defines it empirically; the *proved*
  agreement is a theorem we state for the ACL2 fragment.
- **Counterexample theorems.** Is `⊢ ¬property(witness)` worth minting as a real `Thm`, or
  is a signed green/red evidence artifact enough for rungs 1–2, reserving `Thm` for rung
  3? (I lean: evidence artifact for 1–2, `Thm` for the refutation *witness* when cheap.)
- **How much waterfall.** Do we port ACL2's heuristics, or start with "proptest + manual
  script + our existing tactics" and let the waterfall be a later handler bundle? (Start
  minimal; the handler architecture is the extensible seam.)
- **Numbers.** ACL2's numeric tower (rationals, complex-rationals) vs our stdlib
  (`nat/int/rat/real`). The standard Lisp should use the stdlib numbers; ACL2 dialect
  pins the ACL2 tower. Reconcile via the literal-atom zoo (`atoms.md`).
