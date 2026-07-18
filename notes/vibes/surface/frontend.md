+++
id = "N0033"
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

# Covalence — Frontend & UX Vision

> **DESIGN SKETCH — the frontend counterpart to [`VISION.md`](../vision/VISION.md)
> (the kernel vision).** What the system feels like to *use*: the authoring
> experience and the mechanism that makes many logics share one surface. The
> concrete authoring syntax is [`surface-syntax.md`](./surface-syntax.md) /
> [`surface-compiler.md`](./surface-compiler.md); the proof-theoretic mechanism
> (handler dispatch, internal languages) is [`metatheory.md`](../logics/metatheory.md)
> §7–9; untrusted computation feeding the kernel is
> [`observers.md`](../observers/observers.md).

---

## 1. The one-sentence frontend vision

> **You author in a single surface language; the system tracks every term
> and proposition as it is interpreted across many logics, and lets you ask
> — and prove — *what is provable in which logic, on which language*.**

The kernel vision is "metatheory is the default mode." The *frontend*
vision is the user-facing consequence of that: the everyday act is not
"prove `P` in the one fixed foundation" but **"work with `P` as a thing
that has several interpretations, and reason about where it holds."** The
foundation (this HOL) is still doing all the proving underneath — but the
user spends their time in a surface that is *about* logics and languages,
not trapped inside one.

---

## 2. What is reusable, and why that drives the UX

The goal is **reusable proofs**. We formalize other logics — FOL and
first-order theories (Peano arithmetic; second-order arithmetic viewed as
a multi-sorted first-order theory), then HOL, then set theories (ZFC,
Grothendieck–Tarski), then type theories (MLTT) — and we **relate** them
(see [`metatheory.md`](../logics/metatheory.md) §3). We do *not* need to support
every theory, nor every form of reasoning, because the point is **first-class
metalogic**: prove `P` in some *weak* logic `W` (say, equational reasoning
à la Crole's *Categories for Types* modulo a simple algebraic theory) and
it holds in *many* interpretations at once — every model of `W`.

The UX consequence: the surface is organized around **"weakest sufficient
logic"** as a first-class choice. Picking a weaker logic is not a
limitation the user works around; it is the move that **maximizes reach** —
the same theorem, more interpretations, no re-proof. The frontend makes
that trade legible and cheap, the way a type system makes "the most
general type" legible and cheap.

---

## 3. The unified surface: terms-as-interpreted

Today there are two registers in the codebase: the low-level **tactic
language** (`covalence-init/src/script`, real and working) and the sketched
**surface language** (folded into `script/`,
[`surface-syntax.md`](./surface-syntax.md), mostly aspirational). The
frontend vision is what unifies them: a surface that carries an abstract
term/proposition **together with its interpretations in various
languages**.

Concretely, the endgame workflow (see [`metatheory.md`](../logics/metatheory.md)
§8.1): a user writes in a **source language** that *lowers to several
targets*. For a source term `S`, the system tracks `ToHOL(S)` and
`ToZFC(S)` as its interpretations, and a statement like

```
   HOL ⊢ ToHOL(S)   ⟹   ZFC ⊢ ToZFC(S)
```

is itself a theorem **of our metalogic** (this HOL), which *also*
formalizes the translations `ToHOL` and `ToZFC`. "Provable in which logic,
on which language" stops being a meta-question the user reasons about
informally and becomes an **ordinary object on screen** — a term with its
interpretations, and entailment queries across them (the
`(spec a |- spec b)` / categoricity questions of
[`surface-syntax.md`](./surface-syntax.md) §6, generalized across logics).

This is the part the kernel docs left vague, stated plainly: **the surface
is not a syntax for one logic; it is a workspace of terms each annotated
with how it reads in each logic we have formalized, plus the proved
morphisms between those readings.**

---

## 4. The mechanism: reasoning as an algebraic effect

What makes one surface serve many logics *without* one bespoke prover per
logic is **handler dispatch**. The tactic engine performs a few
open-ended operations — rewriting, unification, reduction/normalization,
decision — and treats each as an **algebraic effect**: the tactic
*requests* the operation, and the **environment supplies the handler**.
(Full treatment: [`metatheory.md`](../logics/metatheory.md) §7.2.)

For the frontend this is the core UX lever:

- A **first-order** environment makes FOL feel native (first-order
  unification, FOL-shaped tactics); a **higher-order** one makes HOL feel
  native; a **dependent-type** one installs a reducer that knows Π/Σ and
  definitional equality. Switching logics is *switching the installed
  handlers*, not switching tools.
- **Per-problem** specialization is the same mechanism at finer grain: a
  unifier that knows arithmetic so it solves `Bits[n + m] =?= Bits[m + n]`
  for SAIL-style bitvector specs; a reducer JIT-compiled to WASM for a hot
  theory. These are *handlers a user installs for a task*, not forks of
  the prover.
- Crucially, **soundness is independent of the handler**: every handler
  ultimately emits a kernel-checkable obligation (a `Thm`, a rewrite
  witnessed by `=`, a certificate the kernel re-checks). A clever, learned,
  or simply wrong handler is slow or fails — never unsound. This is the
  same guarantee as the "declarative meaning, pluggable computation" north
  star of [`surface-syntax.md`](./surface-syntax.md) §1.1, and the "the
  query planner can be an LLM" analogy of §1.2: the planner can be anything
  because the kernel checks the result.

So **the same surface proof replays under different handler sets**, and the
metalogic can quantify over which handler set corresponds to which object
logic. Logic and metalogic share one surface, one elaborator, one tactic
vocabulary — they differ only in installed handlers
([`metatheory.md`](../logics/metatheory.md) §7.1).

---

## 5. The first taste: S-expressions → propositional logic (done)

The frontend vision is large; the **first** concrete step that makes it
tangible is small — and has **landed** (`init/prop.rs`: propositional logic
reified + proved sound internally, since scaled to the PA deep embedding;
[`metatheory.md`](../logics/metatheory.md) §8,
[`theories-models-and-logics.md`](../logics/theories-models-and-logics.md) §5.5):

1. reify **S-expressions** as a HOL datatype — the universal carrier for
   *all* object-language syntax;
2. define **propositional logic** over them (well-formedness, a
   derivability predicate, a denotation into HOL `bool`);
3. **prove it sound inside the metalogic** (`Derivable_Prop ⌜A⌝ ⟹ ⟦A⟧`) —
   doable precisely because propositional logic is *weaker* than our HOL;
4. **translate a subset of HOL into it** — the first language morphism.

That is the whole frontend loop in miniature: one source fragment, two
readings (HOL term ⇄ propositional formula), and a *proved* relationship
between "provable here" and "provable there" — the base case of §3's
multi-target picture.

---

## 6. The interactive loop: play, then distill

A formal system is only as reusable as it is *approachable*. The
counterpart to the authoring surface is an **interactive frontend** — a
REPL/notebook where you *play*: type a definition, try a proof, see what
reduces, ask whether `P` holds in `W`, get an answer immediately. Low
activation energy is a design goal, not a nicety — the metalogic workflow
of §2 ("find the weakest sufficient logic, transport from there") is
exploratory by nature, and exploration needs a fast, forgiving surface.
Because the kernel compiles to WASM, this runs **in the browser**: zero
install, the kernel itself a small download on the page.

The decisive idea is that **the session transcript is itself an
artifact.** A REPL session is just a sequence of surface directives and
their results — and every result already elaborates to a
kernel-checkable object. So the messy, branch-y record of *play* can be
**distilled into a clean, content-addressed theory/codebase**: dead ends
pruned, scratch names canonicalized, surviving definitions and proofs
reorganized into a library. This is the formal-methods analogue of the
Jupyter-notebook → Python-library ecosystem (jupytext, nbdev): the
notebook is where you think; the library is what you ship.

Distillation is **untrusted, and may be LLM-assisted** — and that costs
nothing in soundness, for exactly the reason handlers are safe (§4): the
distilled theory is re-elaborated and re-checked by the kernel from
scratch. An LLM that reorders, renames, generalizes, or drops steps is an
*editor*, never an *authority*; a bad edit produces a theory that fails
to check, not a false theorem. The same LLM can do the genuinely useful
semantic work — suggest the **weakest logic each result actually used**
(§2), factor a repeated argument into a lemma, or propose the morphism
that ports a result to a second target language (§3).

**The seed exists today.** `covalence-repl` is a working S-expression
REPL over the kernel, and the `.cov` proof-script layer
(`covalence-init/src/script`) already replays *untrusted* proof scripts
against the kernel — including by content hash (the REPL's `check-cov` /
`check-cov-hash`), the first step toward content-addressed fragments (§3,
[`surface-syntax.md`](./surface-syntax.md) §7). A transcript of REPL
commands is the embryonic notebook; the script layer is the embryonic
checked replay. What's missing is the surface language on top (§3, §5)
and the distillation pass — both additive.

---

## 7. From today's tactic language to the unified surface

The progression (status honest):

- **Today.** The S-expression tactic/proof language (`script/`) is real:
  `(#by …)` / `(#proof …)` proofs replayed against the kernel, with the
  **environment already acting as the dispatcher** — name-resolved
  tactics/rules/lemmas, host-tactic registration (`#register-ffi-tactic`),
  and unification kept behind `Env::apply_unify` / `Env::rw_unify` *so a
  custom handler can be registered later*. This is the seed of §4, built
  small on purpose ([`metatheory.md`](../logics/metatheory.md) §7.3).
- **Next.** The reified-syntax layer (§5) and the surface authoring
  language ([`surface-syntax.md`](./surface-syntax.md)) — declarative
  definitions, the `#theory`/`#def`/`#thm` directives, the
  spec-vs-definition distinction.
- **Then.** Generalize the single hard-wired unifier into true
  multi-handler effect dispatch; teach the elaborator to carry an
  *interpretation target* ("elaborate this term in object language `L`");
  carry terms together with their cross-language interpretations in the
  surface. These are the "least compatible / additive work" items of
  [`metatheory.md`](../logics/metatheory.md) §9 — nothing here forces undoing the
  current design.

---

## 8. Where this sits relative to the kernel vision

The two vision docs share one discipline: **external things — a logic, a
program, a clever reasoning strategy — enter the system as objects we
reason about and check, never as black-box trust.** The kernel doc makes
that claim about the *foundation*; this doc makes it about the *experience*
of using the system.
