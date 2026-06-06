# Core library: rich theory at no TCB cost

> **STATUS: WORKING NOTE — extracted from session conversation.**
> Captures the design for Covalence's **core library** ("corelib"):
> a body of foundation theorems (arithmetic, lists, induction
> principles, …) accessible through the
> [`Prover`](../../../../../crates/covalence-shell/src/prover.rs)
> API, with a **paranoid** build that re-verifies everything at
> startup and a **default** build that links in pre-proven Thms. A
> traditional standard library ("stdlib") then sits *on top of*
> corelib, layering richer theory (regex, parsers, advanced
> datatypes) at user's option. Sibling to
> [`kernel-as-os.md`](./kernel-as-os.md); both describe operational
> machinery on top of the layered framework.

The user's framing, verbatim (combined):

> *We need a nice API (wrapped up in covalence-shell) for a standard
> library. The stdlib should be verified at startup in a `OnceCell`
> in a "paranoid" build, but just linked in as pre-proven otherwise
> — and is essential since Prover methods in covalence-shell should
> be able to use the stdlib to discuss e.g. arithmetic on naturals
> and integers but also for example regular expressions, parsers,
> inductive datatypes, etc. This lets us have a very rich theory
> exposed by the Prover API while keeping the actual TCB minimal.* +
> *A better word is probably "core lib" — then the stdlib can be a
> more traditional library on top.*

---

## Contents

1. [Corelib vs stdlib](#1-corelib-vs-stdlib)
2. [Two build modes](#2-two-build-modes)
3. [What corelib contains](#3-what-corelib-contains)
4. [The API on `Prover`](#4-the-api-on-prover)
5. [How corelib mounts into the Kernel](#5-how-corelib-mounts-into-the-kernel)
6. [`OnceCell` + lazy initialization](#6-oncecell--lazy-initialization)
7. [Why the TCB doesn't grow](#7-why-the-tcb-doesnt-grow)
8. [Stdlib on top of corelib](#8-stdlib-on-top-of-corelib)
9. [Connection to federation](#9-connection-to-federation)
10. [Connection to facts-not-proofs](#10-connection-to-facts-not-proofs)
11. [Open questions](#11-open-questions)
12. [Cross-references](#12-cross-references)

---

## 1. Corelib vs stdlib

> **Important caveat (added after the user's correction).** A
> proved theorem is **not** an [authority](./kernel-as-os.md#3-the-kernels-three-tables).
> Authorities *write observations* (BLAKE3 oracle, Ed25519 verifier,
> WASM executor, user, peer kernel, release-build signer). Proved
> theorems are *facts derived from observations + rules* — they ride
> the same trust chain everything else does. So **corelib is just a
> proved theorem (or a corpus thereof)** signed *by* a release
> authority for distribution; corelib is not itself an authority,
> and the same holds for every stdlib library.

The user's distinction:

- **Corelib** — the *foundation* theorems the prover API needs to
  even talk meaningfully about basic data: naturals, integers, lists,
  booleans, induction principles. Compiled into the binary; two
  build modes (paranoid re-derivation or default trust-the-build).
  Essential for `Prover` methods to be ergonomic.
- **Stdlib** — a *traditional library* layered on top of corelib.
  Regex, parsers, inductive-datatype framework, advanced theories.
  Not always compiled in; user opts in to whichever libraries they
  want. Each stdlib library can itself ship in paranoid or default
  mode.

The split matches the conventional layering in other systems:

- Rust: `core` (no-std, foundation) vs `std` (on top, optional dep).
- Lean: `Init` / `core` vs `Mathlib`.
- HOL Light: a small initial kernel-coupled set vs `Library/`,
  `Examples/`, etc.

Corelib's content is *small and stable*. Stdlib content is *large
and evolving*. Both ride the same OnceCell-and-modes machinery
described below.

---

## 2. Two build modes

```rust
// In covalence-corelib (or covalence-shell::corelib):

#[cfg(feature = "corelib-verify")]
fn init_corelib(kernel: &mut Kernel) -> CoreLib {
    // Re-derive every corelib Thm by running the derivation script
    // against the live kernel. If any step fails, panic — startup
    // is broken.
    let script = include_bytes!("../corelib-script.bin");
    CoreLib::derive_from_script(kernel, script)
        .expect("corelib derivation failed; rebuild kernel or corelib")
}

#[cfg(not(feature = "corelib-verify"))]
fn init_corelib(kernel: &mut Kernel) -> CoreLib {
    // Deserialize pre-proven Thms, verify signature, inject under
    // the release authority. No kernel rule applications.
    let prebuilt = include_bytes!("../corelib-prebuilt.sigblob");
    CoreLib::load_signed(kernel, prebuilt)
        .expect("corelib signature verification failed")
}

static CORE_LIB: OnceCell<CoreLib> = OnceCell::new();

pub fn corelib(kernel: &mut Kernel) -> &'static CoreLib {
    CORE_LIB.get_or_init(|| init_corelib(kernel))
}
```

The two paths produce identical `CoreLib` values at runtime. The
*provenance* differs; the consumed object doesn't.

### Build artifact

Whoever builds corelib produces *both* artifacts:

- `corelib-script.bin` — the derivation script (a sequence of
  serialized rule applications). Used by paranoid builds.
- `corelib-prebuilt.sigblob` — the pre-proven Thms, signed by the
  release authority. Used by default builds.

Both are content-addressed and shipped together (the signed blob
references the script's hash; the build process verifies they
agree). A user who doesn't trust the build can enable
`corelib-verify`; a user who does can use the default and avoid the
startup cost.

The same shape applies to stdlib libraries; each ships its own
script + sigblob, each has its own feature flag.

---

## 3. What corelib contains

Starting list (small now; will grow conservatively — corelib must
stay tractable to audit):

- **Naturals**: `Nat` type, `0`, `succ`, `+`, `*`, `<`, induction
  principle; basic theorems (commutativity, associativity,
  distributivity, well-ordering).
- **Integers**: `Int` type, embedding from `Nat`, signed arithmetic,
  ordering, basic theorems.
- **Booleans + propositional reasoning**: the existing
  [`bool`](../../../../../crates/covalence-kernel/src/term.rs) is
  kernel-primitive; corelib adds laws (de Morgan, distribution,
  tautology helpers).
- **Lists**: polymorphic `List α`, `nil`, `cons`, `append`, `map`,
  `fold`; induction principle; basic theorems.
- **Option / Result**: standard ADTs as defined types.
- **Equational-reasoning helpers**: `rewrite_under_eq`,
  `cong_*_intro`, etc. — common patterns the Alethe and OpenTheory
  bridges already lean on.

That's it for corelib. Regex, parser combinators, inductive-datatype
*framework* — all are stdlib material (see [§8](#8-stdlib-on-top-of-corelib)).
The principle: **corelib is what every Prover method might need**;
anything more specialized belongs upstream.

Each corelib entry is a small theory `T_thing` defined as a
[layer-3 theory](../../layered-framework/notes/modified-hol.md#33-top-theories-morphisms-interpretations)
inside modified HOL.

---

## 4. The API on `Prover`

Two access patterns, both essential.

### 4.1 Named accessors for common things

```rust
pub trait Prover {
    // existing methods...

    // -----------------------------------------------------------
    // Corelib: naturals
    // -----------------------------------------------------------

    /// The Nat type.
    fn nat_ty(&mut self) -> Result<Self::Type, ProverError>;

    /// Construct `a + b : Nat`.
    fn nat_add(&mut self, a: Self::Term, b: Self::Term)
        -> Result<Self::Term, ProverError>;

    /// Theorem: `∀a b. a + b = b + a`.
    fn nat_add_comm(&mut self) -> Result<Self::Thm, ProverError>;

    /// Theorem: `∀a b c. (a + b) + c = a + (b + c)`.
    fn nat_add_assoc(&mut self) -> Result<Self::Thm, ProverError>;

    // ... etc; same shape for other corelib theorems
}
```

Ergonomic; obvious how to use; tab-completable.

### 4.2 Generic lookup for the long tail

```rust
pub trait Prover {
    /// Look up a corelib theorem by name. The naming convention is
    /// `theory_name::theorem_name`, e.g.
    /// `"nat::add_comm"`, `"list::append_assoc"`.
    ///
    /// Returns `Err(ProverError::NotImplemented(name))` if the
    /// corelib doesn't include this theorem — frontends can route
    /// around it or surface the gap.
    fn corelib_thm(&self, name: &str)
        -> Result<Self::Thm, ProverError>;

    /// Look up a corelib term former.
    fn corelib_term(&mut self, name: &str, args: &[Self::Term])
        -> Result<Self::Term, ProverError>;

    /// Look up a stdlib theorem (see §8). Returns NotImplemented if
    /// the relevant library isn't loaded.
    fn stdlib_thm(&self, library: &str, name: &str)
        -> Result<Self::Thm, ProverError>;
}
```

The generic API is the load-bearing one for downstream shells (Alethe
needs many theorems; OpenTheory has its own naming; SAT/SMT frontends
need their own subsets). Named accessors are a friendly layer for
high-traffic cases.

### 4.3 Discovery

```rust
pub trait Prover {
    /// List theorems in a corelib theory.
    fn corelib_list(&self, theory: &str)
        -> Result<Vec<&'static str>, ProverError>;

    /// List all corelib theories.
    fn corelib_theories(&self) -> Result<Vec<&'static str>, ProverError>;

    /// List loaded stdlib libraries.
    fn stdlib_libraries(&self) -> Result<Vec<&'static str>, ProverError>;
}
```

For interactive REPL use, IDE autocomplete, and the
[FUSE projection](./kernel-as-os.md#5-fuse-is-the-externalization)
of corelib content.

---

## 5. How corelib is identified and accessed

> **Corelib is a content-addressed value, not a filesystem path.**
> Its canonical identity is the hash of its serialized
> (arena + UF + name-table) blob. The
> [Kernel-as-OS](./kernel-as-os.md) framing — the `/auth/...`
> filesystem — is for **authorities** (writers of observations);
> proved theorems and libraries are **values**, identified by hash,
> living in the content-addressed store. Tree-shaped navigation
> *can* be overlaid onto a library (so a user can browse it as
> `nat/add_comm`), but the internal primitive is content-addressing,
> not paths.

### 5.1 The artifact

A corelib distribution bundle is:

- **Serialized arena + UF**, with an internal **name table**
  mapping logical names (e.g., `"nat::add_comm"`) to `TermId`s. The
  whole thing is a single CA blob with hash `H_corelib`.
- A **signature** by the release authority over `H_corelib`. This
  is an observation `release.signed(H_corelib, sig_bytes)` recorded
  in the kernel's fact table.

```
corelib distribution = (
    blob:      Arena + UF + name_table,    ← content-addressed; identity = H_corelib
    signature: release_authority sig over H_corelib,
)
```

### 5.2 Loading

The user (or `OnceCell` init) calls something like:

```rust
let corelib = framework.load_library(H_corelib)?;
```

The framework:

1. Fetches the blob at `H_corelib` from the content-addressed store
   (paranoid: re-derive via script; default: deserialize the
   shipped blob).
2. Verifies the release authority's signature over `H_corelib`
   (this verification is itself an observation; the user's trust
   in `release_authority` makes it actionable).
3. Imports the arena+UF into the kernel under the framework's
   import machinery.
4. Returns a handle exposing name-table lookups
   (`corelib.thm("nat::add_comm") -> Thm`).

### 5.3 The optional filesystem overlay

The Kernel *can* expose libraries through tree-shaped paths for
navigation — e.g., `kernel.read("/lib/corelib/nat/add_comm")`
resolves to the Thm. This is a **convenience overlay** for users
who want to browse, not the primitive. The library's canonical
identity remains `H_corelib`; two users mounting the same library
at different paths are talking about the *same* library.

```
content-addressed substrate                    overlay (optional)
─────────────────────────────                  ──────────────────
H_corelib  → arena + UF + name table   ←──→   /lib/corelib/
                                               ├── nat/
                                               │     ├── add_comm
                                               │     └── ...
                                               └── ...
```

### 5.4 Why not authority-shaped

The corelib doesn't write observations. It's not a source of facts
about the world. It's a *bundle of proved Thms* derived from the
substrate's rules. Authorities (BLAKE3, Ed25519, the release signer,
the user) are who *generated* the observations that the corelib's
proofs eventually discharged — but the corelib itself just hands
out Thms. **No new authority is created when a library is loaded.**

The release authority *is* an authority — it owns a `signed`
relation over CA hashes. That's where signature-based trust enters
the system. Loading the corelib uses the release authority's
observations indirectly, but the corelib is the *value* being
vouched for, not the voucher.

---

## 6. `OnceCell` + lazy initialization

The corelib initializes **once per process**, lazily — first time
some `Prover::corelib_*` method is called, or eagerly via
`corelib::ensure_loaded()` at startup.

Why `OnceCell` rather than eager init in `main`:

- **Library users.** Code that uses `covalence-shell` as a library
  (Python bindings, embedded prover, federated peer) doesn't have a
  predictable `main`. Lazy init means "corelib is there when you
  reach for it."
- **Testing.** Many tests don't need corelib. `OnceCell`'s lazy
  init means tests that don't use it don't pay the init cost.
- **Errors at the right time.** A paranoid build's corelib
  derivation could fail (kernel changed shape; corelib stale).
  Lazy init surfaces the failure at first corelib use, not at
  process start — arguably worse for surprise but better for
  debuggability.

The trade-off: paranoid users probably want eager init at startup
(fail fast on a broken corelib). Provide both:

```rust
pub fn ensure_loaded(kernel: &mut Kernel) {
    let _ = corelib(kernel);
}
```

Call it at the top of `main` if you want eager; otherwise lazy.
Stdlib libraries follow the same pattern with their own `OnceCell`s.

---

## 7. Why the TCB doesn't grow

Each corelib Thm enters the system **as a Thm**, not as an axiom. In
paranoid mode this is operationally true (the Thm was produced by
the kernel's own rules during init). In default mode it's true *by
construction*: the build process produced it via the kernel's rules
on the build machine; the signed blob is the witness that the build
was honest; the user trusts the release authority's key the same way
they trust any other authority.

The trust set under default mode grows by *one* entry:
`{corelib_authority_key signs only honest corelibs}`. Under paranoid
mode it grows by *zero* (the local kernel re-verifies). Compare:

| Mode | Trust set additions | Startup cost | Kernel-equivalence required? |
|---|---|---|---|
| Default | release authority's key | fast (deserialize + sig check) | no — pre-built against whatever kernel built the corelib, plus the signature |
| Paranoid | none | slow (re-derive all theorems) | yes — local kernel must be able to produce the same Thms |

The default mode is the more federation-friendly: a peer ships their
corelib, signs it, you choose whether to trust their key. Different
distributions of Covalence might ship different corelibs; users opt
in.

The paranoid mode is the more cautious-developer-friendly: I changed
the kernel; I want to know if my corelib still derives. Catch the
breakage at startup instead of at first downstream use.

---

## 8. Stdlib on top of corelib

A **stdlib library** is a traditional Rust library that ships its own
pre-proven (or paranoid-rederivable) theorems on top of corelib. Each
library:

- Lives in its own crate (`covalence-stdlib-regex`,
  `covalence-stdlib-parsers`, `covalence-stdlib-inductive`, …).
- Has its own content-addressed identity (a hash like `H_regex`).
- Ships its own `corelib-shaped` artifact (derivation script for
  paranoid + signed blob for default).
- The signature is by *some* release authority — typically the
  Covalence release signer for officially-shipped libraries; a
  community signer for community ones. The *library* is not an
  authority.
- Has its own `OnceCell` and lazy-init.
- Optionally projects under `/lib/stdlib/<library>/` for navigation.
- Depends on corelib + whichever other stdlib libraries it needs.

The user opts in by:

- Adding the crate as a Cargo dependency.
- Calling `<library>::ensure_loaded(kernel)` at startup, *or* using
  the library lazily.
- Optionally enabling `<library>-verify` for paranoid mode.

What goes here (the things the user listed as use cases that aren't
in corelib):

- **Regular expressions**: `Regex` type, matching semantics,
  closure-under-operations theorems. Standalone library; depends on
  corelib for `List`, `Option`.
- **Parser combinators**: monadic combinators, theorems about
  composition / inversion / left-recursion-avoidance. Standalone
  library; depends on corelib + regex.
- **Inductive datatype framework**: a *theorem-generator* that, given
  a well-formed datatype spec, produces constructors, destructor,
  induction principle, recursion principle. Depends on corelib.
  Probably the most consequential stdlib library because it
  generalizes to user-defined datatypes.
- **Numerical analysis**, **cryptographic theory**, **category
  theory** — all candidate stdlib libraries shipped independently.

**Why the split matters.** Corelib must stay small enough to audit
*and* small enough that paranoid mode boots in seconds. Stdlib
libraries can be arbitrarily large (regex theory alone could be
hundreds of theorems); the user pays for what they use.

---

## 9. Connection to federation

The corelib is a **pre-baked federation peer**. Its Thms enter your
kernel under the release authority's signature the same way another
kernel's Thms would. The only difference: corelib is local (shipped
with the binary) rather than remote (over the network).

Federation extensions:

- **Multiple corelibs.** Different distributions of Covalence might
  ship different corelibs (one with classical-HOL-style numerals,
  one with HoTT-flavored). Users opt in to whichever signature key
  they trust.
- **Stdlib libraries as federation peers.** A user can subscribe to a
  community-maintained stdlib library by trusting its publisher's
  key, the same way they'd subscribe to a remote kernel peer.
- **Versioning.** Corelib is a content-addressed artifact with a
  hash. Upgrading means a new hash + new signature.
- **Reproducibility.** Paranoid mode *is* the reproducibility check:
  same kernel rules + same derivation script ⇒ same Thms.

---

## 10. Connection to facts-not-proofs

Corelib is the canonical example of the
[facts-not-proofs](../../layered-framework/notes/facts-not-proofs.md)
discipline:

- The pre-proven artifact stores **facts** (`Thm` values), not
  justifications.
- The derivation script (for paranoid mode) is **optional** — it's
  the recorder mode mentioned in the facts-not-proofs note,
  retained for reproducibility but not for soundness.
- A consumer who trusts the release authority's key never runs the
  script; they just use the Thms.

This is also why corelib doesn't bloat the kernel: the kernel sees
only the Thms (facts); the script is build-time material.

---

## 11. Open questions

- **Where does corelib live?** Default plan: `covalence-corelib` as
  a new crate, with a Cargo feature `corelib-verify` for paranoid
  mode. Alternative: inline into `covalence-shell`. Recommend:
  separate crate so the build artifacts are easy to inspect and so
  `covalence-shell` doesn't bloat.
- **What's the derivation script format?** Options: (a) a binary
  log of `(rule_name, premise_ids, result_id)` triples (compact;
  needs a deserializer); (b) a Rust function in the crate that
  invokes `Prover` methods (no extra format; harder to verify
  cross-version); (c) an S-expression script (parseable; verbose).
  Lean to (a) — it's the recorder format from facts-not-proofs.
- **What's the signed-blob format?** Default plan: a Table
  ([`covalence-object`](../../../../../crates/covalence-object/src/table.rs))
  of `(name, serialized_thm)` rows, with an Ed25519 signature over
  the Table's hash. Reuses existing machinery.
- **Corelib evolution under kernel rewrite.** When the kernel is
  rewritten (per
  [shared-backbone Phase 2](../00-overview.md#5-the-four-phases)),
  the existing corelib's derivation script may no longer apply.
  Plan: each kernel version has its own corelib. The build process
  re-derives corelib against the new kernel; the new signed blob
  ships with the new release.
- **Corelib content-addressing identity.** Should corelib's
  identity be the hash of its derivation script, or the hash of
  its pre-built blob? Both should be derivable from build artifact
  metadata.
- **Per-theory paranoid mode.** Could a user enable paranoid for
  *some* corelib theories but not others? Probably yes — the
  script is structured as one block per theory; verify on opt-in.
  Probably not worth doing in V1.
- **What's in V0?** Minimum corelib for OpenTheory + Alethe
  workloads: naturals, integers, lists, booleans, ordering,
  induction. Regex/parsers/inductive-datatype framework all wait
  for first stdlib libraries.
- **Stdlib library discovery.** How does a user find what stdlib
  libraries exist? V1: a list in the project README. V2: a
  registry (akin to `crates.io` but for proven libraries),
  possibly federated.

---

## 12. Cross-references

- [`kernel-as-os.md`](./kernel-as-os.md) — corelib mounts as a
  directory under `/lib/corelib/` in the Kernel's filesystem;
  stdlib libraries mount under `/lib/stdlib/<library>/`.
- [`../00-overview.md`](../00-overview.md) — the path doc; corelib
  work fits Phase 2 (parallel prover + VCS streams).
- [`../../layered-framework/notes/facts-not-proofs.md`](../../layered-framework/notes/facts-not-proofs.md)
  — the LCF discipline corelib's two modes both respect.
- [`../../layered-framework/notes/modified-hol.md`
  §3.3](../../layered-framework/notes/modified-hol.md#33-top-theories-morphisms-interpretations)
  — corelib theories live in the top layer (theories + morphisms
  + interpretations).
- [`../../../../VISION.md`](../../../../VISION.md) §3 — computational
  metatheory; corelib is the symbolic-metatheory parallel
  (pre-proven theorems for re-use, with the kernel re-verifying or
  trusting-the-build).
- [`../../../../../ARCHITECTURE.md` §10.2](../../../../../ARCHITECTURE.md)
  — mount-as-implication; loading corelib is mounting its
  authority's namespace.
- [`../../../../../crates/covalence-shell/src/prover.rs`](../../../../../crates/covalence-shell/src/prover.rs)
  — the `Prover` trait the corelib API extends.
- HOL Light's standard library, Rust's `core` vs `std`, Lean's
  `Init` vs `Mathlib` — design templates. Covalence's twist is the
  dual paranoid/default build mode + the explicit corelib/stdlib
  split.
