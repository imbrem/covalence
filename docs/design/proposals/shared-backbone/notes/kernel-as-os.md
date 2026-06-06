# Kernel as OS: UNIX + Plan 9 philosophy

> **STATUS: WORKING NOTE — extracted from session conversation.**
> Captures the design ethos for `covalence-shell::Kernel`: it's not a
> theorem-prover kernel, not a blob backend — it's the **operating
> system kernel of the prover/VCS process**, in the Linux-with-Plan-9
> sense. UNIX philosophy throughout; everything is a file.
> Companion to the [shared-backbone proposal](../00-overview.md) and
> the [modified-HOL note](../../layered-framework/notes/modified-hol.md);
> realizes [`ARCHITECTURE.md` §10](../../../../../ARCHITECTURE.md)
> (namespaces, mount, FS projection) at the implementation level.

The user's framing, verbatim:

> *Kernel should be a bit like the Linux kernel here: keeping up a
> table of file descriptors + facts about them. Hence the fusion of
> VCS and prover — they both use the same Kernel as the backend.*

> *This whole system should very much be based on the UNIX philosophy
> — and in particular, everything is a file! Even Plan 9, really!*

---

## Contents

1. [The framing](#1-the-framing)
2. [The auth/value split](#2-the-authvalue-split-filesystem-for-authorities-hashes-for-values)
3. [Everything is a file — what that means for authorities](#3-everything-is-a-file--what-that-means-for-authorities)
4. [The Kernel's three tables](#4-the-kernels-three-tables)
5. [VCS + prover fusion at the operational level](#5-vcs--prover-fusion-at-the-operational-level)
6. [FUSE is the externalization](#6-fuse-is-the-externalization)
7. [Federation is mount](#7-federation-is-mount)
8. [What this implies for the API](#8-what-this-implies-for-the-api)
9. [Open questions](#9-open-questions)
10. [Cross-references](#10-cross-references)

---

## 1. The framing

`covalence-shell::Kernel` is the **system kernel of the prover/VCS
process** — analogous to the Linux kernel managing a Unix
process's resources, or (more aspirationally) the Plan 9 kernel where
the everything-is-a-file principle is taken to its logical extreme.

Three things follow:

1. **The Kernel owns the resources.** Blobs, trees, theorems,
   observations, oracle programs, mount points — all are *resources*
   the Kernel tracks via a handle table (file descriptors).
2. **Operations are filesystem-shaped.** Open, read, write, list,
   mount, chmod-equivalent. The API surface looks more like
   POSIX/9P than like an SDK.
3. **VCS and prover are co-equal consumers.** They both call into
   the Kernel; they both manipulate the same files; the "fusion"
   from the [vision](../../../../VISION.md) is realized
   operationally as "same Kernel, same filesystem."

This is **the implementation realization** of
[`ARCHITECTURE.md` §10](../../../../../ARCHITECTURE.md) (namespaces as
prefix-indexed relations; mount = attach-under-prefix; FS projection
of the relational store). §10 gives the formal semantics; this note
gives the operational design ethos that lets §10 land in code.

---

## 2. The auth/value split: filesystem for authorities, hashes for values

> **Important refinement.** The "everything is a file" / Plan-9
> framing applies to **authorities** (writers of observations) and
> their state — mutable, namespace-shaped, mount-able. **Values**
> (proved theorems, blobs, libraries, oracle programs, signed
> artifacts) are **content-addressed** by hash, not by path. Trees
> *can* be overlaid on a content-addressed value for navigation
> (e.g., the corelib has a path-shaped name table), but the
> internal primitive is the hash.

| Kind | Storage primitive | Filesystem role |
|---|---|---|
| Authority (BLAKE3 oracle, Ed25519 verifier, user, release signer, peer kernel) | Mutable namespace under `/auth/...` | Path-addressed; mountable; observations recorded as files |
| Observation (`O.R(args)` written by authority `O`) | Entry in fact table, indexed by authority | Path-addressed under owning authority |
| Resource handle (open blob, open tree) | Entry in resource table | FD-like; not path-addressed |
| Mount point | Namespace overlay | Path-addressed |
| **Blob** (bytes) | **Hash** | Optional overlay path |
| **Tree** (Git-like) | **Hash** | Optional overlay path |
| **Theorem (`Thm`)** | **Hash** of its serialized form | Optional overlay path |
| **Library** (corelib, stdlib library, user library) | **Hash** of (arena + UF + name-table) blob | Optional overlay (e.g., `/lib/corelib/`) |
| **Oracle program** | **Hash** of bytecode | Optional overlay |
| **Signed artifact** | **Hash** of (payload + signature) | Optional overlay |

The two substrates have **different primitives but can be
bridged**:

- The filesystem is what *changes* (authorities recording
  observations as the system runs); the content-addressed store is
  what *stays the same* (every hash points to exactly one immutable
  value forever).
- Federation, mount, and authority bookkeeping are filesystem
  operations. Distributing a library, signing a Thm, citing a blob
  are content-addressed operations.

Two interaction patterns:

1. **Mounting a CA tree as a filesystem directory.** A
   content-addressed tree (Git-like, or any nested value with
   natural directory shape) **can be mounted at a filesystem path**
   for navigation. The mount is *optional* — the value exists
   regardless of whether it's projected into the filesystem — but
   it's the natural Plan-9-shaped move when a user wants to browse.
   `cog mount tree://<H_corelib> /lib/corelib/` is the spelling.
   The mount is a read-only overlay; modifying it isn't possible
   because the CA value is immutable.
2. **Authorities writing observations *referencing* CA hashes.**
   E.g., `release_signer.signed(H_corelib, sig)` is a filesystem
   entry under `/auth/release_signer/signed/` whose contents
   reference the CA hash `H_corelib`. The observation is mutable
   (the authority might revoke and re-sign); the value it points to
   is immutable. Loading the corelib (a CA value) under the
   release authority's signature (a filesystem-recorded observation)
   is the canonical pattern.

The asymmetry is one-way: CA values can be *projected into* the
filesystem; filesystem state cannot become a CA value without first
being serialized and hashed (which produces a new CA value of the
filesystem snapshot — a Thm or a blob or a tree).

---

## 3. Everything is a file — what that means for authorities

Plan 9 generalized UNIX's "everything is a file" to its logical
conclusion: even the window system, RPC interfaces, per-process state
were exposed as files. Covalence takes the same move:

| Thing | What it looks like in the Kernel's filesystem |
|---|---|
| Content-addressed blob | A file. Path is the address (e.g., `/blobs/blake3/<hash>`). |
| Content-addressed tree | A directory. Children are named files / subdirectories. |
| Theorem (`Thm`) | A file. Contents are the Thm's serialized form. Path includes its identity. |
| Observation | A file (or a directory entry under the relevant authority). |
| Oracle program (WASM blob + soundness proof) | A directory containing the bytecode file + the proof file. |
| Mount point | A directory. Looking it up dispatches to whatever backend is mounted. |
| Authority | A namespace owner. Owns a directory; observations under it are files. |
| Resource handle | A file descriptor. Lightweight, transferable, closable. |
| Fact ("X happened at time T under authority A") | A file in the relevant authority's namespace. |
| Per-session state | A file in `/proc/self/` style. |

The point isn't that we literally implement a filesystem (although
[FUSE (§5)](#5-fuse-is-the-externalization) means we can). The point
is that **the conceptual model is path-based**: every operation has a
path; every resource lives at a path; relations between resources are
filesystem relations (containment, links, mounts).

---

## 4. The Kernel's three tables

Adapting the Linux-kernel analogy: a Linux kernel has process table,
file descriptor table, mount table. Covalence's `Kernel` has:

1. **Resource table** — open handles to blobs, trees, theorems, etc.
   `(Handle → underlying content reference)`. Lightweight; passed
   around freely; closed when done. Linux: `struct file *`.
2. **Fact table** — uninterpreted observations.
   `(authority, relation, args) → recorded fact`. The Kernel's
   "kernel log": when an oracle returns a hash, when a tree is
   committed, when a signature verifies, the fact lands here.
   No HOL-kernel-level interpretation until userspace asks.
3. **Authority registry** — who can write what.
   `(name → (owned_relations, kind))`. `kind` is one of: local
   gensym, public-keyed (for federation), framework-builtin.
   Equivalent to capabilities + ownership in a multi-user kernel.

The HOL kernel underneath (`covalence-kernel`) operates on the
*logical* objects (terms, types, proofs). The shell Kernel operates
on the *operational* objects (handles, facts, authorities). The
prover/VCS APIs are how userspace bridges between them.

---

## 5. VCS + prover fusion at the operational level

The vision says "VCS and prover developed in parallel, eventually
unified." Operationally, the unification is **same Kernel**:

- `cog commit` records a tree, mints a `TreeStore.is_tree(hash)`
  fact under the TreeStore authority. Returns a resource handle.
- The prover wants to reason about that tree. It opens the same
  handle (or reads the same fact from the fact table) and proceeds.
  No translation, no separate data model.
- `cog mount path` adds a mount point in the Kernel's namespace.
  The prover sees the mounted content under the same path; queries
  return facts from both local and mounted sources.
- A prover's `Thm` is itself stored as a file (when serialized) and
  can be the target of `cog commit`. Theorems flow through the same
  pipeline as any other artifact.

This is why the rename I suggested earlier (`Kernel` → `BlobBackend`)
was *wrong*. It's not a blob backend; it's the OS. Its current state
is small; its eventual shape carries every resource the system knows
about.

---

## 6. FUSE is the externalization

[`covalence-fuse`](../../../../../crates/covalence-fuse) (commits
`b66c655`, `3f9207a`) is the literal projection of the Kernel's
filesystem into the host OS's filesystem. Anything the Kernel
exposes as paths → FUSE exposes as a mounted directory the user can
`ls`, `cat`, `cp`, etc.

This makes the design empirically Plan-9-shaped: you can interact
with the prover's internals from the shell. `ls /mnt/cov/thms/` lists
known theorems; `cat /mnt/cov/blobs/<hash>` reads a blob;
`echo foo > /mnt/cov/facts/user/declare/x` records a user-asserted
fact (with all the trust-set consequences that implies).

This is also the path to a **9P-style federation protocol**: expose
the Kernel's filesystem over a socket; remote kernels mount it; facts
flow across; signed Thms ride the file-write boundary.

---

## 7. Federation is mount

In Plan 9, mounting a remote system's namespace into yours is the
default IPC mechanism. Covalence inherits this:

- One Kernel exposes its filesystem (via FUSE locally, or a
  9P-equivalent protocol remotely).
- Another Kernel mounts it: `cog mount remote://peer /n/peer/`.
- Now `/n/peer/blobs/<hash>` is accessible; `/n/peer/auth/blake3/`
  exposes the peer's BLAKE3 observations.
- Trust is per-mount-edge: facts from `/n/peer/` carry an implicit
  "peer asserted this" authority. Discharging via meaning-axiom is
  the user's call.

The
[`ARCHITECTURE.md` §10.2 mount-as-implication](../../../../../ARCHITECTURE.md)
story (`mount Q at P ≡ ∀x. Q(x) ⇒ P(x)`) is the *logical* shape; the
filesystem-mount is the *operational* shape; both are the same
operation viewed at different levels.

---

## 8. What this implies for the API

The Kernel API should:

- **Be path-based wherever possible.** `kernel.open(path)`,
  `kernel.read(path)`, `kernel.list(prefix)`, `kernel.mount(path,
  backend)`. Resource handles are the FD equivalent.
- **Expose observations as filesystem state.** Recording a fact and
  writing-a-file are the same operation. Querying facts and
  reading-a-directory are the same operation.
- **Support per-process namespaces (Plan-9-style).** Different
  consumers (one prover session, one VCS session) can see different
  views of the same Kernel by mounting differently. This is how
  cross-session isolation falls out for free.
- **Stay UNIX-small.** Each operation does one thing. Compose by
  layering, not by adding flags.
- **Be 9P-friendly downstream.** The federation protocol should
  ride a small file-protocol surface, not a bespoke RPC.

The concrete `Prover` and `HolLightKernel` traits we already have
(see the [format-graph note in `modified-hol.md`
§3.8](../../layered-framework/notes/modified-hol.md#38-format-graph-shell-traits-as-interfaces))
sit *on top of* this filesystem. They're userspace libraries that
make the Kernel's filesystem ergonomic for their format.

---

## 9. Open questions

- **Path scheme.** Default: hierarchical UNIX-style paths
  (`/auth/blake3/hashed/<input>/<output>`). Alternatives: flat
  content-addressed (`/<hash>`) with overlay metadata. The
  hierarchical view is more navigable; the flat view is more
  honest about what's really stored. Probably: both, with the
  hierarchical view as a virtual filesystem layered over the flat
  one.
- **Mount semantics for cyclic federations.** A mounts B; B mounts A.
  9P handles this; we'd inherit if we go 9P.
- **Per-session namespaces — V1 or later?** Plan 9's per-process
  namespaces are powerful but add complexity. V1 could have one
  global namespace per Kernel; per-session lands once it's clear
  which sessions need isolation.
- **What's the V1 list of fact-authorities?** Strawman:
  `BlobStore`, `TreeStore`, `Blake3`, `Sha256`, `Ed25519`, plus a
  catch-all `User` for hand-asserted observations. Each gets a
  directory.
- **How does the FUSE mount interact with concurrent writes?** The
  Kernel needs `&mut` for many operations; FUSE may multiplex
  requests. Likely answer: `Arc<Mutex<Kernel>>` at the FUSE boundary,
  with read paths fast and write paths serialized.
- **9P or HTTP/REST for federation?** 9P is the principled answer;
  HTTP is the pragmatic one. The existing `covalence-serve` (HTTP +
  WebSocket) is HTTP-shaped already; the federation pathway might
  stay HTTP-with-a-9P-like-shape rather than literal 9P.

---

## 10. Cross-references

- [`../00-overview.md`](../00-overview.md) — the path doc; the
  "Kernel as OS" framing makes the substrate-first phasing
  operational.
- [`../../layered-framework/notes/modified-hol.md`
  §3.8](../../layered-framework/notes/modified-hol.md#38-format-graph-shell-traits-as-interfaces)
  — the format graph; the HOL Light API and other format APIs sit
  *above* this filesystem.
- [`../../../../../ARCHITECTURE.md` §10](../../../../../ARCHITECTURE.md)
  — namespaces as prefix-indexed relations; mount = attach-under-prefix;
  FS projection. This note is the operational design ethos for
  realizing §10.
- [`../../../../../ARCHITECTURE.md` §11](../../../../../ARCHITECTURE.md)
  — storage: Git-like trees + Dolt-style prolly-tree tables. The
  filesystem the Kernel projects sits on top of this.
- [`../../../../VISION.md`](../../../../VISION.md) §5 — the
  architecture diagram. The bottom-outer layer is, operationally,
  this filesystem-kernel.
- [`covalence-fuse`](../../../../../crates/covalence-fuse) — the
  literal projection of the Kernel's filesystem into the host OS.
- [Plan 9 / 9P](https://en.wikipedia.org/wiki/Plan_9_from_Bell_Labs)
  — the inspiration.
