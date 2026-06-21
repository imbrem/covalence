# Covalence in the browser — kernel, IDE, and articles

**Status: in progress.** This is the working design for running the Covalence
kernel *in the browser* and for the `category.wiki` north star: a full prover
that loads **articles** — `.cov` files that are first-class documents, rendering
to HTML (equations to MathML) with a purpose-built Typst-like markup and
pluggable widgets (graphs, string diagrams, commutative diagrams).

This doc is the counterpart to [`VISION.md`](./VISION.md) (kernel) and
[`frontend.md`](./frontend.md) (UX): it is specifically about the **deployment
seam** — how the proof world reaches a browser, and how the browser prover and a
browser IDE share one core.

## North star

A static web app at `category.wiki` where:

- the **kernel runs client-side** (no server round-trip to check a proof);
- a page *is* a `.cov` article — prose + definitions + theorems — that
  **renders to HTML/MathML** and whose theorems are **checked in the browser**;
- the article's **own** content is always kernel-checked; its **dependencies**
  (other articles it `#import`s) are **trusted by default** — admitted by their
  exported statements without replaying their proofs — but this is **visibly
  flagged and configurable** down to full re-checking.

## Layering

The deployment seam adds exactly one new layer (`service`) and otherwise reuses
the existing stack:

```
covalence-core        the TCB — sync, wasm-clean (LazyLock only)
   └─ covalence-hol    HOL builder + `.cov` script checker (run / run_async)
        └─ covalence-kernel
             ├─ store/backend   content-addressed blobs (wasm-portable)
             └─ service   ← NEW: KernelService — the ONE check/inspect surface
                  ├─ covalence-web-kernel   wasm-bindgen shim   (browser)
                  ├─ covalence-lsp          LSP server          (native)
                  └─ covalence-serve        HTTP/WebSocket API  (native)
```

`covalence-kernel::service` is the single, target-agnostic place where
"check a `.cov` source → theorems + diagnostics" lives, so the three front-ends
never re-implement proof checking. It is implemented today
(`crates/covalence-kernel/src/service.rs`):

```rust
pub struct KernelService { pub trust: TrustPolicy }
pub struct CheckReport   { pub ok: bool, pub theorems: Vec<TheoremInfo>, pub diagnostics: Vec<Diagnostic> }
pub struct TheoremInfo   { pub name: String, pub statement: String }
pub struct Diagnostic    { pub severity: Severity, pub message: String, pub span: Option<Span> }

impl KernelService { pub fn check(&self, src: &str) -> CheckReport; }
```

`check` is synchronous and **builds for `wasm32-unknown-unknown`** today; the
whole stack (`core → hol → store → kernel`) compiles to that target with no
changes beyond the `covalence-hol` tokio/getrandom portability fix.

## Target decision: one wasm target, native LSP

There were two candidate browser targets, and we **collapse to one**:

| | Browser prover / IDE | (rejected) Browser-VSCode LSP |
|---|---|---|
| Target | `wasm32-unknown-unknown` + `wasm-bindgen` | `wasm32-wasip1-threads` (WASI) |
| Editor | our own (CodeMirror/Monaco) talks to the kernel **directly** | `lsp-server` over WASI stdio via `@vscode/wasm-wasi-lsp` |
| `lsp-server` on wasm | not needed | required (needs `std::thread`) |

**Decision:** ship the browser prover/IDE as a `wasm-bindgen` app whose editor
calls `KernelService` directly (diagnostics / hover / completion as plain async
calls — no LSP wire protocol). The **LSP only ever compiles native** (desktop
VSCode, local `cov lsp`) with full tokio. We therefore **do not build the
`wasm32-wasip1-threads` VSCode-web LSP**.

Consequences:
- one wasm target, one ABI, far less surface to keep portable;
- the "IDE on the web" goal is met by our own app, not by `vscode.dev`;
- we *give up* Covalence support **inside vscode.dev specifically** — recoverable
  later by reviving the WASI/LSP build, kept here as a documented option, not a
  target.

Today's `covalence-lsp` is only a **syntax** server (`covalence_sexp::parse`); it
does not call the prover at all. Real proof diagnostics land by having the native
LSP wrap `KernelService` — the same surface the browser uses.

## Trust model (article vs. dependencies)

`category.wiki` mixes "I proved this here" with "this builds on published work."
The policy (`TrustPolicy` / `TrustLevel`):

- the article's **own** `#thm`s are **always** re-derived by the kernel —
  nothing in the text is trusted;
- a **dependency** (`#import`ed article) defaults to `TrustStatements`: its
  exported theorem **statements** are admitted without replaying its proofs,
  rendered with a **"trusted dependency" badge**;
- `DeepCheck` re-checks a dependency from source (nothing trusted).

This reconciles "trust deps by default, noted & configurable" with the standing
principle that imports are never *silently* trusted (cf. the `feedback-no-trust`
guidance): trust is explicit, surfaced, and reversible. *(Enforcement of the two
levels — and of statement-only admission — is pending; see `SKELETONS.md`.)*

## Async dependency loading

The decisive constraint for the browser: **loading a dependency article over the
network is inherently async.** A blocking executor on the browser main thread
(`futures::executor::block_on`) **cannot** drive a JS-backed future — a `fetch`
only resolves when control returns to the JS event loop, which a blocking
executor never yields to. So self-contained articles check synchronously today,
but network `#import`s need a genuinely async path.

The script layer is already shaped for this: `run_async` takes a resolver
returning `Import` **futures**, so an `#import` of an unresolved dependency can
`await` a fetch. `KernelService` exposes the `ArticleSource` async trait as the
seam the browser fills with a `fetch`-backed loader.

**Decision: futures + `wasm-bindgen-futures` as the baseline; JSPI as a deferred
Chromium-only fast-path.** (Rationale in [`wasm3-rust.md`](./wasm3-rust.md).)

The two candidates were:
1. **Futures + `wasm-bindgen-futures`** — expose `check` as a JS `Promise`, drive
   `run_async` on the browser event loop, resolver = async JS `fetch`. Portable
   to every browser.
2. **JS Promise Integration (JSPI, WASM 3.0-era)** — let a synchronous-looking
   wasm call suspend while an imported async JS function runs, then resume —
   async I/O *without* a futures rewrite.

We pick **(1)** because:
- `category.wiki` is open-web and must run in **Safari**, where **JSPI is not
  available** (Chromium-only default; Firefox flagged; Safari uncommitted) and
  has **no stable wasm-bindgen support**;
- our engine is **already async** — `run_async` takes a resolver returning
  `Import` *futures* — so the cost that makes JSPI attractive (re-coloring a
  synchronous call graph) is **mostly pre-paid** for us. We just drive the
  existing async core from `wasm-bindgen-futures` and back the resolver with a
  JS `fetch`.

**JSPI stays a deferred optimization**: feature-detected
(`'Suspending' in WebAssembly`) for contexts we control (Electron / a
Chromium-based VSCode-web), where it would let the *native-shaped synchronous*
path run in-browser unchanged. **Asyncify is rejected** (code-size/perf tax).

Note also (from the research): **Rust cannot target WasmGC**, and the kernel
needs none of memory64 / multi-memory / EH / tail-calls — so the WASM 3.0
headline features don't touch the browser kernel. The features we rely on
(`reference-types`, `bulk-memory`, …) are already default-on; parallel
verification, if ever wanted, is the mature `wasm32-wasip1-threads` + atomics
path.

## Articles: `.cov` as a first-class document

An article *is* a `.cov` file (not Markdown with proofs embedded). The render
pipeline is mostly greenfield, but the substrate exists:

- **Notation printer (new, on the critical path).** Today a checked theorem can
  only be rendered as a canonical S-expression (`(eq (app f x) y)`); a
  `Term` → readable-math printer (→ MathML) does not exist yet. This is the
  shared dependency between "inspect a theorem" and "render an article."
- **Markup (new).** A purpose-built, Typst-like prose markup with a raw-HTML
  fallback, parsed with `winnow` (via `covalence-parse`), embedding `$…$`
  equations and `#widget` directives.
- **Widgets (substrate exists).** `covalence-graph` already has a pure-Rust
  `render_svg` + `StringDiagram` — the backend for string/commutative-diagram
  widgets. Graphs/figures plug in the same way.

Pipeline: `markup → (prose→HTML, equations→MathML, theorem-refs→notation-printed
statements, #widget→SVG) → HTML`.

## Kernel federation via PKI (future, aspirational)

Now that the kernel runs in the browser, a natural next capability: let a
client kernel **federate** with a server (or peer) kernel, trading
**cryptographically-signed theorems** instead of re-deriving everything or
trusting a server blindly. A theorem checked by a kernel you trust (by its
public key) can be admitted without replaying its proof — the trust is
explicit, signed, and surfaced.

This is **not** in the TCB: federation is an **observer/facts** layer over the
kernel. The core still only believes what it checks; a *fact* admitted on a
trusted signature is exactly the same "trusted, not re-checked" move the article
[trust model](#trust-model-article-vs-dependencies) already makes — generalized
from "the standard library" to "any peer whose key I trust."

### Light vs. full mode (the optional ~2 MB download)

The web kernel artifact is largeish (~2 MB wasm). Loading it should be
**opt-in**, so the REPL/IDE has two modes:

- **Light mode (today's behaviour).** Thin client: the browser sends
  S-expressions to `cov serve` over the WebSocket REPL; the **server** checks
  everything; the client trusts the server. No kernel download.
- **Full mode.** The REPL **asynchronously downloads** the wasm kernel, runs it
  locally (its own `KernelService` + an in-memory store), and **federates** with
  the server: it checks locally where it can, and exchanges signed facts with
  the server for everything else. The 2 MB cost is paid only when the user opts
  in (or lazily, on first local check).

Both modes are just different `backend`s behind the REPL's existing
`SyncBackend`/`AsyncBackend` abstraction — light = a remote backend, full = a
local kernel backend optionally *composed over* the remote one (the same
layered-backing pattern the store already supports).

### What a federated "fact" is

Each kernel has an **identity**: an ed25519 keypair (`covalence-sig` already
wraps this). A **fact** is a content-addressed theorem plus provenance:

```
Attestation {
  theory: O256,        // content hash of the theory / environment context
  concl:  O256,        // content hash of the conclusion term
  checker: PubKey,     // the kernel that derived it
  sig:    Signature,   // ed25519 over (theory, concl)
}
```

Both `theory` and `concl` are already content-addressed (`O256`), so an
attestation is a tiny, self-describing certificate. The underlying theory and
(optionally) the proof are ordinary content-addressed blobs, fetched through the
existing store / `BlobSource` composition or the async `ArticleSource` seam —
federation reuses the *same* transport as network article loading.

### The trust decision

`TrustPolicy`/`TrustLevel` generalize cleanly:

- **`DeepCheck`** — re-derive from the proof blob; trust no signature.
- **`TrustStatements`** (today's default for std-lib) — admit the statement;
  with federation this becomes *"admit if accompanied by an attestation from a
  key in my trust set."*
- a **trust set** is a set of public keys (flat web-of-trust now; a CA /
  delegation chain later). Anything admitted on a signature is rendered with the
  attesting key — never *silently* trusted (consistent with the standing
  "no silent trust of imports" principle).

### Why we're already compatible

| Need | Already have |
|---|---|
| PKI primitive | `covalence-sig` (ed25519, EdDSA) |
| Stable theorem references | `O256` content addressing of terms/theories |
| Home for signed facts | the `covalence-kernel::facts` observer module (skeleton) |
| The trust knob | `service::TrustPolicy` / `TrustLevel` |
| Fact/blob transport | store `BlobSource` composition + async `ArticleSource` |
| Optional lazy kernel | the web kernel is a separable wasm artifact, already dynamic-imported |
| Pluggable client backend | REPL's `SyncBackend`/`AsyncBackend` trait objects |

### What's new to build (when we get there)

- An `Attestation` type + sign/verify in `covalence-kernel::facts` (over
  `covalence-sig`), and a fact store keyed by `(theory, concl)`.
- A federation protocol step (exchange attestations + content-addressed blobs)
  layered on the existing REPL/serve transport.
- Trust-set management (which keys; revocation; later a delegation chain).
- A REPL/IDE "light ↔ full" toggle that lazily fetches the wasm kernel and
  swaps the backend.

Marked aspirational; no code yet. Builds on [`observers.md`](./observers.md)
(the observer substrate) and the `browser-kernel` federation note in
[`VISION.md`](./VISION.md).

## Roadmap

1. **Portability** — `covalence-hol` builds for `wasm32-unknown-unknown`. ✅
2. **Shared service** — `covalence-kernel::service::KernelService` (sync `check`
   → theorems + diagnostics; `ArticleSource`/`TrustPolicy` seams). ✅
3. **`covalence-web-kernel`** — wasm-bindgen cdylib over `KernelService`; a
   minimal `covalence-web` route that loads a `.cov`, checks it, lists theorems.
   *(End-to-end "prover in the browser", WASM execution stubbed.)*
4. **Async dependency loading** — wire `ArticleSource` through `run_async`
   (mechanism per the WASM3/JSPI research); enforce `TrustPolicy`.
5. **Notation printer** — `Term` → math (→ MathML).
6. **Article renderer** — markup parser + HTML/MathML emitter + graph widgets.
7. **Native LSP over `KernelService`** — real proof diagnostics in desktop VSCode.
8. **Light/full REPL modes** — opt-in lazy download of the ~2 MB wasm kernel; a
   local kernel backend behind the existing `SyncBackend`/`AsyncBackend`
   abstraction (light = remote, full = local optionally composed over remote).
9. **Kernel federation via PKI** — signed `Attestation`s in
   `covalence-kernel::facts` (ed25519 via `covalence-sig`); `TrustLevel` extended
   to "admit if signed by a key in my trust set"; a federation exchange over the
   existing REPL/serve transport. See *Kernel federation via PKI* above.
