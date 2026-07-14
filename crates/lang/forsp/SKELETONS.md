# covalence-forsp — SKELETONS

## Severe

- **The small-step relation is an *untrusted* witness, not a kernel proof.**
  `semantics.rs` (`ForspSemantics`) implements `Semantics<ForspRepr>` with a
  `StepCert` (`ForspStep`) and composite `Thm` (`StepTrace`) that are just
  **before/after machine snapshots** — Forsp has no kernel theory yet, so no
  `⊢ state → state'` is produced. The trait wiring is deliberately arranged so a
  kernel-backed forsp theory drops in as a `Semantics` *swap* (its `StepCert`
  would carry a real reduction theorem, its `Thm` the composite), leaving the
  driver (`RunToValue`) and `forsp_reduce` untouched. Needs: an object-language
  encoding of the Forsp machine (stack/env/continuation) as kernel terms and a
  `Reduces` relation over them.

## Minor

- **`/forsp` web-export wiring is unbuilt.** `forsp_reduce` returns a
  `ForspReduction` (the `StepTrace` of machine snapshots + final stack + status)
  ready for the endpoint to render as reduction steps, but the actual
  `/forsp` HTTP/JSON handler that serializes the trace is not wired here.
- **Snapshots share a monotonically-growing heap.** A `Snapshot` clones only the
  `stack`/`env`/continuation `ValRef`s; the heap they index lives in the
  `ForspSemantics`' `RefCell<Forsp>` and only grows. Fine for finite reductions;
  a long-running / diverging program never reclaims heap cells (no GC).
