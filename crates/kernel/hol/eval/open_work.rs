//! Source-local open work for this module/crate.
//!
//! Migrated from the former Markdown registry. Move markers beside the relevant
//! implementation as the area is touched; `bun run todos` provides the index.

// TODO(cov:kernel.hol.eval.nat-int-definitional-derivations-are-evalthm-typed, major): nat/int definitional derivations are EvalThm-typed: the chains use
// TODO(cov:kernel.hol.eval.bytes-definitional-evaluation-missing, major): bytes definitional evaluation missing: blocked on the Blob ↔ list u8
// TODO(cov:kernel.hol.eval.fixed-width-definitional-evaluation-stops-at-tonat-fromnat, major): fixed-width definitional evaluation stops at toNat/fromNat
// TODO(cov:kernel.hol.eval.sn-shr-arithmetic-right-shift-defs-intops-rs, major): sN.shr (arithmetic right shift), defs/intops.rs: needs floor-division
// TODO(cov:kernel.hol.eval.nat-ops-defs-nat-rs, major): nat ops, defs/nat.rs: natBitAnd/Or/Xor, natToBytesLe/Be,
// TODO(cov:kernel.hol.eval.bytes-ops-defs-blob-rs, major): bytes ops, defs/blob.rs: bytesConsNat, bytesAt declaration-only
// TODO(cov:kernel.hol.eval.other-binaries, major): Other binaries: (sub/div/min/max/copysign): reuse
// TODO(cov:kernel.hol.eval.unaries, major): Unaries: (sqrt/abs/neg/ceil/floor/trunc/nearest): need a new
// TODO(cov:kernel.hol.eval.comparisons, major): Comparisons: (eq/ne/lt/gt/le/ge): eq sort is bool, the result
// TODO(cov:kernel.hol.eval.conversions, major): Conversions: (promote/demote/truncSat/convert): mixed operand/result
// TODO(cov:kernel.hol.eval.init-script-infer-rs, major): init script/infer.rs: 4 code sites (:283/:427 blob, :298 nat
// TODO(cov:kernel.hol.eval.init-sexp-rs, major): init sexp.rs: 2 sites (:290 blob / :301 smallint deserialization
// TODO(cov:kernel.hol.eval.downstream-out-of-this-stage-s-scope, major): downstream (out of this stage's scope): kernel/hol/traits
// TODO(cov:kernel.hol.eval.provetrue-is-single-step-only, minor): provetrue is single-step only: It reduces one redex and bridges = T;
// TODO(cov:kernel.hol.eval.connective-rule-perf-logic-out, minor): Connective-rule perf (logic-out): and/or/imp/not/all/lem are now multi-step
