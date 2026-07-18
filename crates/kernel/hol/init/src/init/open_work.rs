//! Source-local open work for this module/crate.
//!
//! Migrated from the former Markdown registry. Move markers beside the relevant
//! implementation as the area is touched; `bun run todos` provides the index.

// TODO(cov:kernel.hol.init.src.init.polymorphic-let-style-specs-are-not-yet-twinned, major): Polymorphic let-style specs are not yet twinned: twins::unfoldspec
// TODO(cov:kernel.hol.init.src.init.def-style-selector-and-declaration-only-specs-get-no-body-twin, major): Def-style (ε-selector) and declaration-only specs get no body-twin
// TODO(cov:kernel.hol.init.src.init.typespec-re-home-is-prototype-only, major): TypeSpec re-home is prototype-only: twins::unittypedef() re-homes
// TODO(cov:kernel.hol.init.src.init.ball-add-containment-unproved, major): ball.add containment unproved: (init/ball.rs, F2c groundwork = data +
// TODO(cov:kernel.hol.init.src.init.rat-field-order-leaves, major): rat field/order leaves: (init/rat.rs, postulated via the axiom helper)
// TODO(cov:kernel.hol.init.src.init.real-dedekind-cut-suprema, major): real Dedekind-cut suprema: (init/real.rs, postulated via axiom, NOT
// TODO(cov:kernel.hol.init.src.init.rat-cov-operators-stay-constdef-op-givens-no-inline-def, major): rat.cov operators stay ConstDef::Op givens (no inline #def): Inlining
// TODO(cov:kernel.hol.init.src.init.real-cov-non-order-theorems, major): real.cov non-order theorems: ofratmono, zeroneone, iscut are
// TODO(cov:kernel.hol.init.src.init.stream-cov-wrapper-side-round-trips, major): stream.cov wrapper-side round-trips: headmk, tailconst, mkat
// TODO(cov:kernel.hol.init.src.init.binary-normal-form, major): Binary normal form: (init/natbinary.rs). double/bit0/bit1 +
// TODO(cov:kernel.hol.init.src.init.bitstring-iso, major): Bitstring iso: (init/natbitsiso.rs, stage NP3). bitsucc (increment,
// TODO(cov:kernel.hol.init.src.init.bytes-parsers-string-bytes-agreement, major): Bytes parsers + string/bytes agreement: (init/natparsebytes.rs +
// TODO(cov:kernel.hol.init.src.init.rationals-from-decimal-scientific-notation, major): Rationals from decimal + scientific notation: (stretch, not built). A
// TODO(cov:kernel.hol.init.src.init.float-parsing, major): Float parsing: (init/floatparse.rs, stage FP1). Built: parseFloat
// TODO(cov:kernel.hol.init.src.init.floatcert32-round-to-nearest-even-enclosure, major): FloatCert32 round-to-nearest-even enclosure: (numeral W13, not built)
// TODO(cov:kernel.hol.init.src.init.list-theory, major): List theory: (init/list.rs + listrecursion.rs + list.cov). Missing
// TODO(cov:kernel.hol.init.src.init.monoid-categorical-rewriters, major): Monoid / categorical rewriters: (init/monoid.rs + cat.rs). Not built
// TODO(cov:kernel.hol.init.src.init.formal-languages-kleene-algebra-theory, major): Formal-languages / Kleene-algebra theory: (init/lang.rs). Not yet proved
// TODO(cov:kernel.hol.init.src.init.regex-on-lists-matches, major): Regex on lists / Matches: (init/regex/). Deferred
// TODO(cov:kernel.hol.init.src.init.text-theory, major): Text theory: (init/char.rs, string.rs). Surface the list ops
// TODO(cov:kernel.hol.init.src.init.utf-8-utf-16-codecs, major): UTF-8 / UTF-16 codecs: (init/utf8.rs + utf8.cov, init/utf16.rs). Deferred
// TODO(cov:kernel.hol.init.src.init.reified-object-logic-s-expr-prop-logic, major): Reified object logic (S-expr → prop logic): (init/sexpr.rs + init/prop.rs,
// TODO(cov:kernel.hol.init.src.init.tree-sexp-theory, major): tree / sexp theory: (init/tree.rs, sexp.rs). Still deferred: branchinj
// TODO(cov:kernel.hol.init.src.init.inductive-types-api-backends, major): Inductive-types API backends: (init/inductive/{api,church,engine}.rs, over
// TODO(cov:kernel.hol.init.src.init.s-expression-parsing, major): S-expression parsing: (init/sexprparse.rs, stage SP1). A fuel-bounded
// TODO(cov:kernel.hol.init.src.init.json-parsing, major): JSON parsing: (init/jsonparse.rs, stage JP). A fuel-bounded reader
// TODO(cov:kernel.hol.init.src.init.lisp-acl2-layer, major): Lisp / ACL2 layer: (init/lisp.rs, over the carved carrier). Built: car/cdr/
// TODO(cov:kernel.hol.init.src.init.iter-deep-embedding, major): λiter deep embedding: (init/lambdaiter.rs + .cov, init/cvrecursion.rs)
// TODO(cov:kernel.hol.init.src.init.carrier-generic-model, major): Carrier-generic model: specs are stated over the self-model vocabulary (kernel
// TODO(cov:kernel.hol.init.src.init.haskell-like-surface-extraction, major): Haskell-like surface extraction: nat.sig/nat.thy are hand-written; they are the
