;; nat_add.sig — the `NatAdd` SIGNATURE as declared data (surface-compiler §3.0).
;; The *add fragment* of Nat: one sort `A` (the carrier α) and three unapplied
;; operations. This is the SMALL signature the cross-model `add.comm` demo runs
;; over — distinct from the canonical, full `init/nat.sig` (the whole nat theory),
;; because `nat/unary` (carrier `list unit`) is a genuine second model of THIS
;; fragment only. A `.sig` file IS a `(#sig …)` body; this is the single-sorted,
;; first-order shape the `Signature` type consumes (multi-sort / HOL-ω families
;; are deferred).
(#sig NatAdd
  (sort A)
  (op zero A)
  (op succ (-> A A))
  (op add  (-> A A A)))
