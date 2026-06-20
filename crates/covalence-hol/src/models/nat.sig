;; nat.sig — the `Nat` SIGNATURE as declared data (surface-compiler §3.0).
;; One sort `A` (the carrier α) and the three unapplied operations. A `.sig`
;; file IS a `(#sig …)` body; this is the single-sorted, first-order shape the
;; `Signature` type consumes (multi-sort / HOL-ω families are deferred).
(#sig Nat
  (sort A)
  (op zero A)
  (op succ (-> A A))
  (op add  (-> A A A)))
