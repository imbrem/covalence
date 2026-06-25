;; nat_add.thy — the `NatAdd` THEORY as declared data (surface-compiler §3.0):
;; the signature `NatAdd` plus the four Peano-addition SPECS, stated ABSTRACTLY
;; over the signature's vocabulary (`zero`/`succ`/`add`, sort `A`). A `(#spec …)`
;; is a proof OBLIGATION — a goal every model must discharge — NOT a postulate.
;; The binders are untyped — each `a`/`b`'s type is inferred from the ops
;; (all `A`), so the SAME spec text instantiates at any carrier when a model
;; re-elaborates it. This is the add-fragment theory the cross-model `add.comm`
;; demo runs over (carriers kernel `nat` and `list unit`); the canonical, full
;; nat theory is `init/nat.thy`.
(#thy NatAddTheory
  (over NatAdd)
  (#spec zero.add (forall (a) (= (add zero a) a)))
  (#spec add.zero (forall (a) (= (add a zero) a)))
  (#spec succ.add (forall (a) (forall (b) (= (add (succ a) b) (succ (add a b))))))
  (#spec add.succ (forall (a) (forall (b) (= (add a (succ b)) (succ (add a b)))))))
