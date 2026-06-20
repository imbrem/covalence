;; nat.thy — the `Nat` THEORY as declared data (surface-compiler §3.0): the
;; signature `Nat` plus the four Peano-addition axioms, stated ABSTRACTLY over
;; the signature's vocabulary (`zero`/`succ`/`add`, sort `A`). The binders are
;; untyped — each `a`/`b`'s type is inferred from the ops (all `A`), so the SAME
;; axiom text instantiates at any carrier when a model re-elaborates it.
(#thy NatTheory
  (over Nat)
  (axiom zero.add (forall (a) (= (add zero a) a)))
  (axiom add.zero (forall (a) (= (add a zero) a)))
  (axiom succ.add (forall (a) (forall (b) (= (add (succ a) b) (succ (add a b))))))
  (axiom add.succ (forall (a) (forall (b) (= (add a (succ b)) (succ (add a b)))))))
