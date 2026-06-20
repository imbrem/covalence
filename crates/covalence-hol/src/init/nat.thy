;; nat.thy — the CANONICAL `nat` THEORY (surface-compiler §3.0): the full
;; specification of nat, as the list of proof OBLIGATIONS `(#spec …)` a model
;; must discharge. This is the INTERFACE; `init/nat.cov` is the PROOF that
;; kernel-nat (the structure carrying a `natrec`) SATISFIES it.
;;
;; Every exported `(#thm NAME … (#concl C) …)` of `nat.cov` appears here as a
;; `(#spec NAME C)` — same name, same conclusion. A `#spec` asserts NOTHING (it
;; is not a postulate); satisfaction is a separate proof. The
;; [`crate::init::nat_thy`] module checks, for EVERY spec here, that `nat.cov`
;; exports a theorem of the same name whose conclusion is α-equal to the spec —
;; i.e. `nat.cov ⊨ nat.thy`, the interface↔implementation correspondence.
;;
;; The specs are stated over the SELF-MODEL vocabulary (sort `nat` := kernel
;; `nat`; `add` := `nat.add`, `rec` := `natrec-op`, literal `0` := zero, …), so
;; re-elaborating each in the kernel env reproduces exactly the `nat.cov`
;; conclusion. A carrier-abstract presentation (over a `tfree` sort,
;; re-elaborated at any structure with a `natrec`) is deferred — see
;; `init/SKELETONS.md`.
(#thy nat
  (over nat)
  (#spec succ.ne_zero
    (forall (n nat) (not (= (succ n) 0))))
  (#spec succ.cong_ne
    (forall (m nat) (forall (n nat) (==> (not (= m n)) (not (= (succ m) (succ n)))))))
  (#spec rec.zero
    (forall (z nat) (forall (f (fun nat (fun nat nat))) (= (app (app (app (natrec-op nat) z) f) 0) z))))
  (#spec rec.succ
    (forall (z nat) (forall (f (fun nat (fun nat nat))) (forall (n nat) (= (app (app (app (natrec-op nat) z) f) (succ n)) (app (app f n) (app (app (app (natrec-op nat) z) f) n)))))))
  (#spec eq.refl
    (forall (n nat) (= n n)))
  (#spec add.zero
    (forall (a nat) (= (nat.add a 0) a)))
  (#spec add.succ
    (forall (a nat) (forall (b nat) (= (nat.add a (succ b)) (succ (nat.add a b))))))
  (#spec add.comm
    (forall (a nat) (forall (b nat) (= (nat.add a b) (nat.add b a)))))
  (#spec add.assoc
    (forall (a nat) (forall (b nat) (forall (c nat) (= (nat.add (nat.add a b) c) (nat.add a (nat.add b c)))))))
  (#spec add.cancel
    (forall (a nat) (forall (b nat) (forall (c nat) (==> (= (nat.add a c) (nat.add b c)) (= a b))))))
  (#spec add.swap_mid
    (forall (w nat) (forall (x nat) (forall (y nat) (forall (z nat) (= (nat.add (nat.add w x) (nat.add y z)) (nat.add (nat.add w y) (nat.add x z))))))))
  (#spec mul.zero
    (forall (a nat) (= (nat.mul a 0) 0)))
  (#spec mul.succ
    (forall (a nat) (forall (b nat) (= (nat.mul a (succ b)) (nat.add a (nat.mul a b))))))
  (#spec mul.comm
    (forall (a nat) (forall (b nat) (= (nat.mul a b) (nat.mul b a)))))
  (#spec mul.one
    (forall (a nat) (= (nat.mul a 1) a)))
  (#spec distrib
    (forall (a nat) (forall (b nat) (forall (c nat) (= (nat.mul a (nat.add b c)) (nat.add (nat.mul a b) (nat.mul a c)))))))
  (#spec distrib.r
    (forall (a nat) (forall (b nat) (forall (c nat) (= (nat.mul (nat.add a b) c) (nat.add (nat.mul a c) (nat.mul b c)))))))
  (#spec mul.assoc
    (forall (a nat) (forall (b nat) (forall (c nat) (= (nat.mul (nat.mul a b) c) (nat.mul a (nat.mul b c)))))))
  (#spec zero.sub
    (forall (m nat) (= (nat.sub 0 m) 0)))
  (#spec succ.sub
    (forall (n nat) (forall (m nat) (= (nat.sub (succ n) (succ m)) (nat.sub n m)))))
  (#spec le.succ_succ
    (forall (n nat) (forall (m nat) (= (nat.le (succ n) (succ m)) (nat.le n m)))))
  (#spec lt.succ_succ
    (forall (n nat) (forall (m nat) (= (nat.lt (succ n) (succ m)) (nat.lt n m)))))
  (#spec le.zero
    (forall (m nat) (nat.le 0 m)))
  (#spec zero.lt_succ
    (forall (m nat) (nat.lt 0 (succ m))))
  (#spec le.refl
    (forall (n nat) (nat.le n n)))
  (#spec not.succ_le_zero
    (forall (n nat) (not (nat.le (succ n) 0))))
  (#spec not.lt_zero
    (forall (n nat) (not (nat.lt n 0))))
  (#spec lt.irrefl
    (forall (n nat) (not (nat.lt n n))))
  (#spec le.succ_self
    (forall (n nat) (nat.le n (succ n))))
  (#spec le.total
    (forall (a nat) (forall (b nat) (or (nat.le a b) (nat.le b a)))))
  (#spec lt.iff_succ_le
    (forall (a nat) (forall (b nat) (= (nat.lt a b) (nat.le (succ a) b)))))
  (#spec le.add_r
    (forall (a nat) (forall (k nat) (nat.le a (nat.add a k)))))
  (#spec le.zero_iff
    (forall (b nat) (==> (nat.le b 0) (= b 0))))
  (#spec le.antisym
    (forall (a nat) (forall (b nat) (==> (nat.le a b) (==> (nat.le b a) (= a b))))))
  (#spec le.add_sub
    (forall (a nat) (forall (b nat) (==> (nat.le a b) (= (nat.add a (nat.sub b a)) b)))))
  (#spec le.trans
    (forall (a nat) (forall (b nat) (forall (c nat) (==> (nat.le a b) (==> (nat.le b c) (nat.le a c)))))))
  (#spec lt.imp_le
    (forall (a nat) (forall (b nat) (==> (nat.lt a b) (nat.le a b)))))
  (#spec lt.trans
    (forall (a nat) (forall (b nat) (forall (c nat) (==> (nat.lt a b) (==> (nat.lt b c) (nat.lt a c)))))))
  (#spec le.add_cancel_r
    (forall (a nat) (forall (b nat) (forall (c nat) (= (nat.le (nat.add a c) (nat.add b c)) (nat.le a b))))))
  (#spec lt.add_mono_r
    (forall (a nat) (forall (b nat) (forall (c nat) (= (nat.lt (nat.add a c) (nat.add b c)) (nat.lt a b))))))
  (#spec le.iff_lt_or_eq
    (forall (a nat) (forall (b nat) (= (nat.le a b) (or (nat.lt a b) (= a b))))))
  (#spec lt.trichotomy
    (forall (a nat) (forall (b nat) (or (nat.lt a b) (or (= a b) (nat.lt b a))))))
  (#spec add.lt_add
    (forall (a nat) (forall (b nat) (forall (c nat) (forall (d nat) (==> (nat.lt a b) (==> (nat.lt c d) (nat.lt (nat.add a c) (nat.add b d)))))))))
  (#spec lt.cross
    (forall (p nat) (forall (q nat) (forall (r nat) (forall (s nat) (==> (= (nat.add p s) (nat.add r q)) (= (nat.lt p q) (nat.lt r s))))))))
  (#spec le.cross
    (forall (p nat) (forall (q nat) (forall (r nat) (forall (s nat) (==> (= (nat.add p s) (nat.add r q)) (= (nat.le p q) (nat.le r s))))))))
  (#spec pow.add
    (forall (a nat) (forall (m nat) (forall (n nat) (= (nat.pow a (nat.add m n)) (nat.mul (nat.pow a m) (nat.pow a n)))))))
  (#spec shl.eq_mul_pow
    (forall (a nat) (forall (m nat) (= (nat.shl a m) (nat.mul a (nat.pow 2 m))))))
)
