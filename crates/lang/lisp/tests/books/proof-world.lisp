(in-package "ACL2")

(defthm-unsigned-byte-p byte-bound
  :hyp t :bound 8 :concl 3 :gen-linear t)
(defthm-signed-byte-p signed-bound
  :hyp t :bound 8 :concl -1 :gen-type t)
(defruledl local-disabled-ground (equal (+ 1 1) 2))

; Standard implicit equivalence/congruence forms generate exact obligations.
(defequiv equal)
(defcong equal equal (+ x y) 1)

; Malformed trailing syntax remains unresolved.
(defequiv malformed-equivalence extra)

(in-theory (e/d (foo) (bar baz)))
(def-ruleset sample-rules '(foo bar))
(add-to-ruleset sample-rules '(baz))
