(in-package "ACL2")

(define plain-id (x) x)
(defun-nx nx-id (x) x)
(defn old-id (x) x)

(defrule plain-id-a
  (equal (plain-id (quote a)) (quote a))
  :rule-classes :rewrite)
(defruled nx-id-a
  (equal (nx-id (quote a)) (quote a)))
(defrulel old-id-a
  (equal (old-id (quote a)) (quote a)))

; Common std/util/define metadata preserves the recoverable logical body.
(define typed-id ((x consp)) x)
(define extended-id ((x consp :type t))
  :guard (consp x)
  :measure (acl2-count x)
  :verify-guards nil
  :returns (result consp)
  x
  ///
  "Post-definition documentation."
  (defrule extended-id-a
    (equal (extended-id (quote a)) (quote a))))

; Multiple returns and unknown expansion-affecting options stay rejected.
(define returns-two (x)
  :returns (mv left right)
  (cons x x))
(define prepwork-id (x)
  :prepwork ((defun hidden-helper (y) y))
  x)

; std::define also accepts metadata after the logical body.
(define post-metadata-id (x)
  x
  :guard-hints (("Goal" :in-theory nil)))
