; mixed.lisp — the deliberately-mixed book: one event (at least) per tally
; category. The test asserts this book's EXACT tally.

(in-package "ACL2")

; A satisfied dependency: its events are processed into the same tally
; (the include itself is a skip; the contents are their own rows).
(include-book "app-basics")

; Re-inclusion is idempotent (ACL2 semantics): skipped.
(include-book "app-basics")

; A dependency we do not ship: recorded as a skipped dependency, not an error.
(include-book "no-such-book")

; :dir books need a configured system book directory, which this slice
; does not have: skipped.
(include-book "arithmetic/top" :dir :system)

; local events are processed pass-1 style (the defun IS installed and usable
; below) but tallied as skipped — nothing is undone at end-of-book.
(local (defun pair-up (x) (cons x x)))

; ...so this ground defthm over the local defun is provable (by reduction,
; riding the pair-up defun hypothesis): admitted in dialect.
(defthm pair-up-a
  (equal (pair-up (quote a)) (cons (quote a) (quote a))))

; :hints / :rule-classes are IGNORED but recorded; the bare goal is in the
; reified fragment: transported.
(defthm three-with-hints
  (equal (+ 1 2) 3)
  :hints (("Goal" :in-theory (enable app)))
  :rule-classes :rewrite)

; implies-goals parse as events; the prover slice cannot take them (free
; variables need induction; implies is not a dialect head): rejected.
(defthm consp-implies
  (implies (consp x) (equal (car (cons (car x) (quote ()))) (car x))))

; A false ground goal is refuted by computation, never admitted: rejected.
(defthm bogus
  (equal (+ 2 2) 5))

; Unsupported event classes are rejected with reasons.
(defmacro appq (x y)
  (app x y))

(encapsulate ()
  (defthm hidden (equal 1 1)))

(mutual-recursion
  (defun evenish (x) (if (endp x) t (oddish (cdr x))))
  (defun oddish (x) (if (endp x) nil (evenish (cdr x)))))
