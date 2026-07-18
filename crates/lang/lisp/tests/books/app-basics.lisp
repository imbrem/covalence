; app-basics.lisp — the append / reverse / length staples, community-book
; style, over the covalence ACL2 slice.
;
; Reader notes (see notes/vibes/lisp/acl2-book-frontend.md §2): explicit
; (quote ...) — the shared S-expression parser has no ' reader macro — and
; single-`;` line comments only.

(in-package "ACL2")

(defun app (x y)
  (if (consp x)
      (cons (car x) (app (cdr x) y))
    y))

(defun rev (x)
  (if (consp x)
      (app (rev (cdr x)) (cons (car x) (quote ())))
    (quote ())))

(defun len2 (x)
  (if (endp x)
      0
    (+ 1 (len2 (cdr x)))))

; Ground lemmas. Goals inside the reified fragment (quoted data, integer
; literals, car/cdr/cons/consp/equal/+) go through the Derivable_ACL2
; certificate + the machine-checked soundness metatheorem and are TRANSPORTED
; to closed base-HOL model equations; the rest are proved by certified
; kernel reduction, riding their defun equations as hypotheses.

(defthm four
  (equal (+ 2 2) 4))

(defthm car-app
  (equal (car (cons (quote a) (quote (b)))) (quote a)))

(defthm app-ab-c
  (equal (app (quote (a b)) (quote (c))) (quote (a b c))))

(defthm rev-rev-ab
  (equal (rev (rev (quote (a b)))) (quote (a b))))

(defthm len2-abc
  (equal (len2 (quote (a b c))) 3))

; The universally quantified staples. These need induction, which the book
; pipeline does not wire yet (the kernel-side S6 route exists — see
; source-local TODO markers): honestly rejected, never faked.

(defthm app-assoc
  (equal (app (app x y) z) (app x (app y z))))

(defthm len2-app
  (equal (len2 (app x y)) (+ (len2 x) (len2 y))))
