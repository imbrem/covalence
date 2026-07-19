(in-package "ACL2")

(defun alias-target (x) x)
(defmacro alias-view (x) `(alias-target ,x))
(add-macro-alias alias-view alias-target)

(defthm alias-view-ground
  (equal (alias-view 'a) 'a))

(add-macro-alias alias-target alias-view)
(add-macro-alias missing-view missing-target)
