(in-package "ACL2")

(def-generic-rule listp-rules generic-ground
  (equal (+ 2 3) 5)
  :rule-classes :rewrite
  :tags (sample))

(def-listp-rule listp-ground
  (equal (+ 3 4) 7)
  :hints nil)

(def-projection-rule projection-ground
  (equal (+ 4 5) 9)
  :disable t)
