(in-package "ACL2")

(defthm-using-gl gl-identity
  :hyp (natp x)
  :concl (equal x x)
  :g-bindings ((x (:g-number 0))))

(local
 (def-gl-thm local-gl-identity
   :concl (equal y y)
   :g-bindings ((y (:g-number 0)))))
