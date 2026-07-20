(in-package "ACL2")

(local
 (make-event
  '(progn
     (defthm local-generated-a (equal 1 1))
     (defthm local-generated-b (equal 2 2)))))

(defthm public-after-local (equal 3 3))
