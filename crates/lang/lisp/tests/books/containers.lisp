(defsection linked-section
  "A transparent section."
  :parents (acl2)
  (defund section-id (x) x)
  (defthmd section-ground
    (equal (section-id (quote a)) (quote a))))

(progn
  (defthm progn-ground (equal (+ 7 8) 15)))
