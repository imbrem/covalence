(in-package "ACL2")
(include-book "interface-dep")

(defsection interface-demo
  (defthm interface-target-theorem
    (equal 'interface-ok 'interface-ok)))
