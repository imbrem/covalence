(in-package "ACL2")

(define wrapper-id (x)
  :returns (value integerp)
  x
  ///
  (std::more-returns
   (value (equal value x)
          :name wrapper-id-exact)))

(acl2::with-supporters
 (local (defthm local-supporter (equal 1 1)))
 :names (local-supporter)
 (defthm exported-with-supporter t))

(assert-event (equal (+ 2 3) 5))
(assert-event nil)
(assert-event (unknown-assertion-function 1))
