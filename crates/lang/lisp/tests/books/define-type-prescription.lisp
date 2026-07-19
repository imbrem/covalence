(in-package "ACL2")

(define natural-id ((x natp))
  x
  :type-prescription (natp (natural-id x)))
