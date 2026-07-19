(in-package "ACL2")

; This is the literal-width form used by x86isa/utils/basic-structs.lisp.
(defbitstruct 8bits 8)

; Aggregate layouts remain outside the bounded expansion.
(defbitstruct byte-pair
  ((low 8bits)
   (high 8bits))
  :inline t)
