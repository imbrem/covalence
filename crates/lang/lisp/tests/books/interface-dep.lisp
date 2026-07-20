(in-package "ACL2")

; The interface imports no logical authority from this source.  Its only
; acknowledged capability is the frontend's built-in transparent DEFSECTION
; handling used by the target.
(defmacro defsection (name &rest events)
  `(progn ,@events))
