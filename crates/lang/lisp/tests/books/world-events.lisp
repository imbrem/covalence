(in-package "ACL2")

(defconst *byte-mask* (- (expt 2 8) 1))

(defun generate-registers ()
  `(defconsts (*r0* *r1* *register-count*)
     ,(cons 'mv (append (increasing-list 0 1 2) (list 2)))))

(make-event (generate-registers))

(defconst *last-register* (- *register-count* 1))

(defmacro define-mask (name &rest bytes)
  `(defconst ,name (list ,@bytes)))

(define-mask *masks* #x0f #xf0)

(defmacro unsupported-key (name &key value)
  `(defconst ,name ,value))

(unsupported-key *must-not-exist* :value 7)
