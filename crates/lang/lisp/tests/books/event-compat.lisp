(in-package "ACL2")

(set-inhibit-warnings "theory")
(set-gag-mode nil)

(encapsulate ()
  (logic)
  (defun-inline inline-id (x)
    x)
  (verify-guards inline-id)
  (defthm inline-id-a
    (equal (inline-id (quote a)) (quote a))))

; Ordered table state is recorded explicitly for later make-event queries.
(table importer-sensitive-setting :key :value)
