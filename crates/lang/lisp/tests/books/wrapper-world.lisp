(in-package "ACL2")

(defxdoc importer-doc :short "Documentation only.")
(defxdoc+ importer-doc :long "More documentation.")
(xdoc::set-default-parents importer-doc)
(xdoc::order-subtopics importer-doc nil t)
(xdoc::add-resource-directory "sample" "images")

(with-output :off :all :gag-mode nil
  (defund-inline wrapped-id (x) x))

(progn!
  (defthm wrapped-id-a
    (equal (wrapped-id (quote a)) (quote a))))

(push-untouchable (wrapped-id) t)

; PROGRAM changes subsequent definition semantics and remains unresolved.
; SET-STATE-OK is admission-control state retained for proof-world replay.
(program)
(set-state-ok t)
