(in-package "ACL2")

(fty::deffixtype sample
  :pred sample-p
  :fix sample-fix
  :equiv sample-equiv
  :define t
  :forward t)

; Existing-equivalence registrations require a different bounded expansion.
(fty::deffixtype existing
  :pred existing-p
  :fix existing-fix
  :equiv existing-equiv
  :define nil)
