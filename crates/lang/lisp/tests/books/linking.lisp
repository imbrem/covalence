; Extensionless relative lookup probes .lisp, .lsp, then .acl2.
(include-book "linked/relative")

; A named root is explicit authority for :dir lookup.
(include-book "arithmetic/top" :dir :system)

; Unknown roots remain honest skips rather than falling back elsewhere.
(include-book "arithmetic/top" :dir :missing)

; Options unrelated to linking are recorded, without disabling the include.
(include-book "linked/explicit.acl2" :uncertified-okp t)
