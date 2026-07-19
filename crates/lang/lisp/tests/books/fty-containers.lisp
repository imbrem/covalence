(in-package "ACL2")

(fty::defprod packet
  ((tag symbolp)
   (payload true-listp))
  :layout :list
  ///
  (defthm packet-post-obligation
    (implies (packet-p x) (true-listp x))))

(fty::deflist packet-list
  :elt-type packet
  :true-listp t)

(fty::defoption maybe-packet packet-p)
