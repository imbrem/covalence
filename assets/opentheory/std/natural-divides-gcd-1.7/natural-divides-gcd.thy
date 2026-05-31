name: natural-divides-gcd
version: 1.7
description: Natural number greatest common divisor
author: Joe Leslie-Hurd <joe@gilith.com>
license: MIT
requires: base
requires: natural-divides-def
requires: natural-divides-thm
show: "Data.Bool"
show: "Data.Pair"
show: "Number.Natural"
show: "Relation"

def {
  package: natural-divides-gcd-def-1.3
  checksum: 533aef22d91ee7b4a1247e6e804f31e7bcf622f6
}

thm {
  import: def
  package: natural-divides-gcd-thm-1.7
  checksum: 793bf67e08cc1779fcf7a4729f5f255d40dc8b73
}

main {
  import: def
  import: thm
}
