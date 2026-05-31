name: natural-divides-lcm
version: 1.0
description: Natural number least common multiple
author: Joe Leslie-Hurd <joe@gilith.com>
license: MIT
requires: base
requires: natural-divides-def
requires: natural-divides-gcd
requires: natural-divides-thm
show: "Data.Bool"
show: "Number.Natural"

def {
  package: natural-divides-lcm-def-1.0
  checksum: 5286f18fcc7de1e800747c9bcae0713dd188971b
}

thm {
  import: def
  package: natural-divides-lcm-thm-1.0
  checksum: 492b9462ef1667dfab2de59249d4df44d8eca454
}

main {
  import: def
  import: thm
}
