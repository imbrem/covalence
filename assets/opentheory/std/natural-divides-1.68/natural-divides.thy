name: natural-divides
version: 1.68
description: The divides relation on natural numbers
author: Joe Leslie-Hurd <joe@gilith.com>
license: MIT
homepage: http://opentheory.gilith.com/?pkg=natural-divides
requires: base
show: "Data.Bool"
show: "Data.Pair"
show: "Number.Natural"
show: "Relation"
hol-light-int-file: hol-light.int
hol-light-thm-file: hol-light.art
haskell-name: opentheory-divides
haskell-category: Number Theory
haskell-int-file: haskell.int
haskell-src-file: haskell.art
haskell-test-file: haskell-test.art

def {
  package: natural-divides-def-1.41
  checksum: d0b2af6b068eb3e39c2268bd96988e581d1595ab
}

thm {
  import: def
  package: natural-divides-thm-1.52
  checksum: ab2d2a005df4bbf8c977096846ddf8fd7f423ee5
}

gcd {
  import: def
  import: thm
  package: natural-divides-gcd-1.7
  checksum: e3e4f0655fdf4fb8017f4c564eedd0f507373dc3
}

lcm {
  import: def
  import: thm
  import: gcd
  package: natural-divides-lcm-1.0
  checksum: 48ce6659977540183d3654de11b5eb29757f1d35
}

main {
  import: def
  import: thm
  import: gcd
  import: lcm
}
