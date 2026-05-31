name: natural-bits
version: 1.72
description: Natural number to bit-list conversions
author: Joe Leslie-Hurd <joe@gilith.com>
license: MIT
homepage: http://opentheory.gilith.com/?pkg=natural-bits
requires: base
requires: probability
show: "Data.Bool"
show: "Data.List"
show: "Data.Pair"
show: "Function"
show: "Number.Natural"
show: "Probability.Random"
hol-light-int-file: hol-light.int
hol-light-thm-file: hol-light.art
haskell-name: opentheory-bits
haskell-int-file: haskell.int
haskell-src-file: haskell.art

def {
  package: natural-bits-def-1.31
  checksum: d3b322d91850c4c6fedf840cc18dcc7fb27aca1d
}

thm {
  import: def
  package: natural-bits-thm-1.57
  checksum: cee34b637312544f60b2db476dcb9d01b881d29a
}

main {
  import: def
  import: thm
}
