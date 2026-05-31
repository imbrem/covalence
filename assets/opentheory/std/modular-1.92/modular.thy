name: modular
version: 1.92
description: Parametric theory of modular arithmetic
author: Joe Leslie-Hurd <joe@gilith.com>
license: MIT
requires: base
requires: modular-witness
requires: natural-bits
requires: natural-divides
requires: probability
show: "Data.Bool"
show: "Number.Modular"
show: "Number.Natural"
show: "Probability.Random"
hol-light-int-file: hol-light.int
hol-light-thm-file: hol-light.art

def {
  package: modular-def-1.85
  checksum: 5ae2c622d9003a6de3fab81dc34830b5edd48a21
}

thm {
  import: def
  package: modular-thm-1.66
  checksum: d3529917c7f6faab24ed2dbcd3d5b4a215d1ccc0
}

main {
  import: def
  import: thm
}
