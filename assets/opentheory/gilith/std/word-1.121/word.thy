name: word
version: 1.121
description: Parametric theory of words
author: Joe Leslie-Hurd <joe@gilith.com>
license: MIT
requires: base
requires: natural-bits
requires: natural-divides
requires: probability
requires: word-witness
show: "Data.Bool"
show: "Data.List"
show: "Data.Word"
show: "Data.Word.Bits"
show: "Number.Natural"
show: "Probability.Random"
hol-light-int-file: hol-light.int
hol-light-thm-file: hol-light.art

def {
  package: word-def-1.81
  checksum: 96817017df5c56e707283d2aa923f82027f7a47e
}

bits {
  import: def
  package: word-bits-1.100
  checksum: 0d5a72eab8491e05988b7a26cca08674566f4814
}

main {
  import: def
  import: bits
}
