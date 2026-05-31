name: word-def
version: 1.81
description: Definition of word operations
author: Joe Leslie-Hurd <joe@gilith.com>
license: MIT
provenance: HOL Light theory extracted on 2014-11-17
requires: base
requires: natural-bits
requires: natural-divides
requires: probability
requires: word-witness
show: "Data.Bool"
show: "Data.Word"
show: "Number.Natural"
show: "Probability.Random"

def {
  article: "word-def.art"
}

modular {
  import: def
  interpretation: "modular.int"
  package: modular-1.92
  checksum: 54fb32196e0b9b4803cff847d074c080dae9e564
}

main {
  import: def
  import: modular
}
