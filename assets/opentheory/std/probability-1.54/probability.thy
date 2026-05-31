name: probability
version: 1.54
description: Probability
author: Joe Leslie-Hurd <joe@gilith.com>
license: MIT
homepage: http://opentheory.gilith.com/?pkg=probability
requires: base
requires: stream
show: "Data.Bool"
show: "Data.List"
show: "Data.Pair"
show: "Data.Stream"
show: "Function"
show: "Number.Natural"
show: "Probability.Random"
hol-light-int-file: hol-light.int
hol-light-thm-file: hol-light.art
haskell-int-file: haskell.int
haskell-src-file: haskell.art
haskell-arbitrary-type: "Probability.Random.random"

def {
  package: probability-def-1.42
  checksum: bd32f1836319b2298e22daf5239b4d66583cd8dc
}

thm {
  import: def
  package: probability-thm-1.20
  checksum: 273c4473bc1871452598224e52ad2659944977cd
}

main {
  import: def
  import: thm
}
