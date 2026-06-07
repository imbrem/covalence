name: relation-well-founded
version: 1.56
description: Well-founded relations
author: Joe Leslie-Hurd <joe@gilith.com>
license: MIT
requires: bool
requires: pair
requires: relation-def
requires: relation-thm
show: "Data.Bool"
show: "Data.Pair"
show: "Relation"

def {
  package: relation-well-founded-def-1.38
  checksum: 8dac1adb31a0915d7cf32d96dd58e8b7505c72cd
}

thm {
  import: def
  package: relation-well-founded-thm-1.63
  checksum: e2701505ef0b4d5a64306ffa6f2e4f19f7632016
}

main {
  import: def
  import: thm
}
