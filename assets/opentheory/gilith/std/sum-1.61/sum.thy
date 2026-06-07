name: sum
version: 1.61
description: Sum types
author: Joe Leslie-Hurd <joe@gilith.com>
license: MIT
requires: bool
requires: natural
requires: pair
show: "Data.Bool"
show: "Data.Pair"
show: "Data.Sum"
show: "Number.Natural"

def {
  package: sum-def-1.67
  checksum: 70559fe2cff865e12eed2572bf2168296e3be301
}

thm {
  import: def
  package: sum-thm-1.3
  checksum: b7518ab1d3476e2eb3d7af688d6961a0a467e9a4
}

main {
  import: def
  import: thm
}
