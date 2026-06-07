name: list-zip
version: 1.31
description: The list zip functions
author: Joe Leslie-Hurd <joe@gilith.com>
license: MIT
requires: bool
requires: list-append
requires: list-def
requires: list-dest
requires: list-fold
requires: list-length
requires: list-map
requires: list-nth
requires: list-thm
requires: natural
requires: pair
show: "Data.Bool"
show: "Data.List"
show: "Data.Pair"
show: "Number.Natural"

def {
  package: list-zip-def-1.23
  checksum: 94cd14b9e697b97dccb54d697e70881d964a7f33
}

thm {
  import: def
  package: list-zip-thm-1.27
  checksum: 0da673d0ac0ccbfd5c6a0a4f13b0baaea4457faf
}

main {
  import: def
  import: thm
}
