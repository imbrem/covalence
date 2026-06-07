name: relation-natural
version: 1.39
description: Relations over natural numbers
author: Joe Leslie-Hurd <joe@gilith.com>
license: MIT
requires: bool
requires: function
requires: natural
requires: relation-def
requires: relation-thm
requires: relation-well-founded
requires: set
show: "Data.Bool"
show: "Function"
show: "Number.Natural"
show: "Relation"

def {
  package: relation-natural-def-1.26
  checksum: bb6564664b7136f9979da87aed52df68a786e00f
}

thm {
  import: def
  package: relation-natural-thm-1.44
  checksum: 39cd05bb1255d3a37faad824a78d1f928e14c597
}

main {
  import: def
  import: thm
}
