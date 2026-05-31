name: relation
version: 1.63
description: Relation operators
author: Joe Leslie-Hurd <joe@gilith.com>
license: MIT
requires: bool
requires: function
requires: natural
requires: pair
requires: set
show: "Data.Bool"
show: "Data.Pair"
show: "Function"
show: "Number.Natural"
show: "Relation"
show: "Set"

def {
  package: relation-def-1.25
  checksum: 9f7a83d975e6e78994a4c5cbf2a328f27bc1d513
}

thm {
  import: def
  package: relation-thm-1.15
  checksum: d7008776d55f6c2701e81a162a7f24486e8db96a
}

well-founded {
  import: def
  import: thm
  package: relation-well-founded-1.56
  checksum: 45a67e08acc2b9649be3dc26258c195c16eadc9a
}

natural {
  import: def
  import: thm
  import: well-founded
  package: relation-natural-1.39
  checksum: 09d44e8e8fc16e4bf812940c2d86d51d5ee2a9fe
}

main {
  import: def
  import: thm
  import: well-founded
  import: natural
}
