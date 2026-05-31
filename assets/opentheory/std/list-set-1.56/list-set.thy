name: list-set
version: 1.56
description: List to set conversions
author: Joe Leslie-Hurd <joe@gilith.com>
license: MIT
requires: bool
requires: list-def
requires: list-dest
requires: list-length
requires: natural
requires: set
show: "Data.Bool"
show: "Data.List"
show: "Number.Natural"
show: "Set"

def {
  package: list-set-def-1.53
  checksum: eb885d37d937fc38d799e7360fc407504130d7da
}

thm {
  import: def
  package: list-set-thm-1.52
  checksum: b13a6d8784cf12cb6474c5b9b09f15753782a147
}

main {
  import: def
  import: thm
}
