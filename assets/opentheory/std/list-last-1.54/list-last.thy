name: list-last
version: 1.54
description: The last list function
author: Joe Leslie-Hurd <joe@gilith.com>
license: MIT
requires: bool
requires: list-append
requires: list-def
requires: list-dest
requires: list-reverse
requires: list-thm
show: "Data.Bool"
show: "Data.List"

def {
  package: list-last-def-1.47
  checksum: 063834272449def434a9b7e136fcd1ca34b70eb4
}

thm {
  import: def
  package: list-last-thm-1.42
  checksum: 628ca2e16ad64ea06963ccdbf7a0b4b1e989fe1e
}

main {
  import: def
  import: thm
}
