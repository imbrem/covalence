name: list-reverse
version: 1.50
description: The list reverse function
author: Joe Leslie-Hurd <joe@gilith.com>
license: MIT
requires: bool
requires: list-append
requires: list-def
requires: list-length
requires: list-map
requires: list-set
requires: natural
requires: set
show: "Data.Bool"
show: "Data.List"
show: "Number.Natural"
show: "Set"

def {
  package: list-reverse-def-1.48
  checksum: cbf546f9f0f42720e5922d29cf5f36f6f2dc5492
}

thm {
  import: def
  package: list-reverse-thm-1.20
  checksum: bb433cf4f1279715fcf11cfb2428d0bfe7511a3c
}

main {
  import: def
  import: thm
}
