name: option
version: 1.72
description: Option types
author: Joe Leslie-Hurd <joe@gilith.com>
license: MIT
requires: bool
requires: function
requires: natural
show: "Data.Bool"
show: "Data.Option"
show: "Function"
show: "Number.Natural"

def {
  package: option-def-1.61
  checksum: 01e7e75e16564c5a3a32d891fc6e5f80893b4eb9
}

thm {
  import: def
  package: option-thm-1.54
  checksum: d9e75246e4bc739cc3ec3ce6382176a7d3bc4f6e
}

dest {
  import: def
  import: thm
  package: option-dest-1.56
  checksum: f23e3a6032268fd3c5e1525ee665f42defcfd83d
}

map {
  import: def
  import: thm
  package: option-map-1.14
  checksum: 8d0c71b57363fe40b2f39dd3c3a510f1f9421c07
}

main {
  import: def
  import: thm
  import: dest
  import: map
}
