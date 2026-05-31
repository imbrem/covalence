name: word-bits
version: 1.100
description: Word to bit-list conversions
author: Joe Leslie-Hurd <joe@gilith.com>
license: MIT
requires: base
requires: natural-bits
requires: word-def
show: "Data.Bool"
show: "Data.List"
show: "Data.Word"
show: "Data.Word.Bits"
show: "Number.Natural"

def {
  package: word-bits-def-1.85
  checksum: 9b0192c383a8f5336382264e24cb981d1da993ae
}

thm {
  import: def
  package: word-bits-thm-1.100
  checksum: d821764281fec050af704b3d0e23e9f3296aab45
}

main {
  import: def
  import: thm
}
