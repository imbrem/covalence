name: unit
version: 1.21
description: The unit type
author: Joe Leslie-Hurd <joe@gilith.com>
license: MIT
requires: bool
show: "Data.Bool"
show: "Data.Unit"

def {
  package: unit-def-1.13
  checksum: 5f6feb4c479325bbb29dd41bcf726dc252ee0910
}

thm {
  import: def
  package: unit-thm-1.17
  checksum: 0503f8acde52725c922d2c6d4c4290ab592562f2
}

main {
  import: def
  import: thm
}
