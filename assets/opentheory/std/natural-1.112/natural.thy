name: natural
version: 1.112
description: The natural numbers
author: Joe Leslie-Hurd <joe@gilith.com>
license: MIT
requires: bool
requires: function
show: "Data.Bool"
show: "Function"
show: "Number.Natural"

axiom-infinity {
  package: axiom-infinity-1.12
  checksum: 53e364be097eb2d2284001aa97935dcee31a969c
}

def {
  import: axiom-infinity
  package: natural-def-1.29
  checksum: 881d4b54385e84df7360d40052b061eb8bc67893
}

thm {
  import: def
  package: natural-thm-1.22
  checksum: 5c21d070b2f254a88335be15c935de8808de25b6
}

dest {
  import: thm
  package: natural-dest-1.18
  checksum: b2e09315a88f198b20aa98e636c5828d3aeec233
}

numeral {
  import: thm
  package: natural-numeral-1.20
  checksum: d60228fe9c6d0bfacfeb3e1ce8eb00022e67b883
}

order {
  import: def
  import: thm
  package: natural-order-1.52
  checksum: 937d23a213b188a327fbeea8a52499174616ec0b
}

add {
  import: def
  import: thm
  import: dest
  import: numeral
  import: order
  package: natural-add-1.68
  checksum: f9341138585730a5deae7f1e40b1ff84b93c8203
}

mult {
  import: def
  import: thm
  import: numeral
  import: order
  import: add
  package: natural-mult-1.61
  checksum: 9c28888dd90df611c9be94870701eb5d4713d069
}

div {
  import: def
  import: thm
  import: numeral
  import: order
  import: add
  import: mult
  package: natural-div-1.57
  checksum: eb81638e71b78e109466f6c04c217ce68c4e36d4
}

exp {
  import: def
  import: thm
  import: numeral
  import: order
  import: add
  import: mult
  import: div
  package: natural-exp-1.53
  checksum: 686af29b672bfd642a5f1ecad073e563caf11e92
}

factorial {
  import: def
  import: thm
  import: numeral
  import: order
  import: add
  import: mult
  package: natural-factorial-1.39
  checksum: 2d5aa3c8377c9f9089a75ebaf29913c94b5e91ef
}

distance {
  import: thm
  import: numeral
  import: order
  import: add
  import: mult
  package: natural-distance-1.52
  checksum: ead8b0b469ebabd24b83f8f6356f412e8710f607
}

funpow {
  import: def
  import: thm
  import: numeral
  import: add
  import: mult
  package: natural-funpow-1.17
  checksum: 06b3d82f505ad5c709d22cb2693e99cb9e5704a9
}

main {
  import: axiom-infinity
  import: def
  import: thm
  import: dest
  import: numeral
  import: order
  import: add
  import: mult
  import: div
  import: exp
  import: factorial
  import: distance
  import: funpow
}
