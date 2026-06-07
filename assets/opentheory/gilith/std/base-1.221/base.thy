name: base
version: 1.221
description: The standard theory library
author: Joe Leslie-Hurd <joe@gilith.com>
license: MIT
homepage: http://opentheory.gilith.com/?pkg=base
show: "Data.Bool"
show: "Data.List"
show: "Data.Option"
show: "Data.Pair"
show: "Data.Sum"
show: "Data.Unit"
show: "Function"
show: "Number.Natural"
show: "Number.Real"
show: "Relation"
show: "Set"
haskell-name: opentheory
haskell-int-file: haskell.int
haskell-src-file: haskell.art
haskell-test-file: haskell-test.art
haskell-equality-type: "Data.List.list"
haskell-equality-type: "Data.Option.option"
haskell-equality-type: "Data.Pair.*"
haskell-equality-type: "Data.Sum.+"
haskell-equality-type: "Number.Natural.natural"
haskell-arbitrary-type: "Data.List.list"
haskell-arbitrary-type: "Data.Option.option"
haskell-arbitrary-type: "Data.Pair.*"
haskell-arbitrary-type: "Data.Sum.+"
haskell-arbitrary-type: "Number.Natural.natural"

bool {
  package: bool-1.37
  checksum: 3ce9f58a6d6373bd7540fd16b482130ece4799b8
}

unit {
  import: bool
  package: unit-1.21
  checksum: 098b2cf5bceac9960544b90b9747f4d175bf0fc9
}

function {
  import: bool
  package: function-1.55
  checksum: 35d4e6c28baaee5cee8c39751d651af7d7cfe5dc
}

pair {
  import: bool
  import: function
  package: pair-1.30
  checksum: e056c94ca855aed96b2ca200718657c1c056d245
}

natural {
  import: bool
  import: function
  package: natural-1.112
  checksum: ff4fccf76261abbdf062f6e9501580aa78d5049d
}

set {
  import: bool
  import: function
  import: pair
  import: natural
  package: set-1.85
  checksum: dfd75b0733fea6cfb8b4bf2626f86532f8f3992a
}

relation {
  import: bool
  import: function
  import: pair
  import: natural
  import: set
  package: relation-1.63
  checksum: 1e86fb7c0edc0ea67c3583a227c66d7975f4ab0a
}

sum {
  import: bool
  import: pair
  import: natural
  package: sum-1.61
  checksum: b308349b08d4b77294d83a789a1ecb56a7359c44
}

option {
  import: bool
  import: function
  import: natural
  package: option-1.72
  checksum: de65c07af309d3986ad380dfb7329c4faae24abf
}

list {
  import: bool
  import: function
  import: pair
  import: natural
  import: set
  package: list-1.107
  checksum: dbf869cbb3abd4c940c1fbc11ca12bd33661e015
}

real {
  import: bool
  import: function
  import: pair
  import: natural
  import: set
  package: real-1.61
  checksum: 4eb38ef27f905a03c025066f45722bb05fc6eda9
}

main {
  import: bool
  import: unit
  import: function
  import: pair
  import: natural
  import: set
  import: relation
  import: sum
  import: option
  import: list
  import: real
}
