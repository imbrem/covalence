name: list
version: 1.107
description: List types
author: Joe Leslie-Hurd <joe@gilith.com>
license: MIT
requires: bool
requires: function
requires: natural
requires: pair
requires: set
show: "Data.Bool"
show: "Data.List"
show: "Data.Pair"
show: "Function"
show: "Number.Natural"
show: "Set"

def {
  package: list-def-1.63
  checksum: 14ec565fcc461c3e04db57f3fca0e89ef3e293a4
}

thm {
  import: def
  package: list-thm-1.55
  checksum: ad4e20d2a7cc4abcd7553428a7b248f548475f36
}

dest {
  import: def
  import: thm
  package: list-dest-1.50
  checksum: 8ddb9caa57e83c2d898166ef9c114a5d4dfcfd0a
}

length {
  import: def
  import: thm
  import: dest
  package: list-length-1.53
  checksum: 2d525f962af99dbb7d028b81f5e8322da9f6053c
}

set {
  import: def
  import: dest
  import: length
  package: list-set-1.56
  checksum: ce1bde367d70c272059ff24bf74821a3d21774d1
}

append {
  import: def
  import: thm
  import: dest
  import: length
  import: set
  package: list-append-1.59
  checksum: 6e0d26ce66604917635099b9147448640a708170
}

map {
  import: def
  import: thm
  import: dest
  import: length
  import: set
  import: append
  package: list-map-1.54
  checksum: fc460c62d5a52430cc8c5402798eb6b19ef812be
}

filter {
  import: def
  import: length
  import: set
  import: append
  import: map
  package: list-filter-1.55
  checksum: 12c55193f9ba7cb378c318b174bd6aab7c32c8a1
}

reverse {
  import: def
  import: length
  import: set
  import: append
  import: map
  package: list-reverse-1.50
  checksum: cc941ee3d2f427d68c5dd191d8591b63ec30fc0b
}

fold {
  import: def
  import: length
  import: append
  import: reverse
  package: list-fold-1.29
  checksum: f04fe88c3ef8354213008ace7189e37390c8840a
}

last {
  import: def
  import: thm
  import: dest
  import: append
  import: reverse
  package: list-last-1.54
  checksum: f8c7a22a66273bc3c7f2e471df1c6547ade21efd
}

nth {
  import: def
  import: thm
  import: dest
  import: length
  import: set
  import: append
  import: map
  import: last
  package: list-nth-1.62
  checksum: 9ecb1d7d4d3a567ec08f4034a9fbf00be1617bd5
}

replicate {
  import: def
  import: thm
  import: length
  import: set
  import: append
  import: map
  import: nth
  package: list-replicate-1.62
  checksum: e35dfead4d202a6a4ae87c2a26154e1a6e4f6c7f
}

take-drop {
  import: def
  import: thm
  import: dest
  import: length
  import: append
  import: nth
  import: replicate
  package: list-take-drop-1.63
  checksum: a8d0f2a72e094d860531d9c8b76c38997eebf6b2
}

interval {
  import: length
  import: map
  import: nth
  package: list-interval-1.61
  checksum: be1fcf160a98813a1b44ff655af63c202df01feb
}

zip {
  import: def
  import: dest
  import: fold
  import: length
  import: append
  import: map
  import: nth
  import: thm
  package: list-zip-1.31
  checksum: a46998adf1a558a80d81ce979c9728a8aac97b81
}

nub {
  import: def
  import: length
  import: reverse
  import: set
  package: list-nub-1.57
  checksum: d5f1a3e97bade3b0aa1b96c3b6ed2be53243d147
}

main {
  import: def
  import: thm
  import: dest
  import: length
  import: set
  import: append
  import: map
  import: filter
  import: reverse
  import: fold
  import: last
  import: nth
  import: replicate
  import: take-drop
  import: interval
  import: zip
  import: nub
}
