// BOOLSIMP — boolean simplification over hand-declared tt()/ff() (no BOOL hook).
module BOOLSIMP
  syntax B ::= "tt" | "ff" | and(B, B) | or(B, B) | neg(B)
  rule and(tt(), X) => X
  rule and(ff(), X) => ff()
  rule or(tt(), X) => tt()
  rule or(ff(), X) => X
  rule neg(tt()) => ff()
  rule neg(ff()) => tt()
endmodule
