// PEANO-MAX — conditional rewriting (K `requires`) with NO hooks. `leq` is a
// first-order recursive predicate returning true()/false(); `max` is defined by
// two guarded rules. A guard fires only when its condition reduces to true().
module PEANO-MAX
  syntax Bool ::= "true" | "false"
  rule leq(z(), N)       => true()
  rule leq(s(M), z())    => false()
  rule leq(s(M), s(N))   => leq(M, N)
  rule max(M, N) => N requires leq(M, N)
  rule max(M, N) => M requires leq(N, M)
endmodule
