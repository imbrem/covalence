// PEANO — first-order natural-number arithmetic (Covalence K demo).
// Reduces via covalence_init::k::KSession. Nullary constructors are written
// applied (z()); variables are bare (M, N). No hooks, no cells, no binders.
module PEANO
  syntax Nat ::= "z" | s(Nat) | plus(Nat, Nat) | mult(Nat, Nat)
  rule plus(z(), N) => N
  rule plus(s(M), N) => s(plus(M, N))
  rule mult(z(), N) => z()
  rule mult(s(M), N) => plus(N, mult(M, N))
endmodule
