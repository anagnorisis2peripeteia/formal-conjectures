import Mathlib

attribute [local irreducible] Nat.add_comm

example (a b : Nat) : a + b = b + a := by
  simp
