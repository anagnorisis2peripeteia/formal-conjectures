import Mathlib

example (a n : Nat) (b : Bool) (h : a + (n + 1) < 31) : a + (if b then 1 else 0) + n < 31 := by
  omega
