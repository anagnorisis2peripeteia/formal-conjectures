import Mathlib

example : True := by
  attribute [simp] Nat.add_comm
  trivial
