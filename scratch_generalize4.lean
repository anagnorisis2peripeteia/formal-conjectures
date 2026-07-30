import Mathlib

example (f : Nat → Nat) (a : Nat) (h : f a = 3) : True := by
  generalize ha : f a = x at h
  have hx : x = 3 := by simpa [ha] using h
  subst x
  trivial
