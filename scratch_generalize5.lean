import Mathlib

example (f : Nat → Nat) (a : Nat) (h : f a = 3) : True := by
  generalize hx : f a = x at h
  trace_state
  trivial
