import Mathlib

example (b : Bool) (h : b = true) : True := by
  generalize hb : b = x
  have hx : x = true := by simpa [hb] using h
  subst x
  trivial
