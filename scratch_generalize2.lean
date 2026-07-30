import WOWII217Closure13Fast

example (n : Nat) (h : n = 0) : True := by
  intro
  generalize h' : n = m
  trivial
