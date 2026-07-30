import WOWII217Closure13Fast

example (g : Nat) (h : g = 3) : True := by
  generalize h' : g = x
  trivial
