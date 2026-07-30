import WOWII217Closure13Fast
import WOWII217Finite13
import Mathlib

open WOWII217FiniteBase WOWII217Closure

example (g : BitVec 78)
    (h : fixedDegreeSequenceUpper (n := 13) g
      [6, 6, 6, 6, 6, 6, 6, 5, 5, 5, 5, 5, 5] = true) :
    (degreeBitsUpper (n := 13) g 0).same (BoolFour.ofNat 6) = true := by
  have h' := h
  norm_num [fixedDegreeSequenceUpper, matchesDegreesFromUpper] at h' ⊢
  aesop
