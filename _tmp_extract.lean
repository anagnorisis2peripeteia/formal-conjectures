import WOWII217Finite13ClosureSharedDeg

open WOWII217FiniteBase

example (g : BitVec 78)
    (h : fixedDegreeSequenceUpper (n := 13) g
      [6,6,6,6,6,6,6,5,5,5,5,5,5] = true) :
    (degreeBitsUpper (n := 13) g 0).same (BoolFour.ofNat 6) = true := by
  norm_num [WOWII217FiniteBase.fixedDegreeSequenceUpper, WOWII217FiniteBase.matchesDegreesFromUpper] at h ⊢
  aesop
