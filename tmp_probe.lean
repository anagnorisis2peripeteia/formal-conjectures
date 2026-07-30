import WOWII217Finite13ClosureSharedDeg

open WOWII217Finite13ClosureSharedDeg WOWII217FiniteBase

example (g : BitVec 78)
    (hDeg : fixedDegreeSequenceUpper (n := 13) g [6,6,6,6,6,6,6,5,5,5,5,5,5] = true) :
    degreeUpperNat (n := 13) g 0 = 6 := by
  have h := hDeg
  norm_num [fixedDegreeSequenceUpper, matchesDegreesFromUpper] at h ⊢
  -- try to close
  sorry

