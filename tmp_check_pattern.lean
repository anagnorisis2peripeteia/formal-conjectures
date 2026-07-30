import WOWII217Finite13ClosureSharedDeg
open WOWII217Finite13ClosureSharedDeg WOWII217FiniteBase

example (g : BitVec 78)
    (hDeg : fixedDegreeSequenceUpper (n := 13) g [6,6,6,6,6,6,6,5,5,5,5,5,5] = true) :
    True := by
  have h := hDeg
  simp [fixedDegreeSequenceUpper] at h
  trivial
