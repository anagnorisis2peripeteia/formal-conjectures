import WOWII217Finite13
import WOWII217FiniteBase

example (g : BitVec 78)
    (hDeg : WOWII217FiniteBase.fixedDegreeSequenceUpper (n := 13) g
      [6, 6, 6, 6, 6, 6, 6, 5, 5, 5, 5, 5, 5] = true) :
    (WOWII217FiniteBase.degreeBitsUpper (n := 13) g 0).same (WOWII217FiniteBase.BoolFour.ofNat 6) = true := by
  simpa [WOWII217FiniteBase.fixedDegreeSequenceUpper, WOWII217FiniteBase.matchesDegreesFromUpper] using hDeg
