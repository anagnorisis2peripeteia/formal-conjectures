import WOWII217Finite13ClosureSharedDeg

open WOWII217Finite13ClosureSharedDeg WOWII217FiniteBase

example :
    ∀ (g : BitVec 78),
      hasHighLowEdge13 g = true →
      WOWII217FiniteBase.fixedDegreeSequenceUpper (n := 13) g
        [6, 6, 6, 6, 6, 6, 6, 5, 5, 5, 5, 5, 5] = true →
      WOWII217FiniteBase.connectedUpper (n := 13) g = true := by
  intro g hHigh hDeg
  native_decide
