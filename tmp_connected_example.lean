import WOWII217Finite13ClosureSharedDeg

open WOWII217Finite13ClosureSharedDeg
open WOWII217FiniteBase

example :
    ∀ (g : BitVec 78),
      hasHighLowEdge13 g = true →
      fixedDegreeSequenceUpper (n := 13) g
        [6, 6, 6, 6, 6, 6, 6, 5, 5, 5, 5, 5, 5] = true →
      connectedUpper (n := 13) g = true := by
  intro g hHigh hDeg
  bv_decide
