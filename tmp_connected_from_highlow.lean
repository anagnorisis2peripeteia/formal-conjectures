import WOWII217Finite13ClosureRelSymHighLow

open WOWII217Finite13ClosureRelSymHighLow WOWII217FiniteBase WOWII217Finite13

example :
    ∀ (g : BitVec 78),
      hasHighLowEdge13 g = true →
      fixedDegreeSequenceUpper (n := 13) g
        [6, 6, 6, 6, 6, 6, 6, 5, 5, 5, 5, 5, 5] = true →
      connectedUpper (n := 13) g = true := by
  intro g hHigh hDeg
  simp [connectedUpper, reachableFromZeroUpper, hasHighLowEdge13, fixedDegreeSequenceUpper, matchesDegreesFromUpper, degreeBitsUpper]
    at hHigh hDeg ⊢
