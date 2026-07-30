import WOWII217Finite13ClosureRelSymHighLowSharedDeg

open WOWII217Finite13ClosureRelSymHighLowSharedDeg WOWII217Finite13

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
example :
    ∀ g : BitVec 78,
      hasHighLowEdge13 g = true →
      fixedDegreeSequenceUpper (n := 13) g
        [6, 6, 6, 6, 6, 6, 6, 5, 5, 5, 5, 5, 5] = true →
      canonicalPermutationBlocksPattern13 g 0 = true := by
  native_decide
