import WOWII217Finite13

open WOWII217Finite13 WOWII217FiniteBase

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
example (g : BitVec 78)
    (hHigh : WOWII217Finite13ClosureSharedDeg.hasHighLowEdge13 g = true)
    (hDeg : WOWII217FiniteBase.fixedDegreeSequenceUpper (n := 13) g
      [6, 6, 6, 6, 6, 6, 6, 5, 5, 5, 5, 5, 5] = true) :
    WOWII217Finite13.canonicalPermutationBlocksPattern13 g 0 = true := by
  sorry
