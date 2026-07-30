import WOWII217Finite13ClosureSharedDeg
import WOWII217Finite13
open WOWII217Finite13ClosureSharedDeg WOWII217Finite13

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
private theorem test_canon :
    ∀ (g : BitVec 78),
      hasHighLowEdge13 g = true →
      WOWII217FiniteBase.fixedDegreeSequenceUpper (n := 13) g
        [6, 6, 6, 6, 6, 6, 6, 5, 5, 5, 5, 5, 5] = true →
      canonicalPermutationBlocksPattern13 g 0 = true := by
  intro g hHigh hDeg
  native_decide
