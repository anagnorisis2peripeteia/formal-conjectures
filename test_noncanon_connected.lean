import WOWII217Finite13ClosureSharedDeg
import WOWII217Finite13

open WOWII217Finite13ClosureSharedDeg WOWII217Finite13 WOWII217FiniteBase

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
example :
    ∃ (g : BitVec 78),
      connectedUpper (n := 13) g = true ∧
      hasHighLowEdge13 g = true ∧
      fixedDegreeSequenceUpper (n := 13) g
        [6, 6, 6, 6, 6, 6, 6, 5, 5, 5, 5, 5, 5] = true ∧
      canonicalPermutationBlocksPattern13 g 0 = false := by
  native_decide
