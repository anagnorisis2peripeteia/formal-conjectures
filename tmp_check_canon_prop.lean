import WOWII217Finite13ClosureSharedDeg

private theorem test_canon :
    ∀ (g : BitVec 78),
      WOWII217Finite13ClosureSharedDeg.hasHighLowEdge13 g = true →
      WOWII217FiniteBase.fixedDegreeSequenceUpper (n := 13) g
        [6, 6, 6, 6, 6, 6, 6, 5, 5, 5, 5, 5, 5] = true →
      WOWII217Finite13.canonicalPermutationBlocksPattern13 g 0 = true := by
  native_decide

#check test_canon
