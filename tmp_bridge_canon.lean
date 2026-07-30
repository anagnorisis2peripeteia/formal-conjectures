import WOWII217Finite13ClosureSharedDeg

open WOWII217Finite13ClosureSharedDeg

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in

private theorem test_canon_bridge :
    ∀ g : BitVec 78,
      hasHighLowEdge13 g = true →
      WOWII217FiniteBase.fixedDegreeSequenceUpper (n := 13) g
        [6, 6, 6, 6, 6, 6, 6, 5, 5, 5, 5, 5, 5] = true →
      canonicalPermutationBlocksPattern13 g 0 = true := by
  intro g hHigh hDeg
  simp (config := { maxSteps := 1000000000 }) only [hasHighLowEdge13, fixedDegreeSequenceUpper,
    matchesDegreesFromUpper, degreeBitsUpper, BoolFour.increment,
    BoolFour.same, BoolFour.ofNat,
    canonicalPermutationBlocksPattern13, canonicalPermutationBlock13,
    blockOrderSignature13, blockOrderedVertex13, bitListLexLe13,
    zeroDegreeBlocksPattern13, adjUpper, setBit, bitMask, maskHas,
    List.range, List.range.loop, List.foldl, List.all, List.any, List.map,
    List.append, List.getD]
  native_decide
