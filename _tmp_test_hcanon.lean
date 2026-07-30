import WOWII217Finite13ClosureSharedDeg
open WOWII217Finite13ClosureSharedDeg

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in

theorem test_hcanon (g : BitVec 78)
    (hHigh : hasHighLowEdge13 g = true)
    (hDeg : WOWII217FiniteBase.fixedDegreeSequenceUpper (n := 13) g
        [6, 6, 6, 6, 6, 6, 6, 5, 5, 5, 5, 5, 5] = true) :
    canonicalPermutationBlocksPattern13 g 0 = true := by
  simp (config := { maxSteps := 1000000000 }) only
    [hasHighLowEdge13, fixedDegreeSequenceUpper, matchesDegreesFromUpper,
      degreeBitsUpper, BoolFour.increment, BoolFour.same, BoolFour.ofNat,
      canonicalPermutationBlocksPattern13, canonicalPermutationBlock13,
      blockOrderSignature13, blockOrderedVertex13, bitListLexLe13,
      zeroDegreeBlocksPattern13, degreeTableAt13, adjUpper, setBit, bitMask,
      maskHas, List.range, List.range.loop, List.flatMap, List.flatten,
      List.map, List.append, List.all, List.any,
      List.length_cons, List.length_nil, List.getD, List.foldl]
  bv_decide (maxSteps := 1000000000) (timeout := 600)
    (embeddedConstraintSubst := false)
