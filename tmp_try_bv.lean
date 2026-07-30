import WOWII217Finite13ClosureSharedDeg

namespace WOWII217Finite13ClosureSharedDeg

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
private theorem test_bv_attempt :
    ∀ (g g1 g2 g3 g4 : BitVec 78) (d d1 d2 d3 : BitVec 52),
      hasHighLowEdge13 g = true →
      fixedDegreeSequenceUpper (n := 13) g
        [6, 6, 6, 6, 6, 6, 6, 5, 5, 5, 5, 5, 5] = true →
      degreeTableConsistent13 g d = true →
      pathClosureParallelRel13 g g1 d = true →
      degreeTableConsistent13 g1 d1 = true →
      pathClosureParallelRel13 g1 g2 d1 = true →
      degreeTableConsistent13 g2 d2 = true →
      pathClosureParallelRel13 g2 g3 d2 = true →
      degreeTableConsistent13 g3 d3 = true →
      pathClosureParallelRel13 g3 g4 d3 = true →
      completeUpper (n := 13) g4 = true := by
  intro g g1 g2 g3 g4 d d1 d2 d3
  intro hHigh hDeg hCons0 hRel0 hCons1 hRel1 hCons2 hRel2 hCons3 hRel3
  simp (config := { maxSteps := 1000000000 }) only
    [hHigh, hDeg, hCons0, hRel0, hCons1, hRel1, hCons2, hRel2, hCons3, hRel3,
      hasHighLowEdge13, degreeTableConsistent13, degreeTableAt13,
      pathClosureParallelRel13, boolFourSumAtLeast12, majority,
      completeUpper, upperPairs, upperIndex, edgeCount, fixedDegreeSequenceUpper,
      matchesDegreesFromUpper, degreeBitsUpper, BoolFour.increment, BoolFour.same,
      BoolFour.ofNat,
      adjUpper, setBit, bitMask, maskHas,
      Bool.and_eq_true, Bool.or_eq_true, List.range, List.range.loop,
      List.foldl, List.all, List.any, List.flatMap, List.flatten, List.map,
      List.append, List.length_cons, List.length_nil, List.getD]
  bv_decide (maxSteps := 1000000000) (timeout := 1800)
    (embeddedConstraintSubst := false)

end WOWII217Finite13ClosureSharedDeg
