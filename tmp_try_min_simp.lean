import WOWII217Finite13ClosureSharedDeg
import WOWII217Finite13

namespace Tmp
open WOWII217Finite13ClosureSharedDeg WOWII217Finite13ClosureRelSymHighLowSharedDeg WOWII217FiniteBase WOWII217Closure13Fast WOWII217Closure

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
theorem test_shared_min_simp :
    ∀ (g g1 g2 g3 g4 : BitVec 78) (d d1 d2 d3 : BitVec 52),
      hasHighLowEdge13 g = true →
      fixedDegreeSequenceUpper (n := 13) g
        [6, 6, 6, 6, 6, 6, 6, 5, 5, 5, 5, 5, 5] = true →
      canonicalPermutationBlocksPattern13 g 0 = true →
      degreeTableConsistent13 g d = true →
      pathClosureParallelRel13 g g1 d = true →
      degreeTableConsistent13 g1 d1 = true →
      pathClosureParallelRel13 g1 g2 d1 = true →
      degreeTableConsistent13 g2 d2 = true →
      pathClosureParallelRel13 g2 g3 d2 = true →
      degreeTableConsistent13 g3 d3 = true →
      pathClosureParallelRel13 g3 g4 d3 = true →
      completeUpper (n := 13) g4 = true := by
  intro g g1 g2 g3 g4 d d1 d2 d3 hHigh hDeg hCanon hC0 hR0 hC1 hR1 hC2 hR2 hC3 hR3
  simp (config := { maxSteps := 1000000 }) only [fixedDegreeSequenceUpper, matchesDegreesFromUpper,
      degreeTableConsistent13, hasHighLowEdge13, canonicalPermutationBlocksPattern13,
      canonicalPermutationBlock13, blockOrderSignature13, blockOrderedVertex13,
      bitListLexLe13, zeroDegreeBlocksPattern13,
      pathClosureParallelRel13, degreePairAtLeast12Upper13, degreePairBits13,
      BoolFive.increment, BoolFive.zero, upperPairs, upperIndex, edgeCount,
      adjUpper, setBit, bitMask, maskHas, connectedUpper, reachableFromZeroUpper,
      BoolFour.increment, BoolFour.same, BoolFour.ofNat, List.all, List.range, List.range.loop,
      List.foldl, List.any, List.flatMap, List.flatten, List.map, List.append,
      List.length_cons, List.length_nil] at hC0 hC1 hC2 hC3 ⊢
  aesop?

end Tmp
