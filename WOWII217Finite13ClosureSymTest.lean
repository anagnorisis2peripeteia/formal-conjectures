import WOWII217Closure
import WOWII217Finite13

namespace WOWII217Finite13ClosureSymTest

open WOWII217FiniteBase WOWII217Closure WOWII217Finite13

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
theorem connected_degreeSequence_6666666555555_closes_sym_r0 :
    ∀ (g g1 g2 g3 g4 : BitVec 78),
      connectedUpper (n := 13) g = true →
      fixedDegreeSequenceUpper (n := 13) g
        [6, 6, 6, 6, 6, 6, 6, 5, 5, 5, 5, 5, 5] = true →
      canonicalPermutationBlocksPattern13 g 0 = true →
      (g1 == pathClosureParallelRound (n := 13) g) = true →
      (g2 == pathClosureParallelRound (n := 13) g1) = true →
      (g3 == pathClosureParallelRound (n := 13) g2) = true →
      (g4 == pathClosureParallelRound (n := 13) g3) = true →
      completeUpper (n := 13) g4 = true := by
  simp (config := { maxSteps := 1000000000 }) only
    [completeUpper, pathClosureParallelRound,
      pathClosureParallelMask, degreeUpperNat,
      upperPairs, upperIndex,
      edgeCount, fixedDegreeSequenceUpper, matchesDegreesFromUpper,
      degreeBitsUpper, BoolFour.increment, BoolFour.same, BoolFour.ofNat,
      connectedUpper, reachableFromZeroUpper,
      canonicalPermutationBlocksPattern13, canonicalPermutationBlock13,
      blockOrderSignature13, blockOrderedVertex13, bitListLexLe13,
      zeroDegreeBlocksPattern13,
      adjUpper, setBit, bitMask, maskHas,
      List.range, List.range.loop, List.foldl, List.all, List.any,
      List.flatMap, List.flatten, List.map, List.append,
      List.length_cons, List.length_nil, List.getD]
  bv_decide (maxSteps := 1000000000) (timeout := 1800)

end WOWII217Finite13ClosureSymTest
