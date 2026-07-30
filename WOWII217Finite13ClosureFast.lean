import WOWII217Closure13Fast

/-!
Shared-intermediate finite certificate for the order-13 exceptional degree
sequence, using the Boolean-counter closure implementation.
-/

namespace WOWII217Finite13ClosureFast

open WOWII217FiniteBase WOWII217Closure WOWII217Closure13Fast

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
theorem connected_degreeSequence_6666666555555_fast_closure_chain :
    ∀ g g1 g2 g3 g4 : BitVec 78,
      connectedUpper (n := 13) g = true →
      fixedDegreeSequenceUpper (n := 13) g
        [6, 6, 6, 6, 6, 6, 6, 5, 5, 5, 5, 5, 5] = true →
      (g1 == pathClosureParallelRound13 g) = true →
      (g2 == pathClosureParallelRound13 g1) = true →
      (g3 == pathClosureParallelRound13 g2) = true →
      (g4 == pathClosureParallelRound13 g3) = true →
      completeUpper (n := 13) g4 = true := by
  simp (config := { maxSteps := 1000000000 }) only
    [completeUpper, pathClosureParallelRound13, pathClosureParallelMask13,
      degreePairAtLeast12Upper13, degreePairBits13,
      BoolFive.increment, BoolFive.zero, upperPairs, upperIndex,
      edgeCount, fixedDegreeSequenceUpper, matchesDegreesFromUpper,
      degreeBitsUpper, BoolFour.increment, BoolFour.same, BoolFour.ofNat,
      connectedUpper, reachableFromZeroUpper,
      adjUpper, setBit, bitMask, maskHas,
      List.range, List.range.loop, List.foldl, List.all, List.any,
      List.flatMap, List.flatten, List.map, List.append,
      List.length_cons, List.length_nil]
  bv_decide (maxSteps := 1000000000) (timeout := 600)

theorem connected_degreeSequence_6666666555555_closes_fast :
    ∀ g : BitVec 78,
      connectedUpper (n := 13) g = true →
      fixedDegreeSequenceUpper (n := 13) g
        [6, 6, 6, 6, 6, 6, 6, 5, 5, 5, 5, 5, 5] = true →
      completeUpper (n := 13) (pathClosureParallelRounds13 4 g) = true := by
  intro g connected degrees
  let g1 := pathClosureParallelRound13 g
  let g2 := pathClosureParallelRound13 g1
  let g3 := pathClosureParallelRound13 g2
  let g4 := pathClosureParallelRound13 g3
  have closed := connected_degreeSequence_6666666555555_fast_closure_chain
    g g1 g2 g3 g4 connected degrees
      (by simp [g1]) (by simp [g2]) (by simp [g3]) (by simp [g4])
  simpa [pathClosureParallelRounds13, g1, g2, g3, g4] using closed

end WOWII217Finite13ClosureFast
