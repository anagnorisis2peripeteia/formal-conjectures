import WOWII217Closure

/-!
The sole order-13 degree sequence not discharged by the degree-only Chvatal
criterion is nevertheless closed by the graph-dependent path closure.
-/

namespace WOWII217Finite13Closure

open WOWII217FiniteBase WOWII217Closure

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
theorem connected_degreeSequence_6666666555555_closes :
    ∀ g : BitVec 78,
      connectedUpper (n := 13) g = true →
      fixedDegreeSequenceUpper (n := 13) g
        [6, 6, 6, 6, 6, 6, 6, 5, 5, 5, 5, 5, 5] = true →
      completeUpper (n := 13) (pathClosureParallelRounds (n := 13) 4 g) = true := by
  simp (config := { maxSteps := 1000000000 }) only
    [completeUpper, pathClosureParallelRounds, pathClosureParallelRound,
      pathClosureParallelMask, degreeUpperNat,
      upperPairs, upperIndex,
      edgeCount, fixedDegreeSequenceUpper, matchesDegreesFromUpper,
      degreeBitsUpper, BoolFour.increment, BoolFour.same, BoolFour.ofNat,
      connectedUpper, reachableFromZeroUpper,
      adjUpper, setBit, bitMask, maskHas,
      List.range, List.range.loop, List.foldl, List.all, List.any,
      List.flatMap, List.flatten, List.map, List.append,
      List.length_cons, List.length_nil]
  bv_decide (maxSteps := 1000000000) (timeout := 600)

end WOWII217Finite13Closure
