import WOWII217FiniteBase
import WOWII217Closure

namespace WOWII217FiniteSmallExceptions

open WOWII217FiniteBase WOWII217Closure

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
theorem connected_degreeSequence_44444422_closure_chain :
    ∀ g g1 g2 g3 g4 : BitVec 28,
      connectedUpper (n := 8) g = true →
      fixedDegreeSequenceUpper (n := 8) g
        [4, 4, 4, 4, 4, 4, 2, 2] = true →
      (g1 == pathClosureParallelRound (n := 8) g) = true →
      (g2 == pathClosureParallelRound (n := 8) g1) = true →
      (g3 == pathClosureParallelRound (n := 8) g2) = true →
      (g4 == pathClosureParallelRound (n := 8) g3) = true →
      completeUpper (n := 8) g4 = true := by
  simp (config := { maxSteps := 1000000000 }) only
    [completeUpper, pathClosureParallelRound,
      pathClosureParallelMask, degreeUpperNat, degreeUpperBv5, BitVec.zero,
      upperPairs, upperIndex,
      edgeCount, fixedDegreeSequenceUpper, matchesDegreesFromUpper,
      degreeBitsUpper, BoolFour.increment, BoolFour.same, BoolFour.ofNat,
      connectedUpper, reachableFromZeroUpper,
      adjUpper, setBit, bitMask, maskHas,
      List.range, List.range.loop, List.foldl, List.all, List.any,
      List.flatMap, List.flatten, List.map, List.append,
      List.length_cons, List.length_nil, beq_iff_eq, Bool.or_eq_true,
      decide_eq_true_eq, ite_self]
  bv_decide (maxSteps := 1000000000) (timeout := 600)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
theorem connected_degreeSequence_44444422_closes :
    ∀ g : BitVec 28,
      connectedUpper (n := 8) g = true →
      fixedDegreeSequenceUpper (n := 8) g
        [4, 4, 4, 4, 4, 4, 2, 2] = true →
      completeUpper (n := 8) (pathClosureParallelRounds (n := 8) 4 g) = true := by
  intro g connected degrees
  let g1 := pathClosureParallelRound (n := 8) g
  let g2 := pathClosureParallelRound (n := 8) g1
  let g3 := pathClosureParallelRound (n := 8) g2
  let g4 := pathClosureParallelRound (n := 8) g3
  have closed := connected_degreeSequence_44444422_closure_chain g g1 g2 g3 g4 connected degrees
    (by simp [g1]) (by simp [g2]) (by simp [g3]) (by simp [g4])
  simpa [pathClosureParallelRounds, g1, g2, g3, g4] using closed

end WOWII217FiniteSmallExceptions
