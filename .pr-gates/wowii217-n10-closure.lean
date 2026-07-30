import WOWII217Closure
import WOWII217FiniteBase

namespace WOWII217Finite10Closure

open WOWII217FiniteBase WOWII217Closure

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000

example (g : BitVec 45) :
    (fixedDegreeSequenceUpper (n := 10) g
      [4, 4, 4, 4, 4, 4, 4, 4, 4, 4] = true) →
    (completeUpper (n := 10) (pathClosureParallelRounds 1 g) = true) := by
  intro h
  revert h g
  simp (config := { maxSteps := 1000000000 }) only
    [edgeCount, fixedDegreeSequenceUpper, matchesDegreesFromUpper, degreeBitsUpper,
      BoolFour.increment, BoolFour.same, BoolFour.ofNat,
      completeUpper, pathClosureParallelRounds, pathClosureParallelRel,
      pathClosureParallelRound, adj_addEligibleEdges, eligibleEdgesMask,
      degreeTableOfUpper, degreeTableAt, degreeUpperNat,
      boolFourSumAtLeast10, abs,
      absentMask, maskHas, adjUpper, setBit, bitMask,
      List.range, List.range.loop, List.foldl, List.all, List.any]
  bv_decide

end WOWII217Finite10Closure
