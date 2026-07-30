import WOWII217Closure13Fast
import WOWII217Finite13

namespace TmpRelSymTry

open WOWII217FiniteBase WOWII217Closure WOWII217Closure13Fast WOWII217Finite13

def pathClosureParallelRel13 (g next : BitVec 78) : Bool :=
  (upperPairs 13).all fun edge =>
    let u := edge.1
    let v := edge.2
    !(adjUpper (n := 13) next u v ||
      (adjUpper (n := 13) g u v || degreePairAtLeast12Upper13 g u v))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
theorem test :
    ∀ g g1 g2 g3 g4 : BitVec 78,
      connectedUpper (n := 13) g = true →
      fixedDegreeSequenceUpper (n := 13) g
        [6, 6, 6, 6, 6, 6, 6, 5, 5, 5, 5, 5, 5] = true →
      pathClosureParallelRel13 g g1 = true →
      pathClosureParallelRel13 g1 g2 = true →
      pathClosureParallelRel13 g2 g3 = true →
      pathClosureParallelRel13 g3 g4 = true →
      completeUpper (n := 13) g4 = true := by
  simp (config := { maxSteps := 1000000000 }) only
    [pathClosureParallelRel13, completeUpper,
      degreePairAtLeast12Upper13, degreePairBits13,
      BoolFive.increment, BoolFive.zero, upperPairs,
      edgeCount, fixedDegreeSequenceUpper, matchesDegreesFromUpper,
      degreeBitsUpper, BoolFour.increment, BoolFour.same, BoolFour.ofNat,
      connectedUpper, reachableFromZeroUpper,
      adjUpper, setBit, bitMask, maskHas,
      List.range, List.range.loop, List.foldl, List.all, List.any,
      List.flatMap, List.flatten, List.map, List.append,
      List.length_cons, List.length_nil]
  bv_decide (maxSteps := 1000000000) (timeout := 120)

end TmpRelSymTry
