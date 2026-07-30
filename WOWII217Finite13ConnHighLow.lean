import WOWII217Closure13Fast
import WOWII217Finite13ClosureRel

/-!
Compact connectivity witness for the labeled residual degree class.
-/

namespace WOWII217Finite13ConnHighLow

open WOWII217FiniteBase WOWII217Closure WOWII217Closure13Fast
open WOWII217Finite13ClosureRel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
set_option debug.skipKernelTC true in
theorem connectedUpper_of_highLow_degreeSequence_6666666555555
    (g : BitVec 78) :
    hasHighLowEdge13 g = true →
    fixedDegreeSequenceUpper (n := 13) g
      [6, 6, 6, 6, 6, 6, 6, 5, 5, 5, 5, 5, 5] = true →
    connectedUpper (n := 13) g = true := by
  simp (config := { maxSteps := 1000000000 }) only
    [hasHighLowEdge13,
      edgeCount, fixedDegreeSequenceUpper, matchesDegreesFromUpper,
      degreeBitsUpper, BoolFour.increment, BoolFour.same, BoolFour.ofNat,
      connectedUpper, reachableFromZeroUpper,
      adjUpper, setBit, bitMask, maskHas,
      List.range, List.range.loop, List.foldl, List.all, List.any,
      List.flatMap, List.flatten,
      List.length_cons, List.length_nil]
  bv_decide (maxSteps := 1000000000) (timeout := 180)

end WOWII217Finite13ConnHighLow
