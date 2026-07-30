import WOWII217Finite13
import WOWII217FiniteBase

open WOWII217Finite13 WOWII217FiniteBase

def hasHighLowEdge13 (g : BitVec 78) : Bool :=
  (List.range 7).any fun u =>
    (List.range 6).any fun offset => adjUpper (n := 13) g u (offset + 7)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
example :
    ∀ (g : BitVec 78),
      hasHighLowEdge13 g = true →
      fixedDegreeSequenceUpper (n := 13) g
        [6, 6, 6, 6, 6, 6, 6, 5, 5, 5, 5, 5, 5] = true →
      canonicalPermutationBlocksPattern13 g 0 = true →
      connectedUpper (n := 13) g = true := by
  intro g hHigh hDeg hCanon
  simp (config := { maxSteps := 1000000000 }) only
    [hasHighLowEdge13, fixedDegreeSequenceUpper, matchesDegreesFromUpper,
      degreeBitsUpper, BoolFour.increment, BoolFour.same, BoolFour.ofNat,
      connectedUpper, reachableFromZeroUpper,
      adjUpper, setBit, bitMask, maskHas,
      List.range, List.range.loop, List.foldl, List.all, List.any,
      List.flatMap, List.flatten, List.map, List.append,
      List.length_cons, List.length_nil]
  bv_decide (maxSteps := 1000000000) (timeout := 120)
    (embeddedConstraintSubst := false)
