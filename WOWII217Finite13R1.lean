import WOWII217Finite13

/-! Trusted finite certificate for the `r = 1` order-13 canonical class. -/

namespace WOWII217Finite13R1

open WOWII217FiniteBase WOWII217Finite13

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
theorem hasHamiltonianDPState :
    ∀ (g : BitVec 78)
      (d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 : BitVec 8192),
      (connectedUpper (n := 13) g &&
        fixedDegreeSequenceUpper (n := 13) g
          [6, 6, 6, 6, 6, 6, 6, 5, 5, 5, 5, 5, 5] &&
        sequentialDegreeBlocksPattern13 g 1 &&
        hamiltonianDPConsistent13Split g
          d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 &&
        !hamiltonianDPHasFullPath13Split
          d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12) = false := by
  simp (config := { maxSteps := 1000000000 }) only
    [edgeCount, fixedDegreeSequenceUpper, matchesDegreesFromUpper, degreeBitsUpper,
      BoolFour.increment, BoolFour.same, BoolFour.ofNat,
      connectedUpper, reachableFromZeroUpper,
      sequentialDegreeBlocksPattern13, zeroDegreeBlocksPattern13,
      sequentialDegreeBlockSorted13, sequentialDegreeBlockKey13,
      adjacencyRowCodeRange13, degreeBlockKey13, adjacencyCountRange13,
      hamiltonianDPConsistent13Split, hamiltonianDPHasFullPath13Split, dpAt13,
      absentMask, maskHas, adjUpper, setBit, bitMask,
      List.range, List.range.loop, List.foldl, List.all, List.any]
  bv_decide (maxSteps := 1000000000) (timeout := 1800)
    (embeddedConstraintSubst := false)

end WOWII217Finite13R1
