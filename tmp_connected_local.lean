import WOWII217Finite13ClosureSharedDeg

open WOWII217Finite13ClosureSharedDeg WOWII217FiniteBase

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in

theorem test_local (g : BitVec 78) :
      hasHighLowEdge13 g = true →
      fixedDegreeSequenceUpper (n := 13) g
        [6, 6, 6, 6, 6, 6, 6, 5, 5, 5, 5, 5, 5] = true →
      connectedUpper (n := 13) g = true := by
  intro hHigh hDeg
  native_decide
