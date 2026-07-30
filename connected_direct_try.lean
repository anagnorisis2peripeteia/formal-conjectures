import WOWII217Finite13ClosureSharedDeg

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
example :
    ∀ (g : BitVec 78),
      WOWII217Finite13ClosureSharedDeg.hasHighLowEdge13 g = true →
      WOWII217Finite13ClosureSharedDeg.connectedUpper (n := 13) g = true := by
  intro g h
  native_decide
