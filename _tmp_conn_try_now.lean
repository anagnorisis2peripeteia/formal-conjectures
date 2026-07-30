import WOWII217Finite13

open WOWII217FiniteBase WOWII217Finite13

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in

def hasHighLowEdge13 (g : BitVec 78) : Bool :=
  (List.range 7).any fun u =>
    (List.range 6).any fun offset => adjUpper (n := 13) g u (offset + 7)

example :
    ∀ (g : BitVec 78),
      hasHighLowEdge13 g = true →
      fixedDegreeSequenceUpper (n := 13) g
        [6, 6, 6, 6, 6, 6, 6, 5, 5, 5, 5, 5, 5] = true →
      connectedUpper (n := 13) g = true := by
  native_decide
