import WOWII217Finite13

open WOWII217FiniteBase WOWII217Finite13

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in

def hHighLocal (g : BitVec 78) : Bool :=
  (List.range 7).any fun u =>
    (List.range 6).any fun offset => adjUpper (n := 13) g u (offset + 7)

lemma test_connected_from_highlow_fixed :
    ∀ (g : BitVec 78),
      hHighLocal g = true →
      fixedDegreeSequenceUpper (n := 13) g
        [6, 6, 6, 6, 6, 6, 6, 5, 5, 5, 5, 5, 5] = true →
      connectedUpper (n := 13) g = true := by
  native_decide
