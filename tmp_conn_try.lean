import WOWII217Finite13
import WOWII217Closure13Fast

open WOWII217FiniteBase WOWII217Closure13Fast WOWII217Finite13

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
  intro g hHigh hDeg
  have hHigh' := hHigh
  have hDeg' := hDeg
  simpa using (by
    simp [hHigh', hDeg'] )
