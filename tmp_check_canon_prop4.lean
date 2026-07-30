import WOWII217Finite13
import WOWII217Closure

open WOWII217Finite13 WOWII217FiniteBase WOWII217Closure

def localHasHighLowEdge13 (g : BitVec 78) : Bool :=
  (List.range 7).any fun u =>
    (List.range 6).any fun offset => adjUpper (n := 13) g u (offset + 7)

example :
    ∀ (g : BitVec 78),
      localHasHighLowEdge13 g = true →
      fixedDegreeSequenceUpper (n := 13) g
        [6, 6, 6, 6, 6, 6, 6, 5, 5, 5, 5, 5, 5] = true →
      canonicalPermutationBlocksPattern13 g 0 = true := by
  intro g hHigh hDeg
  revert g hHigh hDeg
  native_decide
