import WOWII217Finite13ClosureRelSymHighLowSharedDeg
import WOWII217Finite13ClosureSharedDeg

namespace Probe

open WOWII217Finite13ClosureSharedDeg WOWII217Finite13ClosureRelSymHighLowSharedDeg WOWII217Finite13

example :
    ∀ (g : BitVec 78),
      WOWII217Finite13ClosureSharedDeg.hasHighLowEdge13 g = true →
      WOWII217FiniteBase.fixedDegreeSequenceUpper (n := 13) g
        [6, 6, 6, 6, 6, 6, 6, 5, 5, 5, 5, 5, 5] = true →
      WOWII217Finite13.canonicalPermutationBlocksPattern13 g 0 = true := by
  intro g hHigh hDeg
  native_decide

end Probe
