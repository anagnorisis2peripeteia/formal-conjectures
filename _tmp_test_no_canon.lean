import WOWII217Closure13Fast
import WOWII217Finite13
import WOWII217Finite13ClosureSharedDeg

open WOWII217FiniteBase WOWII217Closure WOWII217Closure13Fast WOWII217Finite13
open WOWII217Finite13ClosureSharedDeg

namespace Tmp

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
 theorem test_no_canon :
    ∀ (g g1 g2 g3 g4 : BitVec 78) (d d1 d2 d3 : BitVec 52),
      hasHighLowEdge13 g = true →
      fixedDegreeSequenceUpper (n := 13) g
        [6, 6, 6, 6, 6, 6, 6, 5, 5, 5, 5, 5, 5] = true →
      degreeTableConsistent13 g d = true →
      pathClosureParallelRel13 g g1 d = true →
      degreeTableConsistent13 g1 d1 = true →
      pathClosureParallelRel13 g1 g2 d1 = true →
      degreeTableConsistent13 g2 d2 = true →
      pathClosureParallelRel13 g2 g3 d2 = true →
      degreeTableConsistent13 g3 d3 = true →
      pathClosureParallelRel13 g3 g4 d3 = true →
      completeUpper (n := 13) g4 = true := by
  intro g g1 g2 g3 g4 d d1 d2 d3 hHigh hDeg hCons0 hRel0 hCons1 hRel1 hCons2 hRel2 hCons3 hRel3
  simp [hHigh, hDeg, hCons0, hRel0, hCons1, hRel1, hCons2, hRel2, hCons3, hRel3] at *

end Tmp
