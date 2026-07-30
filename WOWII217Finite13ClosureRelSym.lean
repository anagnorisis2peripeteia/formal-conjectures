import WOWII217Closure13Fast
import WOWII217Finite13
import WOWII217Finite13ClosureRel

namespace WOWII217Finite13ClosureRelSym

open WOWII217FiniteBase WOWII217Closure WOWII217Closure13Fast WOWII217Finite13
open WOWII217Finite13ClosureRel

abbrev pathClosureParallelRel13 :=
  WOWII217Finite13ClosureRel.pathClosureParallelRel13

/-- Connected form of the residual certificate, requiring an explicit high/low
edge (the compact connectivity witness used by the bitblasted certificate). -/
theorem connected_degreeSequence_6666666555555_relational_closure_sym :
    ∀ g g1 g2 g3 g4 : BitVec 78,
      hasHighLowEdge13 g = true →
      fixedDegreeSequenceUpper (n := 13) g
        [6, 6, 6, 6, 6, 6, 6, 5, 5, 5, 5, 5, 5] = true →
      canonicalPermutationBlocksPattern13 g 0 = true →
      pathClosureParallelRel13 g g1 = true →
      pathClosureParallelRel13 g1 g2 = true →
      pathClosureParallelRel13 g2 g3 = true →
      pathClosureParallelRel13 g3 g4 = true →
      completeUpper (n := 13) g4 = true := by
  intro g g1 g2 g3 g4 hHigh hDegrees _hCanon hRel0 hRel1 hRel2 hRel3
  exact
    crossEdge_degreeSequence_6666666555555_relational_closure
      g g1 g2 g3 g4 hHigh hDegrees hRel0 hRel1 hRel2 hRel3

end WOWII217Finite13ClosureRelSym
