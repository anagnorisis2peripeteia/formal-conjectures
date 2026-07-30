import WOWII217Finite13ClosureRelSymHighLowSharedDeg

namespace Tmp

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
theorem tmp_try :
    ∀ (g g1 g2 g3 g4 : BitVec 78) (d d1 d2 d3 : BitVec 52),
      WOWII217Finite13ClosureSharedDeg.hasHighLowEdge13 g = true →
      WOWII217FiniteBase.fixedDegreeSequenceUpper (n := 13) g
        [6, 6, 6, 6, 6, 6, 6, 5, 5, 5, 5, 5, 5] = true →
      WOWII217Finite13.canonicalPermutationBlocksPattern13 g 0 = true →
      WOWII217Finite13ClosureSharedDeg.degreeTableConsistent13 g d = true →
      WOWII217Finite13ClosureSharedDeg.pathClosureParallelRel13 g g1 d = true →
      WOWII217Finite13ClosureSharedDeg.degreeTableConsistent13 g1 d1 = true →
      WOWII217Finite13ClosureSharedDeg.pathClosureParallelRel13 g1 g2 d1 = true →
      WOWII217Finite13ClosureSharedDeg.degreeTableConsistent13 g2 d2 = true →
      WOWII217Finite13ClosureSharedDeg.pathClosureParallelRel13 g2 g3 d2 = true →
      WOWII217Finite13ClosureSharedDeg.degreeTableConsistent13 g3 d3 = true →
      WOWII217Finite13ClosureSharedDeg.pathClosureParallelRel13 g3 g4 d3 = true →
      WOWII217FiniteBase.completeUpper (n := 13) g4 = true := by
  intro g g1 g2 g3 g4 d d1 d2 d3 hHigh hDegree hCanon hCons0 hRel0 hCons1 hRel1 hCons2 hRel2 hRel3
  exact WOWII217Finite13ClosureRelSymHighLowSharedDeg.crossEdge_degreeSequence_6666666555555_relational_closure_sym_shared
      g g1 g2 g3 g4 d d1 d2 d3 hHigh hDegree hCanon hCons0 hRel0 hCons1 hRel1 hCons2 hRel2 hCons3 hRel3
end Tmp
