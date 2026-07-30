import WOWII217Finite13ClosureSharedDeg
import WOWII217Finite13ClosureRelSymHighLowSharedDeg

/-!
Heavy shared-degree completeness certificate for the order-13 residual class.
-/

namespace WOWII217Finite13ClosureSharedDeg

open WOWII217FiniteBase WOWII217Closure WOWII217Closure13Fast WOWII217Finite13

private theorem convert_highLow (g : BitVec 78)
    (h : hasHighLowEdge13 g = true) :
    WOWII217Finite13ClosureRelSymHighLowSharedDeg.hasHighLowEdge13 g = true := by
  convert h

private theorem convert_cons (g : BitVec 78) (d : BitVec 52)
    (h : degreeTableConsistent13 g d = true) :
    WOWII217Finite13ClosureRelSymHighLowSharedDeg.degreeTableConsistent13 g d = true := by
  convert h

private theorem convert_rel (g next : BitVec 78) (d : BitVec 52)
    (h : pathClosureParallelRel13 g next d = true) :
    WOWII217Finite13ClosureRelSymHighLowSharedDeg.pathClosureParallelRel13 g next d = true := by
  convert h

theorem crossEdge_degreeSequence_6666666555555_shared_degree_closure :
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
  intro g g1 g2 g3 g4 d d1 d2 d3 hHigh hDegree hCons0 hRel0 hCons1 hRel1 hCons2 hRel2 hCons3 hRel3
  exact
    WOWII217Finite13ClosureRelSymHighLowSharedDeg.crossEdge_degreeSequence_6666666555555_relational_closure_sym_shared
      g g1 g2 g3 g4 d d1 d2 d3
      (convert_highLow g hHigh) hDegree
      (convert_cons g d hCons0) (convert_rel g g1 d hRel0)
      (convert_cons g1 d1 hCons1) (convert_rel g1 g2 d1 hRel1)
      (convert_cons g2 d2 hCons2) (convert_rel g2 g3 d2 hRel2)
      (convert_cons g3 d3 hCons3) (convert_rel g3 g4 d3 hRel3)

end WOWII217Finite13ClosureSharedDeg
