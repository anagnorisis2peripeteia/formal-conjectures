import WOWII217Finite13ClosureSharedDeg
import Counter13

open WOWII217Finite13ClosureSharedDeg WOWII217Finite13

example : ¬ (
    ∀ (g1 g2 g3 g4 : BitVec 78) (d d1 d2 d3 : BitVec 52),
      hasHighLowEdge13 Counter13.g = true →
      fixedDegreeSequenceUpper (n := 13) Counter13.g
        [6, 6, 6, 6, 6, 6, 6, 5, 5, 5, 5, 5, 5] = true →
      degreeTableConsistent13 Counter13.g d = true →
      pathClosureParallelRel13 Counter13.g g1 d = true →
      degreeTableConsistent13 g1 d1 = true →
      pathClosureParallelRel13 g1 g2 d1 = true →
      degreeTableConsistent13 g2 d2 = true →
      pathClosureParallelRel13 g2 g3 d2 = true →
      degreeTableConsistent13 g3 d3 = true →
      pathClosureParallelRel13 g3 g4 d3 = true →
      completeUpper (n := 13) g4 = true) := by
  intro h
  let d0 : BitVec 52 := degreeTableOfUpper13 Counter13.g
  let g1 : BitVec 78 := Counter13.g
  let g2 : BitVec 78 := Counter13.g
  let g3 : BitVec 78 := Counter13.g
  let g4 : BitVec 78 := Counter13.g
  let d1 : BitVec 52 := degreeTableOfUpper13 g1
  let d2 : BitVec 52 := degreeTableOfUpper13 g2
  let d3 : BitVec 52 := degreeTableOfUpper13 g3
  have hHigh : hasHighLowEdge13 Counter13.g = true := by native_decide
  have hDeg : fixedDegreeSequenceUpper (n := 13) Counter13.g
      [6, 6, 6, 6, 6, 6, 6, 5, 5, 5, 5, 5, 5] = true := by native_decide
  have hCons : degreeTableConsistent13 Counter13.g d0 = true := by native_decide
  have hRel : pathClosureParallelRel13 Counter13.g g1 d0 = true := by
    native_decide
  have h1 : degreeTableConsistent13 g1 d1 = true := by native_decide
  have h2 : pathClosureParallelRel13 g1 g2 d1 = true := by native_decide
  have h3 : degreeTableConsistent13 g2 d2 = true := by native_decide
  have h4 : pathClosureParallelRel13 g2 g3 d2 = true := by native_decide
  have h5 : degreeTableConsistent13 g3 d3 = true := by native_decide
  have h6 : pathClosureParallelRel13 g3 g4 d3 = true := by native_decide
  have hComp : completeUpper (n := 13) g4 = true :=
    h g1 g2 g3 g4 d0 d1 d2 d3 hHigh hDeg hCons hRel h1 h2 h3 h4 h5 h6
  have hConn : connectedUpper (n := 13) Counter13.g = true := by
    simpa [g4] using (completeUpper_implies_connectedUpper (n := 13) (g := g4) hComp)
  have hFalse : connectedUpper (n := 13) Counter13.g = false := by native_decide
  simpa [hConn] using hFalse
