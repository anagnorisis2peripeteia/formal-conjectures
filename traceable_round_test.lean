import WOWII217ClosureCertificateSemantics

open SimpleGraph
open WOWII217ClosureSemantics
open WOWII217FiniteBase WOWII217Closure WOWII217Closure13Fast
open WOWII217Finite13ClosureSharedDeg

namespace Test

-- try one-step graph equivalence for parallel round

theorem graphOfUpper_eq_addEligibleEdges13_of_fast_round (g : BitVec 78) :
    graphOfUpper (n := 13) (pathClosureParallelRound (n := 13) g) =
      addEligibleEdgesFrom (graphOfUpper (n := 13) g) allPairs13
        (graphOfUpper (n := 13) g) := by
  ext x y
  by_cases hxy : x = y
  · subst y
    simp [pathClosureParallelRound]
  · simp [pathClosureParallelRound, adj_addEligibleEdges13_iff, hxy]
    sorry

end Test
