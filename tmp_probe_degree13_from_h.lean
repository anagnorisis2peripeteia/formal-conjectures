import WOWII217Finite13ClosureSharedDeg
import WOWII217ClosureSemantics

namespace Tmp
open WOWII217FiniteBase WOWII217Finite13

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
example (g : BitVec 78)
    (hDeg : fixedDegreeSequenceUpper (n := 13) g
      [6, 6, 6, 6, 6, 6, 6, 5, 5, 5, 5, 5, 5] = true) :
    ∀ i : Fin 13, if (i.1 < 7) then degreeUpperNat (n := 13) g i = 6 else degreeUpperNat (n := 13) g i = 5 := by
  intro i
  fin_cases i <;>
    norm_num [fixedDegreeSequenceUpper, matchesDegreesFromUpper] at hDeg ⊢ <;>
    omega

end Tmp
