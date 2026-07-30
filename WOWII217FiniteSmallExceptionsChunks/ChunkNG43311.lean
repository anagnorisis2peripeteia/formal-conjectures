import WOWII217FiniteBase
import WOWII217Closure

namespace WOWII217FiniteSmallExceptions

open WOWII217FiniteBase WOWII217Closure

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
theorem connected_degreeSequence_43311_closes :
    ∀ g : BitVec 10,
      connectedUpper (n := 5) g = true →
      fixedDegreeSequenceUpper (n := 5) g
        [4, 3, 3, 1, 1] = true →
      completeUpper (n := 5) (pathClosureParallelRounds (n := 5) 4 g) = true := by
  decide

end WOWII217FiniteSmallExceptions
