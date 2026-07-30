import WOWII217FiniteBase
import WOWII217Closure

namespace WOWII217FiniteSmallExceptions

open WOWII217FiniteBase WOWII217Closure

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
theorem connected_degreeSequence_3311_closes :
    ∀ g : BitVec 6,
      connectedUpper (n := 4) g = true →
      fixedDegreeSequenceUpper (n := 4) g
        [3, 3, 1, 1] = true →
      completeUpper (n := 4) (pathClosureParallelRounds (n := 4) 4 g) = true := by
  decide

end WOWII217FiniteSmallExceptions
