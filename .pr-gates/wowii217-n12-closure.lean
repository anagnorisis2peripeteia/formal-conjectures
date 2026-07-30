import WOWII217Closure
import WOWII217Encoding12

namespace WOWII217Finite12Closure

open WOWII217FiniteBase WOWII217Closure

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000000

-- Check if 12x[5, 5, 5, 5, 5, 5, 6, 6, 6, 6, 6, 6] closes in 1 round!
example (g : BitVec 66) :
    (fixedDegreeSequenceUpper (n := 12) g
      [6, 6, 6, 6, 6, 6, 5, 5, 5, 5, 5, 5] = true) →
    (completeUpper (n := 12) (pathClosureParallelRounds 1 g) = true) := by
  intro h
  revert h g
  bv_decide

end WOWII217Finite12Closure
