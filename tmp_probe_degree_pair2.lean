import WOWII217Closure13Fast
import WOWII217Closure
import WOWII217FiniteBase

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in

theorem test_degreePairEquiv (g : BitVec 78) (u v : Fin 13) :
    WOWII217Closure13Fast.degreePairAtLeast12Upper13 g u.1 v.1 =
      (12 ≤ WOWII217Closure.degreeUpperNat (n := 13) g u.1 +
        WOWII217Closure.degreeUpperNat (n := 13) g v.1) := by
  fin_cases u <;> fin_cases v <;> simp [WOWII217Closure13Fast.degreePairAtLeast12Upper13,
    WOWII217Closure13Fast.degreePairBits13, WOWII217Closure.degreeUpperNat]
