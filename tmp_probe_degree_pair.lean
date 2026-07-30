import WOWII217Closure13Fast
import WOWII217ClosureSemantics
import WOWII217Finite13

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in

theorem test_degreePairEquiv (g : BitVec 78) (u v : Nat) (hu : u < 13) (hv : v < 13) :
    WOWII217Closure13Fast.degreePairAtLeast12Upper13 (n := (13)) g u v =
      (12 ≤ WOWII217FiniteBase.degreeUpperNat (n := 13) g u + WOWII217FiniteBase.degreeUpperNat (n := 13) g v) := by
  fin_cases u <;> fin_cases v <;> simp [WOWII217Closure13Fast.degreePairAtLeast12Upper13, WOWII217Closure13Fast.degreePairBits13, WOWII217FiniteBase.degreeUpperNat]
