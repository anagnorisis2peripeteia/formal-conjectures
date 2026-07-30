import WOWII217Closure13Fast
open WOWII217FiniteBase WOWII217Closure WOWII217Closure13Fast
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
set_option debug.skipKernelTC true in
theorem degreePairAtLeast12Upper13_eq_decide (g : BitVec 78) (u v : Fin 13) :
    degreePairAtLeast12Upper13 g u.val v.val =
      decide (12 ≤ degreeUpperNat (n := 13) g u.val + degreeUpperNat (n := 13) g v.val) := by
  simp (config := { maxSteps := 1000000000 }) only
    [degreePairAtLeast12Upper13, degreePairBits13, degreeUpperNat,
      BoolFive.increment, BoolFive.zero,
      adjUpper, List.range, List.range.loop, List.foldl]
  bv_decide (maxSteps := 1000000000) (timeout := 120)
