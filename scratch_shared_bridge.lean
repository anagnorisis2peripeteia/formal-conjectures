import WOWII217Finite13ClosureSharedDeg

open WOWII217Finite13ClosureSharedDeg WOWII217Finite13 WOWII217Closure13Fast WOWII217FiniteBase WOWII217Closure

theorem test_boolFive_ge12_iff (x : BoolFive) : x.b4 || (x.b3 && x.b2) = true ↔ 12 ≤
    (if x.b0 then 1 else 0) +
      2 * (if x.b1 then 1 else 0) +
      4 * (if x.b2 then 1 else 0) +
      8 * (if x.b3 then 1 else 0) +
      16 * (if x.b4 then 1 else 0) := by
  rcases x with ⟨b0,b1,b2,b3,b4⟩
  fin_cases b0 <;> fin_cases b1 <;> fin_cases b2 <;> fin_cases b3 <;> fin_cases b4 <;> decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
theorem test_bridge (g : BitVec 78) (u v : Nat) :
    degreePairAtLeast12Upper13 (n:=13) g u v =
      decide (12 ≤ degreeUpperNat (n := 13) g u + degreeUpperNat (n := 13) g v) := by
  unfold degreePairAtLeast12Upper13
  simp [test_boolFive_ge12_iff]
