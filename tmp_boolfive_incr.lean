import WOWII217Closure13Fast
import WOWII217FiniteBase

open WOWII217Closure13Fast
open WOWII217FiniteBase

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in

def boolFiveValue (x : BoolFive) : Nat :=
  (if x.b0 then 1 else 0) +
    2 * (if x.b1 then 1 else 0) +
    4 * (if x.b2 then 1 else 0) +
    8 * (if x.b3 then 1 else 0) +
    16 * (if x.b4 then 1 else 0)

theorem boolFiveValue_increment_of_lt_thirtyOne (x : BoolFive) (b : Bool)
    (hx : boolFiveValue x < 31) :
    boolFiveValue (BoolFive.increment x b) = boolFiveValue x + (if b then 1 else 0) := by
  rcases x with ⟨x0, x1, x2, x3, x4⟩
  fin_cases b <;> fin_cases x0 <;> fin_cases x1 <;> fin_cases x2 <;> fin_cases x3 <;> fin_cases x4 <;>
    simp [boolFiveValue, BoolFive.increment] at hx ⊢
