import Mathlib
import WOWII217Closure13Fast

open WOWII217Closure13Fast

def boolFiveValue (x : BoolFive) : Nat :=
  (if x.b0 then 1 else 0) +
    2 * (if x.b1 then 1 else 0) +
    4 * (if x.b2 then 1 else 0) +
    8 * (if x.b3 then 1 else 0) +
    16 * (if x.b4 then 1 else 0)

theorem test (x : BoolFive) (b : Bool) :
    boolFiveValue (x.increment b) = boolFiveValue x + (if b then 1 else 0) := by
  rcases x with ⟨x0,x1,x2,x3,x4⟩
  fin_cases x0 <;> fin_cases x1 <;> fin_cases x2 <;> fin_cases x3 <;> fin_cases x4 <;>
    fin_cases b <;> simp [boolFiveValue, BoolFive.increment]
