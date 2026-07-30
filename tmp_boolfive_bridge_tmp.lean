import WOWII217Closure13Fast
import WOWII217Finite13

open WOWII217Closure13Fast
open WOWII217FiniteBase
open WOWII217Finite13

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in

/-- Numeric value of five-bit accumulator. -/
def boolFiveValue (x : BoolFive) : Nat :=
  (if x.b0 then 1 else 0) +
  2 * (if x.b1 then 1 else 0) +
  4 * (if x.b2 then 1 else 0) +
  8 * (if x.b3 then 1 else 0) +
  16 * (if x.b4 then 1 else 0)

theorem boolFiveValue_increment_of_lt_thirtyTwo (x : BoolFive) (b : Bool)
    (hx : boolFiveValue x < 32) :
    boolFiveValue (x.increment b) = boolFiveValue x + if b then 1 else 0 := by
  rcases x with ⟨x0, x1, x2, x3, x4⟩
  fin_cases x0 <;> fin_cases x1 <;> fin_cases x2 <;> fin_cases x3 <;> fin_cases x4 <;>
    fin_cases b <;> simp [boolFiveValue, BoolFive.increment] at hx ⊢


theorem boolFiveValue_foldl_increment (f : α → Bool) (xs : List α) (initial : BoolFive)
    (hbound : boolFiveValue initial + xs.length < 32) :
    boolFiveValue (xs.foldl (fun bits x => bits.increment (f x)) initial) =
      boolFiveValue initial + (xs.foldl (fun count x => count + if f x then 1 else 0) 0) := by
  induction xs generalizing initial with
  | nil => simp
  | cons x xs ih =>
      simp only [List.foldl_cons]
      have hhead : boolFiveValue initial < 32 := by
        have : boolFiveValue initial + 1 ≤ boolFiveValue initial + (List.length (x :: xs)) := Nat.le.intro (Nat.succ (Nat.zero_add _)) ?h sorry
      -- avoid
      sorry


theorem boolFiveValue_degreePairBits13_eq (g : BitVec 78) (u v : Nat) :
    boolFiveValue (degreePairBits13 (n := 13) g u v) =
      degreeUpperNat (n := 13) g u + degreeUpperNat (n := 13) g v := by
  simp [degreePairBits13]
  have h1 := boolFiveValue_foldl_increment (f := fun w => adjUpper (n := 13) g v w)
    (List.range 13)
    (List.range 13).foldl (fun count w => count.increment (adjUpper (n := 13) g u w)) BoolFive.zero
    (by decide)
  sorry
