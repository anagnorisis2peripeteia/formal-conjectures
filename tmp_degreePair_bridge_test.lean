import WOWII217Closure13Fast
import WOWII217FiniteBase

open WOWII217FiniteBase
open WOWII217Closure13Fast

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in

def boolFiveValue (x : BoolFive) : Nat :=
  (if x.b0 then 1 else 0) +
    2 * (if x.b1 then 1 else 0) +
    4 * (if x.b2 then 1 else 0) +
    8 * (if x.b3 then 1 else 0) +
    16 * (if x.b4 then 1 else 0)

theorem boolFiveValue_increment (x : BoolFive) (b : Bool) :
    boolFiveValue (x.increment b) = boolFiveValue x + (if b then 1 else 0) := by
  rcases x with ⟨x0, x1, x2, x3, x4⟩
  fin_cases b <;>
    fin_cases x0 <;> fin_cases x1 <;> fin_cases x2 <;> fin_cases x3 <;> fin_cases x4 <;>
    simp [boolFiveValue, BoolFive.increment, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]


theorem boolFiveValue_foldl_increment (f : α → Bool) (xs : List α) (initial : BoolFive) :
    boolFiveValue (xs.foldl (fun bits x => bits.increment (f x)) initial) =
      boolFiveValue initial + (xs.foldl (fun count x => count + if f x then 1 else 0) 0) := by
  induction xs generalizing initial with
  | nil => simp
  | cons x xs ih =>
      simp [List.foldl_cons]
      have ih' := ih (initial.increment (f x))
      rw [ih']
      rw [boolFiveValue_increment]
      omega


theorem boolFiveValue_degreePairBits13_eq (g : BitVec 78) (u v : Nat) :
    boolFiveValue (degreePairBits13 g u v) =
      degreeUpperNat (n := 13) g u + degreeUpperNat (n := 13) g v := by
  simp [degreePairBits13]
  rw [boolFiveValue_foldl_increment (f := fun w => adjUpper (n := 13) g v w),
    boolFiveValue_foldl_increment (f := fun w => adjUpper (n := 13) g u w)]
  simp [degreeUpperNat, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]


theorem boolFiveAtLeast12_iff (x : BoolFive) :
    (x.b4 || (x.b3 && x.b2)) = true ↔ 12 ≤ boolFiveValue x := by
  rcases x with ⟨x0, x1, x2, x3, x4⟩
  fin_cases x0 <;> fin_cases x1 <;> fin_cases x2 <;> fin_cases x3 <;> fin_cases x4 <;>
    decide


theorem degreePairAtLeast12Upper13_eq (g : BitVec 78) (u v : Nat) :
    degreePairAtLeast12Upper13 g u v =
      decide (12 ≤ degreeUpperNat (n := 13) g u + degreeUpperNat (n := 13) g v) := by
  have hsum :
      boolFiveValue (degreePairBits13 g u v) =
        degreeUpperNat (n := 13) g u + degreeUpperNat (n := 13) g v :=
    boolFiveValue_degreePairBits13_eq g u v
  apply Bool.eq_iff_iff
  constructor
  · intro h
    have h' : 12 ≤ boolFiveValue (degreePairBits13 g u v) := (boolFiveAtLeast12_iff _).1 h
    simpa [hsum] using h'
  · intro h
    have h' : 12 ≤ boolFiveValue (degreePairBits13 g u v) := by
      simpa [hsum] using h
    exact (boolFiveAtLeast12_iff _).2 h'
