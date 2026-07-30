import WOWII217Closure13Fast
import WOWII217Finite13

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

theorem boolFiveValue_increment (x : BoolFive) (b : Bool) :
    boolFiveValue (BoolFive.increment x b) = boolFiveValue x + (if b then 1 else 0) := by
  rcases x with ⟨x0, x1, x2, x3, x4⟩ <;> fin_cases b <;>
    simp [boolFiveValue, BoolFive.increment, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]


theorem boolFiveValue_foldl_increment (f : α → Bool) (xs : List α) (initial : BoolFive)
    (n : Nat) :
    boolFiveValue (xs.foldl (fun bits x => bits.increment (f x)) initial) =
      boolFiveValue initial + (xs.foldl (fun count x => count + if f x then 1 else 0) 0) := by
  induction xs generalizing initial with
  | nil => simp
  | cons x xs ih =>
      simp [List.foldl_cons, boolFiveValue_increment, ih, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]


theorem boolFiveValue_degreePairBits13_eq (g : BitVec 78) (u v : Nat) :
    boolFiveValue (degreePairBits13 (n := 13) g u v) =
      degreeUpperNat (n := 13) g u + degreeUpperNat (n := 13) g v := by
  simp [degreePairBits13]
  -- split into two folds
  rw [boolFiveValue_foldl_increment (f := fun w => adjUpper (n := 13) g v w) (initial :=
    (List.range 13).foldl (fun count w =>
      count.increment (adjUpper (n := 13) g u w)) BoolFive.zero)]
  · simp [degreeUpperNat, boolFiveValue_foldl_increment (f := fun w => adjUpper (n := 13) g u w)]


theorem degreePairAtLeast12Upper13_eq (g : BitVec 78) (u v : Nat) :
    degreePairAtLeast12Upper13 (n := 13) g u v =
    decide (12 ≤ degreeUpperNat (n := 13) g u + degreeUpperNat (n := 13) g v) := by
  unfold degreePairAtLeast12Upper13 degreePairBits13
  have h : boolFiveValue (degreePairBits13 (n := 13) g u v) =
      degreeUpperNat (n := 13) g u + degreeUpperNat (n := 13) g v :=
    boolFiveValue_degreePairBits13_eq g u v
  rw [h]
  rcases (boolFiveValue (degreePairBits13 (n := 13) g u v)) with ⟨⟩
  
