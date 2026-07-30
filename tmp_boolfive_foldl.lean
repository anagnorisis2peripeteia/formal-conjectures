import WOWII217Closure13Fast
import WOWII217FiniteBase

open WOWII217Closure13Fast
open WOWII217FiniteBase

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

theorem boolFiveValue_foldl_increment
    {α : Type*} (f : α → Bool) (xs : List α) (initial : BoolFive)
    (hbound : boolFiveValue initial + xs.length < 31) :
    boolFiveValue (xs.foldl (fun bits x => bits.increment (f x)) initial) =
      boolFiveValue initial + (xs.foldl (fun count x => count + if f x then 1 else 0) 0) := by
  induction xs generalizing initial with
  | nil =>
      simp at hbound
      simp [hbound]
  | cons x xs ih =>
      have hhead : boolFiveValue initial + (xs.length + 1) < 31 := by
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hbound
      have hzero : boolFiveValue initial < 31 := by omega
      by_cases h : f x
      · have hnext : boolFiveValue (BoolFive.increment initial true) + xs.length < 31 := by
          rw [boolFiveValue_increment_of_lt_thirtyOne initial true hzero]
          omega
        have hrec := ih (initial.increment true) hnext
        rw [List.foldl_cons, h]
        rw [boolFiveValue_increment_of_lt_thirtyOne initial true hzero]
        rw [hrec]
        simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      · have hnext : boolFiveValue (BoolFive.increment initial false) + xs.length < 31 := by
          rw [boolFiveValue_increment_of_lt_thirtyOne initial false hzero]
          simpa [h, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hhead
        have hrec := ih (initial.increment false) hnext
        rw [List.foldl_cons, h]
        rw [boolFiveValue_increment_of_lt_thirtyOne initial false hzero]
        rw [hrec]
        simp
