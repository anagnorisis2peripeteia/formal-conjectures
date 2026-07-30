import WOWII217Closure13Fast
import WOWII217FiniteBase

open WOWII217Closure13Fast WOWII217FiniteBase

def boolFiveValueR (x : BoolFive) : Nat :=
  (if x.b0 then 1 else 0) +
    2 * (if x.b1 then 1 else 0) +
    4 * (if x.b2 then 1 else 0) +
    8 * (if x.b3 then 1 else 0) +
    16 * (if x.b4 then 1 else 0)

lemma boolFiveValueR_increment_of_lt_thirtyone (x : BoolFive) (b : Bool)
    (hx : boolFiveValueR x < 31) :
    boolFiveValueR (x.increment b) = boolFiveValueR x + if b then 1 else 0 := by
  rcases x with ⟨x0, x1, x2, x3, x4⟩
  fin_cases x0 <;> fin_cases x1 <;> fin_cases x2 <;> fin_cases x3 <;> fin_cases x4 <;>
    fin_cases b <;> simp [BoolFive.increment, boolFiveValueR] at hx ⊢

lemma boolFiveValueR_foldl_increment {α : Type*} (f : α → Bool) :
    ∀ (xs : List α) (initial : BoolFive),
      boolFiveValueR initial + xs.length ≤ 31 →
      boolFiveValueR (xs.foldl (fun bits x => bits.increment (f x)) initial) =
        xs.foldl (fun count x => count + if f x then 1 else 0) (boolFiveValueR initial) := by
  intro xs
  induction xs with
  | nil =>
      intro initial bound
      simp
  | cons x xs ih =>
      intro initial bound
      have hbound : boolFiveValueR initial + (xs.length + 1) ≤ 31 := by
        simpa [List.length_cons, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using bound
      by_cases hfx : f x = true
      · have hinit : boolFiveValueR initial < 31 := by
          omega
        have hinc : boolFiveValueR (initial.increment true) = boolFiveValueR initial + 1 := by
          exact boolFiveValueR_increment_of_lt_thirtyone initial true hinit
        have htail : boolFiveValueR (initial.increment true) + xs.length ≤ 31 := by
          rw [hinc]
          simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hbound
        have ih' := ih (initial.increment true) htail
        simp [List.foldl_cons, hfx, ih', hinc]
      · have hzero : initial.increment false = initial := by
          simp [BoolFive.increment]
        have htail : boolFiveValueR initial + xs.length ≤ 31 := by
          omega
        have ih' := ih initial htail
        simp [List.foldl_cons, hfx, hzero, ih']

#check boolFiveValueR_foldl_increment
