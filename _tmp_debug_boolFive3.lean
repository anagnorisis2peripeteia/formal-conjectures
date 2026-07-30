import WOWII217Closure13Fast
import WOWII217FiniteBase

open WOWII217FiniteBase WOWII217Closure13Fast

def boolFiveValue (x : BoolFive) : Nat :=
  (if x.b0 then 1 else 0) +
    2 * (if x.b1 then 1 else 0) +
    4 * (if x.b2 then 1 else 0) +
    8 * (if x.b3 then 1 else 0) +
    16 * (if x.b4 then 1 else 0)

theorem boolFiveValue_increment (x : BoolFive) (b : Bool) (hx : boolFiveValue x < 31) :
    boolFiveValue (x.increment b) =
      boolFiveValue x + if b then 1 else 0 := by
  rcases x with ⟨x0, x1, x2, x3, x4⟩
  fin_cases x0 <;> fin_cases x1 <;> fin_cases x2 <;> fin_cases x3 <;> fin_cases x4 <;>
    fin_cases b <;> simp [boolFiveValue, BoolFive.increment] at hx ⊢

theorem test {α : Type*} (f : α → Bool) :
    ∀ (xs : List α) (initial : BoolFive),
      boolFiveValue initial + xs.length < 32 →
      boolFiveValue (xs.foldl (fun bits x => bits.increment (f x)) initial) =
        boolFiveValue initial +
          (xs.foldl (fun count x => count + if f x then 1 else 0) 0) := by
  intro xs
  induction xs with
  | nil => simp
  | cons x xs ih =>
      intro initial bound
      simp [List.foldl_cons]
      have hb : boolFiveValue initial + xs.length + 1 < 32 := by
        simpa [List.length_cons, Nat.add_assoc] using bound
      have initialLt : boolFiveValue initial < 31 := by omega
      have incrementValue :=
        boolFiveValue_increment initial (f x) initialLt
      have ih' := ih (initial.increment (f x))
      have hfx : f x = true ∨ f x = false := by
        exact by cases h : f x <;> aesop
      cases h : f x <;>
      simp [h] at incrementValue ⊢
      · have nextBound :
          boolFiveValue initial + List.length xs < 32 := by
            omega
        have ihTail := ih' nextBound
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ihTail
      · have nextBound :
          boolFiveValue initial + 1 + List.length xs < 32 := by
            omega
        have ihTail := ih' nextBound
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ihTail
