import WOWII217Closure13Fast
import WOWII217Closure
import WOWII217Finite13ClosureSharedDeg
import WOWII217ClosureSemantics

open WOWII217FiniteBase
open WOWII217Closure13Fast
open WOWII217Closure

/-- local 5-bit value --/
def boolFiveValue (x : BoolFive) : Nat :=
  (if x.b0 then 1 else 0) +
  2 * (if x.b1 then 1 else 0) +
  4 * (if x.b2 then 1 else 0) +
  8 * (if x.b3 then 1 else 0) +
  16 * (if x.b4 then 1 else 0)

theorem boolFiveValue_increment_of_lt_thirty_one (x : BoolFive) (b : Bool)
    (hx : boolFiveValue x < 31) :
    boolFiveValue (x.increment b) = boolFiveValue x + if b then 1 else 0 := by
  rcases x with ⟨b0, b1, b2, b3, b4⟩
  fin_cases b0 <;> fin_cases b1 <;> fin_cases b2 <;> fin_cases b3 <;> fin_cases b4 <;>
    fin_cases b <;> simp [boolFiveValue, BoolFive.increment] at hx ⊢

theorem boolFiveValue_foldl_increment {α : Type*} (f : α → Bool) :
    ∀ (xs : List α) (initial : BoolFive),
      boolFiveValue initial + xs.length < 31 →
      boolFiveValue (xs.foldl (fun bits x => bits.increment (f x)) initial) =
        xs.foldl (fun count x => count + if f x then 1 else 0)
          (boolFiveValue initial) := by
  intro xs
  induction xs with
  | nil =>
      intro initial h
      simp [List.foldl]
  | cons x xs ih =>
      intro initial bound
      simp only [List.foldl_cons]
      simp only [List.length_cons] at bound
      have hlt : boolFiveValue initial < 31 := by omega
      have inc := boolFiveValue_increment_of_lt_thirty_one initial (f x) hlt
      have bitBound : (if f x then 1 else 0) ≤ 1 := by split <;> simp
      have nextBound : boolFiveValue (initial.increment (f x)) + xs.length < 31 := by
        rw [inc]
        omega
      simp [inc, ih _ nextBound]

theorem boolFiveValue_degreePairBits13_eq_degreeUpperNat (g : BitVec 78) (u v : Nat) :
    boolFiveValue (degreePairBits13 (n := 13) g u v) =
      degreeUpperNat (n := 13) g u + degreeUpperNat (n := 13) g v := by
  unfold degreePairBits13
  have hU := boolFiveValue_foldl_increment
    (f := fun w => adjUpper (n := 13) g u w)
    (List.range 13) BoolFive.zero (by simp [boolFiveValue])
  have hV := boolFiveValue_foldl_increment
    (f := fun w => adjUpper (n := 13) g v w)
    (List.range 13) (List.range 13).foldl
      (fun bits w => bits.increment (adjUpper (n := 13) g u w)) BoolFive.zero
      (by
        have hU' := hU
        -- specialize hU later
        sorry)
  sorry

