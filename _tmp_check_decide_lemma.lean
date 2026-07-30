import WOWII217Closure13Fast
import WOWII217FiniteBase
import WOWII217Closure

namespace Scratch

open WOWII217Closure13Fast WOWII217FiniteBase WOWII217Closure

/-- Sum represented by BoolFive. -/
def boolFiveValue (x : BoolFive) : Nat :=
  (if x.b0 then 1 else 0) +
    2 * (if x.b1 then 1 else 0) +
    4 * (if x.b2 then 1 else 0) +
    8 * (if x.b3 then 1 else 0) +
    16 * (if x.b4 then 1 else 0)

theorem boolFiveValue_increment_of_lt_thirtyone (x : BoolFive) (b : Bool)
    (hx : boolFiveValue x < 31) :
    boolFiveValue (BoolFive.increment x b) = boolFiveValue x + if b then 1 else 0 := by
  rcases x with ⟨x0, x1, x2, x3, x4⟩
  fin_cases x0 <;> fin_cases x1 <;> fin_cases x2 <;> fin_cases x3 <;> fin_cases x4 <;>
    fin_cases b <;> simp [boolFiveValue, BoolFive.increment] at hx ⊢

theorem boolFiveValue_foldl_increment {α : Type*} (f : α → Bool) :
    ∀ (xs : List α) (initial : BoolFive),
      boolFiveValue initial + xs.length < 32 →
      boolFiveValue (xs.foldl (fun bits x => bits.increment (f x)) initial) =
        xs.foldl (fun count x => count + if f x then 1 else 0)
          (boolFiveValue initial) := by
  intro xs
  induction xs with
  | nil =>
      intro initial bound
      simp at bound
      simp
  | cons x xs ih =>
      intro initial bound
      have hcons : boolFiveValue initial + (if f x then 1 else 0) + xs.length < 32 := by
        simpa [List.length, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using bound
      simp [List.foldl_cons]
      by_cases hx : f x = true
      · have hinitial : boolFiveValue initial < 31 := by omega
        have hnext : boolFiveValue (BoolFive.increment initial true) + xs.length < 32 := by
          rw [boolFiveValue_increment_of_lt_thirtyone initial true hinitial]
          omega
        simp [BoolFive.increment, hx]
        have hnextEq := ih (BoolFive.increment initial true) hnext
        -- rewrite initial state for recursive call
        simpa [hx] using hnextEq
      · have hfalse : boolFiveValue (BoolFive.increment initial false) = boolFiveValue initial := by
          simp [BoolFive.increment]
        have hnext : boolFiveValue (BoolFive.increment initial false) + xs.length < 32 := by
          simpa [hfalse] using hcons
        simp [BoolFive.increment, hx]
        have hnextEq := ih (BoolFive.increment initial false) hnext
        -- replace next initial
        simpa [hfalse, hx, Nat.add_zero] using hnextEq

theorem boolFoldl_add_eq (f : α → Bool) (a : Nat) :
    ∀ xs : List α,
      xs.foldl (fun count x => count + if f x then 1 else 0) a =
        a + xs.foldl (fun count x => count + if f x then 1 else 0) 0 := by
  intro xs
  induction xs with
  | nil => simp
  | cons x xs ih =>
      intro
      simp [ih, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

theorem boolFiveValue_degreePairBits13 (g : BitVec 78) (u : Nat) :
    boolFiveValue ((List.range 13).foldl
      (fun bits w => bits.increment (adjUpper (n := 13) g u w)) BoolFive.zero) =
    degreeUpperNat (n := 13) g u := by
  let f : Nat → Bool := fun w => adjUpper (n := 13) g u w
  have hfold := boolFiveValue_foldl_increment (f := f) (xs := List.range 13)
    BoolFive.zero (by decide : boolFiveValue BoolFive.zero + (List.range 13).length < 32)
  simpa [f, BoolFive.zero, degreeUpperNat, List.length] using hfold

lemma boolFiveAtLeast12_iff (x : BoolFive) :
    (x.b4 || x.b3 && x.b2) = true ↔ 12 ≤ boolFiveValue x := by
  rcases x with ⟨x0, x1, x2, x3, x4⟩
  fin_cases x0 <;> fin_cases x1 <;> fin_cases x2 <;> fin_cases x3 <;> fin_cases x4 <;>
    decide

lemma degreePairAtLeast12Upper13_eq (g : BitVec 78) (u v : Nat) :
    degreePairAtLeast12Upper13 g u v =
      decide (12 ≤ degreeUpperNat (n := 13) g u + degreeUpperNat (n := 13) g v) := by
  have hdeg_u :
      boolFiveValue
          ((List.range 13).foldl
            (fun bits w => bits.increment (adjUpper (n := 13) g u w)) BoolFive.zero) =
          degreeUpperNat (n := 13) g u := by
        simpa using boolFiveValue_degreePairBits13 (g := g) (u := u)
  have hfoldv :
      boolFiveValue
          ((List.range 13).foldl
            (fun bits w => bits.increment (adjUpper (n := 13) g v w))
            ((List.range 13).foldl
              (fun bits w => bits.increment (adjUpper (n := 13) g u w)) BoolFive.zero)) =
          degreeUpperNat (n := 13) g u + degreeUpperNat (n := 13) g v := by
    let bitsu : BoolFive :=
      (List.range 13).foldl (fun bits w => bits.increment (adjUpper (n := 13) g u w))
        BoolFive.zero
    have hbound : boolFiveValue bitsu + (List.range 13).length < 32 := by
      have hdeg : boolFiveValue bitsu = degreeUpperNat (n := 13) g u := by
        simpa [bitsu] using hdeg_u
      have hdeg_bound : degreeUpperNat (n := 13) g u ≤ 13 := by
        unfold degreeUpperNat
        omega
      rw [hdeg]
      omega
    have hv := boolFiveValue_foldl_increment
      (f := fun w => adjUpper (n := 13) g v w) (xs := List.range 13) bitsu hbound
    -- fold result vs nat fold
    have hsumv :
      (List.range 13).foldl (fun count x => count + if adjUpper (n := 13) g v x then 1 else 0) 
        (boolFiveValue bitsu) = degreeUpperNat (n := 13) g v + boolFiveValue bitsu := by
      have haux := boolFoldl_add_eq (f := fun w => adjUpper (n := 13) g v w) 0 (List.range 13)
      have hdegv : degreeUpperNat (n := 13) g v = (List.range 13).foldl (fun count x =>
        count + if adjUpper (n := 13) g v x then 1 else 0) 0 := by
        simpa [degreeUpperNat, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      simp [haux, hdegv, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
    -- final
    calc
      boolFiveValue (degreePairBits13 g u v) =
          (List.range 13).foldl (fun count x => count + if adjUpper (n := 13) g v x then 1 else 0)
            (boolFiveValue ((List.range 13).foldl
              (fun bits w => bits.increment (adjUpper (n := 13) g u w)) BoolFive.zero)) := by
          simpa [degreePairBits13] using hv
      _ = degreeUpperNat (n := 13) g u + degreeUpperNat (n := 13) g v := by
          simpa [hdeg_u, hsumv, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
  have hth :
      (degreePairAtLeast12Upper13 g u v = true) ↔
        (decide (12 ≤ degreeUpperNat (n := 13) g u + degreeUpperNat (n := 13) g v) = true) := by
    unfold degreePairAtLeast12Upper13 degreePairBits13
    rw [boolFiveAtLeast12_iff (degreePairBits13 g u v)]
    -- replace boolean threshold
    constructor <;> intro h
    · have hnum : 12 ≤ boolFiveValue (degreePairBits13 g u v) := by
        simpa [Bool.decide_eq_true_eq] using h
      have : 12 ≤ degreeUpperNat (n := 13) g u + degreeUpperNat (n := 13) g v := by
        simpa [hfoldv] using hnum
      simpa using this
    · have hnum : 12 ≤ degreeUpperNat (n := 13) g u + degreeUpperNat (n := 13) g v := by
        simpa using h
      have : 12 ≤ boolFiveValue (degreePairBits13 g u v) := by
        simpa [hfoldv] using hnum
      simpa using this
  exact Bool.eq_iff_iff.mpr hth

end Scratch
