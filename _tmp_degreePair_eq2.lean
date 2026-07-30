import WOWII217Closure13Fast
import WOWII217Closure
import WOWII217FiniteBase

open WOWII217Closure13Fast WOWII217FiniteBase WOWII217Closure

/-- Sum represented by BoolFive. -/
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
    fin_cases b <;> simp [boolFiveValueR, BoolFive.increment] at hx ⊢

lemma boolFiveValueR_foldl_increment {α : Type*} (f : α → Bool) :
    ∀ (xs : List α) (initial : BoolFive),
      boolFiveValueR initial + xs.length ≤ 31 →
      boolFiveValueR (xs.foldl (fun bits x => bits.increment (f x)) initial) =
        xs.foldl (fun count x => count + if f x then 1 else 0)
          (boolFiveValueR initial) := by
  intro xs
  induction xs with
  | nil =>
      intro initial bound
      simp at bound
      simp
  | cons x xs ih =>
      intro initial bound
      have hx0 : boolFiveValueR (initial.increment (f x)) + xs.length ≤ 31 := by
        by_cases hfx : f x = true
        · have hinitial : boolFiveValueR initial < 31 := by
            have hb : boolFiveValueR initial + 1 + xs.length ≤ 31 := by
              simpa [List.length, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, hfx] using bound
            omega
          rw [boolFiveValueR_increment_of_lt_thirtyone initial true hinitial]
          omega
        · simp [hfx] at bound ⊢
          have hzero : initial.increment false = initial := by
            simp [BoolFive.increment]
          subst hzero
          omega
      simp [List.foldl_cons]
      cases hfx : f x <;>
      simp [BoolFive.increment, hfx, ih _ hx0, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

lemma boolFiveValueR_degreeUpperNat (g : BitVec 78) (u : Nat) :
    boolFiveValueR ((List.range 13).foldl
      (fun bits w => bits.increment (adjUpper (n := 13) g u w)) BoolFive.zero) =
      degreeUpperNat (n := 13) g u := by
  let f : Nat → Bool := fun w => adjUpper (n := 13) g u w
  have hlen : (List.range 13).length ≤ 31 := by simp
  have hzero : boolFiveValueR BoolFive.zero + (List.range 13).length ≤ 31 := by
    simpa [BoolFive.zero, boolFiveValueR]
  have hfold := boolFiveValueR_foldl_increment (f := f) (xs := List.range 13)
    BoolFive.zero hzero
  simpa [f, degreeUpperNat] using hfold

lemma boolFiveAtLeast12_iff (x : BoolFive) :
    (x.b4 || x.b3 && x.b2) = true ↔ 12 ≤ boolFiveValueR x := by
  rcases x with ⟨x0, x1, x2, x3, x4⟩
  fin_cases x0 <;> fin_cases x1 <;> fin_cases x2 <;> fin_cases x3 <;> fin_cases x4 <;>
    decide

lemma boolFoldl_add_eq' {α : Type*} (f : α → Bool) (a : Nat) :
    ∀ (xs : List α),
      (List.foldl (fun count x => count + if f x then 1 else 0) a) =
        a + List.foldl (fun count x => count + if f x then 1 else 0) 0 := by
  intro xs
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp [ih, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

lemma degreePairAtLeast12Upper13_eq (g : BitVec 78) (u v : Nat) :
    degreePairAtLeast12Upper13 g u v =
      decide (12 ≤ degreeUpperNat (n := 13) g u + degreeUpperNat (n := 13) g v) := by
  have hfoldu :
      boolFiveValueR
        ((List.range 13).foldl
          (fun bits w => bits.increment (adjUpper (n := 13) g u w)) BoolFive.zero) =
      degreeUpperNat (n := 13) g u := by
    simpa using boolFiveValueR_degreeUpperNat (g := g) (u := u)
  have hfoldv :
      boolFiveValueR (degreePairBits13 g u v) =
      degreeUpperNat (n := 13) g u + degreeUpperNat (n := 13) g v := by
    let bitsu : BoolFive :=
      (List.range 13).foldl (fun bits w => bits.increment (adjUpper (n := 13) g u w))
        BoolFive.zero
    have hbound : boolFiveValueR bitsu + (List.range 13).length ≤ 31 := by
      rw [hfoldu]
      have hdu : degreeUpperNat (n := 13) g u ≤ 13 := by
        unfold degreeUpperNat
        omega
      have hrange : (List.range 13).length = 13 := by simp
      omega
    have hv := boolFiveValueR_foldl_increment
      (f := fun w => adjUpper (n := 13) g v w) (xs := List.range 13) bitsu hbound
    have hsumv :
        (List.range 13).foldl (fun count x => count + if adjUpper (n := 13) g v x then 1 else 0)
          (boolFiveValueR bitsu) = degreeUpperNat (n := 13) g v + boolFiveValueR bitsu := by
      have haux := boolFoldl_add_eq' (f := fun w => adjUpper (n := 13) g v w) 0 (List.range 13)
      have hdegv : degreeUpperNat (n := 13) g v =
          (List.range 13).foldl (fun count x => count + if adjUpper (n := 13) g v x then 1 else 0) 0 := by
        simpa [degreeUpperNat, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      simpa [haux, hdegv, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
    calc
      boolFiveValueR (degreePairBits13 g u v) =
          (List.range 13).foldl (fun count x => count + if adjUpper (n := 13) g v x then 1 else 0)
            (boolFiveValueR ((List.range 13).foldl (fun bits w => bits.increment (adjUpper (n := 13) g u w)) BoolFive.zero)) := by
          simpa [degreePairBits13] using hv
      _ = degreeUpperNat (n := 13) g u + degreeUpperNat (n := 13) g v := by
          simpa [hfoldu, hsumv, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
  have hth :
      (degreePairAtLeast12Upper13 g u v = true) ↔
        (decide (12 ≤ degreeUpperNat (n := 13) g u + degreeUpperNat (n := 13) g v) = true) := by
    unfold degreePairAtLeast12Upper13
    rw [boolFiveAtLeast12_iff]
    constructor <;> intro h
    · have hnum : 12 ≤ boolFiveValueR (degreePairBits13 g u v) := by
        simpa [Bool.decide_eq_true_eq] using h
      have : 12 ≤ degreeUpperNat (n := 13) g u + degreeUpperNat (n := 13) g v := by
        simpa [hfoldv] using hnum
      simpa using this
    · have hnum : 12 ≤ degreeUpperNat (n := 13) g u + degreeUpperNat (n := 13) g v := by
        simpa using h
      have : 12 ≤ boolFiveValueR (degreePairBits13 g u v) := by
        simpa [hfoldv] using hnum
      simpa using this
  exact Bool.eq_iff_iff.mpr hth

#check degreePairAtLeast12Upper13_eq
