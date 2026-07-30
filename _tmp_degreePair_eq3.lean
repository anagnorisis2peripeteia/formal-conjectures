import WOWII217Closure13Fast
import WOWII217FiniteBase
import WOWII217Closure

open WOWII217Closure13Fast WOWII217FiniteBase WOWII217Closure


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

lemma boolFiveAtLeast12_iff (x : BoolFive) :
    (x.b4 || x.b3 && x.b2) = true ↔ 12 ≤ boolFiveValueR x := by
  rcases x with ⟨x0, x1, x2, x3, x4⟩
  fin_cases x0 <;> fin_cases x1 <;> fin_cases x2 <;> fin_cases x3 <;> fin_cases x4 <;>
    decide

lemma boolFoldl_add_eq (f : α → Bool) (a : Nat) :
    ∀ (xs : List α),
      xs.foldl (fun count x => count + if f x then 1 else 0) a =
        a + xs.foldl (fun count x => count + if f x then 1 else 0) 0 := by
  intro xs
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp [ih, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

lemma boolFiveValueR_degreeUpperNat (g : BitVec 78) (u : Nat) :
    boolFiveValueR ((List.range 13).foldl
      (fun bits w => bits.increment (adjUpper (n := 13) g u w)) BoolFive.zero) =
      degreeUpperNat (n := 13) g u := by
  let f : Nat → Bool := fun w => adjUpper (n := 13) g u w
  have hbound : boolFiveValueR BoolFive.zero + (List.range 13).length ≤ 31 := by
    simp
  have hfold := boolFiveValueR_foldl_increment (f := f) (xs := List.range 13)
    BoolFive.zero hbound
  simpa [f, degreeUpperNat, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hfold

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
      (List.range 13).foldl
        (fun bits w => bits.increment (adjUpper (n := 13) g u w)) BoolFive.zero
    have hbound : boolFiveValueR bitsu + (List.range 13).length ≤ 31 := by
      have hvu : boolFiveValueR bitsu = degreeUpperNat (n := 13) g u := by
        simpa [bitsu] using hfoldu
      rw [hvu]
      have hdu : degreeUpperNat (n := 13) g u ≤ 13 := by
        unfold degreeUpperNat
        omega
      omega
    have hvFold :=
      boolFiveValueR_foldl_increment (f := fun w => adjUpper (n := 13) g v w)
        (xs := List.range 13) bitsu hbound
    have hsumv :
        (List.range 13).foldl (fun count x => count + if adjUpper (n := 13) g v x then 1 else 0)
          (boolFiveValueR bitsu) = degreeUpperNat (n := 13) g v + boolFiveValueR bitsu := by
      have haux := boolFoldl_add_eq (f := fun w => adjUpper (n := 13) g v w) 0 (List.range 13)
      have hdegv : degreeUpperNat (n := 13) g v =
          (List.range 13).foldl (fun count x => count + if adjUpper (n := 13) g v x then 1 else 0) 0 := by
        unfold degreeUpperNat
        simp [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      simpa [haux, hdegv, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
    calc
      boolFiveValueR (degreePairBits13 g u v) =
          (List.range 13).foldl (fun count x => count + if adjUpper (n := 13) g v x then 1 else 0)
            (boolFiveValueR bitsu) := by
            simpa [degreePairBits13, bitsu] using hvFold
      _ = degreeUpperNat (n := 13) g u + degreeUpperNat (n := 13) g v := by
        simpa [hfoldu, hsumv, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
  have hdec :
      (degreePairAtLeast12Upper13 g u v = true) ↔
        (decide (12 ≤ degreeUpperNat (n := 13) g u + degreeUpperNat (n := 13) g v) = true) := by
    unfold degreePairAtLeast12Upper13
    rw [boolFiveAtLeast12_iff (degreePairBits13 g u v)]
    constructor <;> intro h
    · have hnum : 12 ≤ boolFiveValueR (degreePairBits13 g u v) := by
        simpa using h
      have : 12 ≤ degreeUpperNat (n := 13) g u + degreeUpperNat (n := 13) g v := by
        simpa [hfoldv] using hnum
      simpa using this
    · have hnum : 12 ≤ degreeUpperNat (n := 13) g u + degreeUpperNat (n := 13) g v := by
        simpa using h
      have : 12 ≤ boolFiveValueR (degreePairBits13 g u v) := by
        simpa [hfoldv] using hnum
      simpa using this
  exact Bool.eq_iff_iff.mpr hdec

#check degreePairAtLeast12Upper13_eq
