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
    boolFiveValue (BoolFive.increment x b) =
      boolFiveValue x + if b then 1 else 0 := by
  rcases x with ⟨x0, x1, x2, x3, x4⟩
  fin_cases x0 <;> fin_cases x1 <;> fin_cases x2 <;> fin_cases x3 <;>
    fin_cases x4 <;> fin_cases b <;>
    simp [boolFiveValue, BoolFive.increment] at hx ⊢

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
      simp only [List.foldl_cons]
      by_cases hx : f x
      · have hinitial : boolFiveValue initial < 31 := by
          omega
        have hnext :
            boolFiveValue (BoolFive.increment initial true) + xs.length < 32 := by
          rw [boolFiveValue_increment_of_lt_thirtyone initial true hinitial]
          omega
        rw [ih _ hnext]
        rw [boolFiveValue_increment_of_lt_thirtyone initial true hinitial]
        omega
      · have hFalse : BoolFive.increment initial false = initial := by
          simp [BoolFive.increment, hx]
        have hnext :
            boolFiveValue (BoolFive.increment initial false) + xs.length < 32 := by
          rw [hFalse]
          omega
        rw [hFalse]
        rw [ih _ hnext]
        simp [hx]

 theorem boolFoldl_add_eq (f : α → Bool) (a : Nat) :
    ∀ (xs : List α),
      xs.foldl (fun count x => count + if f x then 1 else 0) a =
        a + xs.foldl (fun count x => count + if f x then 1 else 0) 0 := by
  intro xs
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp [ih, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

 theorem boolFiveValue_degreeUpperNat (g : BitVec 78) (u : Nat) :
    boolFiveValue
      ((List.range 13).foldl
        (fun bits w => bits.increment (adjUpper (n := 13) g u w)) BoolFive.zero) =
      degreeUpperNat (n := 13) g u := by
  let f : Nat → Bool := fun w => adjUpper (n := 13) g u w
  have hfold := boolFiveValue_foldl_increment (f := f) (xs := List.range 13)
    BoolFive.zero (by decide : boolFiveValue BoolFive.zero + (List.range 13).length < 32)
  simpa [f, degreeUpperNat] using hfold

 theorem degreePairAtLeast12Upper13_eq (g : BitVec 78) (u v : Nat) :
    degreePairAtLeast12Upper13 g u v =
      decide (12 ≤ degreeUpperNat (n := 13) g u + degreeUpperNat (n := 13) g v) := by
  rw [degreePairAtLeast12Upper13]
  have hdegu :
      boolFiveValue ((List.range 13).foldl
        (fun bits w => bits.increment (adjUpper (n := 13) g u w)) BoolFive.zero) =
      degreeUpperNat (n := 13) g u := by
    simpa using boolFiveValue_degreeUpperNat (g := g) (u := u)
  have hdegv :
      boolFiveValue ((List.range 13).foldl
        (fun bits w => bits.increment (adjUpper (n := 13) g v w))
        ((List.range 13).foldl
          (fun bits w => bits.increment (adjUpper (n := 13) g u w)) BoolFive.zero)) =
      degreeUpperNat (n := 13) g v + degreeUpperNat (n := 13) g u := by
    let bitsu :=
      (List.range 13).foldl (fun bits w => bits.increment (adjUpper (n := 13) g u w))
        BoolFive.zero
    have hv :
      boolFiveValue
        ((List.range 13).foldl
          (fun bits w => bits.increment (adjUpper (n := 13) g v w)) bitsu) =
        (List.range 13).foldl (fun count x => count + if adjUpper (n := 13) g v x then 1 else 0)
          (boolFiveValue bitsu) := by
      have hbound : boolFiveValue bitsu + (List.range 13).length < 32 := by
        have hb : boolFiveValue bitsu ≤ 13 := by
          have h := boolFiveValue_degreeUpperNat (g := g) (u := u)
          rw [h]
          simp [degreeUpperNat]
          omega
        omega
      simpa using (boolFiveValue_foldl_increment (f := fun x => adjUpper (n := 13) g v x)
        (xs := List.range 13) bitsu hbound)
    rw [hv]
    rw [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
    rw [hdegu]
    simpa [degreeUpperNat, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, boolFoldl_add_eq]
  have hbits :
      degreePairAtLeast12Upper13 g u v = (boolFiveValue (degreePairBits13 g u v) =? true)
      := by
    rfl
  have hthr :
      boolFiveValue (degreePairBits13 g u v) ≥ 12 ↔
        decide (12 ≤ degreeUpperNat (n := 13) g u + degreeUpperNat (n := 13) g v) := by
    rw [degreePairBits13, Bool.eq_true_eq]
    have hb4 :
      (degreePairBits13 g u v).b4 || (degreePairBits13 g u v).b3 && (degreePairBits13 g u v).b2 =
        ((12 ≤ boolFiveValue (degreePairBits13 g u v)) := by sorry
    sorry
  sorry

