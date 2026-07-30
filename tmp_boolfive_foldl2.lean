import WOWII217Closure13Fast
import WOWII217Finite13
import WOWII217FiniteBase

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
  | cons x xs ih =>
      have hhead : boolFiveValue initial + xs.length < 30 := by omega
      have hzero : boolFiveValue initial < 31 := by omega
      by_cases h : f x
      · have hinc : boolFiveValue (BoolFive.increment initial true) = boolFiveValue initial + 1 := by
          simpa [h] using (boolFiveValue_increment_of_lt_thirtyOne initial true hzero)
        have hnext : boolFiveValue (initial.increment true) + xs.length < 31 := by
          rw [hinc]
          omega
        have hrec := ih (initial.increment true) hnext
        rw [List.foldl_cons, h]
        rw [hinc]
        rw [hrec]
        omega
      · have hinc : boolFiveValue (BoolFive.increment initial false) = boolFiveValue initial := by
          simpa [h] using (boolFiveValue_increment_of_lt_thirtyOne initial false hzero)
        have hnext : boolFiveValue (initial.increment false) + xs.length < 31 := by
          rw [hinc]
          omega
        have hrec := ih (initial.increment false) hnext
        rw [List.foldl_cons, h]
        rw [hinc]
        rw [hrec]
        simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]


theorem boolFiveAtLeast12_iff (x : BoolFive) :
    (x.b4 || (x.b3 && x.b2)) = true ↔ 12 ≤ boolFiveValue x := by
  rcases x with ⟨x0, x1, x2, x3, x4⟩
  fin_cases x0 <;> fin_cases x1 <;> fin_cases x2 <;> fin_cases x3 <;> fin_cases x4 <;>
    decide

/-- this theorem intentionally has no [n] parameter on degreePairBits13. -/
theorem boolFiveValue_degreePairBits13_eq (g : BitVec 78) (u v : Nat) :
    boolFiveValue (degreePairBits13 g u v) =
      degreeUpperNat (n := 13) g u + degreeUpperNat (n := 13) g v := by
  simp [degreePairBits13]
  have hbound0 : boolFiveValue BoolFive.zero + (List.range 13).length < 31 := by
    norm_num
  have h0 :
      boolFiveValue ((List.range 13).foldl (fun count w => count.increment (adjUpper (n := 13) g u w)) BoolFive.zero) =
        degreeUpperNat (n := 13) g u := by
    simpa [degreeUpperNat] using
      (boolFiveValue_foldl_increment (f := fun w => adjUpper (n := 13) g u w)
        (xs := List.range 13) (initial := BoolFive.zero) hbound0)
  have hbound1 :
      boolFiveValue ((List.range 13).foldl (fun count w => count.increment (adjUpper (n := 13) g u w)) BoolFive.zero) +
        (List.range 13).length < 31 := by
    have hu : boolFiveValue ((List.range 13).foldl (fun count w => count.increment (adjUpper (n := 13) g u w)) BoolFive.zero) =
        degreeUpperNat (n := 13) g u := h0
    have hdu : degreeUpperNat (n := 13) g u < 13 := by
      exact (degreeUpperNat_lt (n := 13) (u := u) g).trans_lt (by decide)
    rw [hu, hdu]
    norm_num
  have h1 :
      boolFiveValue ((List.range 13).foldl (fun count w => count.increment (adjUpper (n := 13) g v w))
        ((List.range 13).foldl (fun count w => count.increment (adjUpper (n := 13) g u w)) BoolFive.zero)) =
        boolFiveValue ((List.range 13).foldl (fun count w => count.increment (adjUpper (n := 13) g u w)) BoolFive.zero) +
          (List.range 13).foldl (fun count x => count + if adjUpper (n := 13) g v x then 1 else 0) 0 := by
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      (boolFiveValue_foldl_increment (f := fun w => adjUpper (n := 13) g v w)
        (xs := List.range 13)
        (initial := (List.range 13).foldl (fun count w => count.increment (adjUpper (n := 13) g u w)) BoolFive.zero)
        hbound1)
  calc
    boolFiveValue (degreePairBits13 g u v) =
        boolFiveValue ((List.range 13).foldl (fun count w => count.increment (adjUpper (n := 13) g v w))
          ((List.range 13).foldl (fun count w => count.increment (adjUpper (n := 13) g u w)) BoolFive.zero)) := by
      rfl
    _ = boolFiveValue ((List.range 13).foldl (fun count w => count.increment (adjUpper (n := 13) g u w)) BoolFive.zero) +
          (List.range 13).foldl (fun count x => count + if adjUpper (n := 13) g v x then 1 else 0) 0 := h1
    _ = degreeUpperNat (n := 13) g u +
          (List.range 13).foldl (fun count x => count + if adjUpper (n := 13) g v x then 1 else 0) 0 := by rw [h0]
    _ = degreeUpperNat (n := 13) g u + degreeUpperNat (n := 13) g v := by
      simp [degreeUpperNat]


theorem degreePairAtLeast12Upper13_eq (g : BitVec 78) (u v : Nat) :
    degreePairAtLeast12Upper13 g u v =
      decide (12 ≤ degreeUpperNat (n := 13) g u + degreeUpperNat (n := 13) g v) := by
  have hsum := boolFiveValue_degreePairBits13_eq (g := g) (u := u) (v := v)
  unfold degreePairAtLeast12Upper13
  have hbits :
      (degreePairBits13 g u v).b4 || ((degreePairBits13 g u v).b3 && (degreePairBits13 g u v).b2) = true ↔
      12 ≤ boolFiveValue (degreePairBits13 g u v) :=
    boolFiveAtLeast12_iff (degreePairBits13 g u v)
  rw [hbits, hsum]
