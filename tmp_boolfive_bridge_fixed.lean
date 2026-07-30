import WOWII217Closure13Fast
import WOWII217Finite13
import WOWII217FiniteBase

open WOWII217Closure13Fast
open WOWII217FiniteBase
open WOWII217Closure

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in

def boolFiveValue (x : BoolFive) : Nat :=
  (if x.b0 then 1 else 0) +
    2 * (if x.b1 then 1 else 0) +
    4 * (if x.b2 then 1 else 0) +
    8 * (if x.b3 then 1 else 0) +
    16 * (if x.b4 then 1 else 0)

theorem boolFiveValue_increment_of_lt_thirtytwo (x : BoolFive) (b : Bool)
    (hx : boolFiveValue x < 32) :
    boolFiveValue (BoolFive.increment x b) = boolFiveValue x + if b then 1 else 0 := by
  rcases x with ⟨x0, x1, x2, x3, x4⟩
  fin_cases b <;> fin_cases x0 <;> fin_cases x1 <;> fin_cases x2 <;> fin_cases x3 <;> fin_cases x4 <;>
    simp [boolFiveValue, BoolFive.increment] at hx ⊢

theorem boolFiveValue_foldl_increment (f : α → Bool) (xs : List α) (initial : BoolFive)
    (hbound : boolFiveValue initial + xs.length < 32) :
    boolFiveValue (xs.foldl (fun bits x => bits.increment (f x)) initial) =
      boolFiveValue initial + (xs.foldl (fun count x => count + if f x then 1 else 0) 0) := by
  induction xs generalizing initial with
  | nil => simp at hbound
  | cons x xs ih =>
      simp only [List.foldl_cons]
      have hhead : boolFiveValue initial + (xs.length + 1) < 32 := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hbound
      have hinitial : boolFiveValue initial < 32 := by omega
      by_cases h : f x = true
      · have hnext : boolFiveValue (initial.increment true) + xs.length < 32 := by
          rw [boolFiveValue_increment_of_lt_thirtytwo initial true hinitial]
          omega
        have htail := ih (initial.increment true) hnext
        rw [h]
        rw [hhead] at hnext
        have hinc : boolFiveValue (initial.increment true) = boolFiveValue initial + 1 := by
          simpa using (boolFiveValue_increment_of_lt_thirtytwo initial true hinitial)
        rw [htail, hinc]
        simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      · have hnext : boolFiveValue (initial.increment false) + xs.length < 32 := by
          rw [boolFiveValue_increment_of_lt_thirtytwo initial false hinitial]
          simpa [h, Nat.add_assoc] using hhead
        have htail := ih (initial.increment false) hnext
        rw [h]
        have hinc : boolFiveValue (initial.increment false) = boolFiveValue initial := by
          simpa [h] using (boolFiveValue_increment_of_lt_thirtytwo initial false hinitial)
        rw [htail, hinc]
        simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

theorem boolFiveValue_degreePairBits13_eq (g : BitVec 78) (u v : Nat) :
    boolFiveValue (degreePairBits13 (n := 13) g u v) =
      degreeUpperNat (n := 13) g u + degreeUpperNat (n := 13) g v := by
  simp [degreePairBits13]
  have h0 :
      boolFiveValue ((List.range 13).foldl (fun count w => count.increment (adjUpper (n := 13) g u w)) BoolFive.zero) =
        degreeUpperNat (n := 13) g u := by
    have hbound : boolFiveValue BoolFive.zero + (List.range 13).length < 32 := by decide
    simpa [List.length] using
      (boolFiveValue_foldl_increment (f := fun w => adjUpper (n := 13) g u w)
        (xs := List.range 13) (initial := BoolFive.zero) hbound)
  have h1 :
      boolFiveValue ((List.range 13).foldl (fun count w => count.increment (adjUpper (n := 13) g v w))
          ((List.range 13).foldl (fun count w => count.increment (adjUpper (n := 13) g u w)) BoolFive.zero) =
        (List.range 13).foldl (fun count x => count + if adjUpper (n := 13) g v x then 1 else 0) 0
          + boolFiveValue (List.range 13).foldl (fun count w => count.increment (adjUpper (n := 13) g u w)) BoolFive.zero := by
    have hbound :
        boolFiveValue ((List.range 13).foldl (fun count w => count.increment (adjUpper (n := 13) g u w)) BoolFive.zero) +
          (List.range 13).length < 32 := by
      have hu0 : boolFiveValue ((List.range 13).foldl (fun count w => count.increment (adjUpper (n := 13) g u w)) BoolFive.zero) ≤ 13 := by
        have hu : boolFiveValue ((List.range 13).foldl (fun count w => count.increment (adjUpper (n := 13) g u w)) BoolFive.zero)
            = degreeUpperNat (n := 13) g u := by simpa [h0]
        have hd : degreeUpperNat (n := 13) g u ≤ 12 := by
          have : degreeUpperNat (n := 13) g u < 13 := by
            exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_of_lt (Nat.lt_of_lt_of_le (Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.zero_lt_succ 10))))))))))))))))))))
          omega
        rw [hu] at hd
        exact le_trans hd (by decide)
      have hlen : (List.range 13).length = 13 := by decide
      omega
    have := boolFiveValue_foldl_increment (f := fun w => adjUpper (n := 13) g v w)
      (xs := List.range 13)
      (initial := (List.range 13).foldl (fun count w => count.increment (adjUpper (n := 13) g u w)) BoolFive.zero)
      hbound
    simpa [h0] using this
  calc
    boolFiveValue (degreePairBits13 (n := 13) g u v) =
        (List.range 13).foldl (fun count x => count + if adjUpper (n := 13) g v x then 1 else 0) 0 +
          boolFiveValue ((List.range 13).foldl (fun count w => count.increment (adjUpper (n := 13) g u w)) BoolFive.zero) := by
      simpa [degreePairBits13] using h1
    _ = degreeUpperNat (n := 13) g v + degreeUpperNat (n := 13) g u := by
      simp [h0, degreeUpperNat, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
    _ = degreeUpperNat (n := 13) g u + degreeUpperNat (n := 13) g v := by omega

theorem boolFiveAtLeast12_iff (x : BoolFive) :
    (x.b4 || (x.b3 && x.b2)) = true ↔ 12 ≤ boolFiveValue x := by
  rcases x with ⟨x0, x1, x2, x3, x4⟩
  fin_cases x0 <;> fin_cases x1 <;> fin_cases x2 <;> fin_cases x3 <;> fin_cases x4 <;> decide

theorem degreePairAtLeast12Upper13_eq (g : BitVec 78) (u v : Nat) :
    WOWII217Closure13Fast.degreePairAtLeast12Upper13 (n := 13) g u v =
      decide (12 ≤ degreeUpperNat (n := 13) g u + degreeUpperNat (n := 13) g v) := by
  have hsum := boolFiveValue_degreePairBits13_eq (n := 13) g u v
  unfold degreePairAtLeast12Upper13
  change (let count := degreePairBits13 (n := 13) g u v; count.b4 || (count.b3 && count.b2)) = true ↔ _
  rw [boolFiveAtLeast12_iff (degreePairBits13 (n := 13) g u v)]
  simpa [hsum] 
