import WOWII217Closure13Fast
import WOWII217Finite13
import WOWII217Closure
import WOWII217FiniteBase

open WOWII217Closure13Fast WOWII217Finite13 WOWII217FiniteBase WOWII217Closure

-- Sum represented by BoolFour

def boolFourValue' (x : BoolFour) : Nat :=
  (if x.b0 then 1 else 0) +
  2 * (if x.b1 then 1 else 0) +
  4 * (if x.b2 then 1 else 0) +
  8 * (if x.b3 then 1 else 0)

def boolFiveValue' (x : BoolFive) : Nat :=
  (if x.b0 then 1 else 0) +
    2 * (if x.b1 then 1 else 0) +
    4 * (if x.b2 then 1 else 0) +
    8 * (if x.b3 then 1 else 0) +
    16 * (if x.b4 then 1 else 0)

lemma boolFourValue_increment_of_lt_fifteen' (x : BoolFour) (b : Bool)
    (hx : boolFourValue' x < 15) :
    boolFourValue' (x.increment b) =
      boolFourValue' x + if b then 1 else 0 := by
  rcases x with ⟨b0, b1, b2, b3⟩
  fin_cases b0 <;> fin_cases b1 <;> fin_cases b2 <;> fin_cases b3 <;>
    fin_cases b <;> simp [boolFourValue', BoolFour.increment] at hx ⊢

lemma boolFourValue_foldl_increment' {α : Type*} (f : α → Bool) :
    ∀ (xs : List α) (initial : BoolFour),
      boolFourValue' initial + xs.length < 16 →
      boolFourValue' (xs.foldl (fun bits x => bits.increment (f x)) initial) =
        xs.foldl (fun count x => count + if f x then 1 else 0) (boolFourValue' initial) := by
  intro xs
  induction xs with
  | nil => simp
  | cons x xs ih =>
      intro initial bound
      simp only [List.foldl_cons] at bound ⊢
      have hbit : (if f x then 1 else 0) ≤ 1 := by split <;> simp
      have hinit : boolFourValue' (initial.increment (f x)) + xs.length < 16 := by
        have hinitial : boolFourValue' initial < 15 := by omega
        rw [boolFourValue_increment_of_lt_fifteen' initial (f x) hinitial]
        omega
      have hnext := ih (initial.increment (f x)) hinit
      rw [hnext, boolFourValue_increment_of_lt_fifteen' initial (f x)]
      omega

lemma boolFourValue_degreeBitsUpper_eq' {n : Nat} (hn : n < 16)
    (g : BitVec (edgeCount n)) (u : Nat) :
    boolFourValue' (degreeBitsUpper g u) = degreeUpperNat g u := by
  unfold degreeBitsUpper degreeUpperNat
  have folded := boolFourValue_foldl_increment' (fun v => adjUpper g u v) (List.range n)
    { b0 := false, b1 := false, b2 := false, b3 := false }
  simpa [boolFourValue'] using folded (by simpa [boolFourValue'] using hn)

lemma boolFiveAtLeast12_iff' (x : BoolFive) :
    (x.b4 || x.b3 && x.b2) = true ↔ 12 ≤ boolFiveValue' x := by
  rcases x with ⟨x0, x1, x2, x3, x4⟩
  fin_cases x0 <;> fin_cases x1 <;> fin_cases x2 <;> fin_cases x3 <;> fin_cases x4 <;>
    decide

lemma boolFiveValue_degreePairBits13' (g : BitVec 78) (u : Nat) :
    boolFiveValue' ((List.range 13).foldl
      (fun bits w => bits.increment (adjUpper (n := 13) g u w)) BoolFive.zero) =
    degreeUpperNat (n := 13) g u := by
  let f : Nat → Bool := fun w => adjUpper (n := 13) g u w
  have hfold := boolFourValue_foldl_increment' (f := f) (xs := List.range 13)
    BoolFour.zero (by decide : boolFourValue' BoolFour.zero + (List.range 13).length < 16)
  simpa [f, BoolFour.zero, degreeUpperNat, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hfold

lemma degreePairAtLeast12Upper13_eq' (g : BitVec 78) (u v : Nat) :
    degreePairAtLeast12Upper13 g u v =
      decide (12 ≤ degreeUpperNat (n := 13) g u + degreeUpperNat (n := 13) g v) := by
  have hdeg_u :
      boolFiveValue' ((List.range 13).foldl
        (fun bits w => bits.increment (adjUpper (n := 13) g u w)) BoolFive.zero) =
      degreeUpperNat (n := 13) g u := by
    simpa using boolFiveValue_degreePairBits13' (g := g) (u := u)
  have hfoldv :
      boolFiveValue' (degreePairBits13 g u v) =
      degreeUpperNat (n := 13) g u + degreeUpperNat (n := 13) g v := by
    let bitsu : BoolFive :=
      (List.range 13).foldl (fun bits w => bits.increment (adjUpper (n := 13) g u w))
        BoolFive.zero
    have hbound : boolFiveValue' bitsu + (List.range 13).length < 32 := by
      have hdeg : boolFiveValue' bitsu = degreeUpperNat (n := 13) g u := by
        simpa [bitsu] using hdeg_u
      have hdeg_bound : degreeUpperNat (n := 13) g u ≤ 13 := by
        unfold degreeUpperNat
        omega
      rw [hdeg]
      omega
    have hv :=
      boolFiveValue_foldl_increment (f := fun w => adjUpper (n := 13) g v w)
        (xs := List.range 13) bitsu hbound
    have hsumv :
      (List.range 13).foldl (fun count x => count + if adjUpper (n := 13) g v x then 1 else 0)
        (boolFiveValue' bitsu) = degreeUpperNat (n := 13) g v + boolFiveValue' bitsu := by
      have haux := boolFoldl_add_eq (f := fun w => adjUpper (n := 13) g v w) 0 (List.range 13)
      have hdegv : degreeUpperNat (n := 13) g v = (List.range 13).foldl (fun count x =>
        count + if adjUpper (n := 13) g v x then 1 else 0) 0 := by
        simpa [degreeUpperNat, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      simpa [haux, hdegv, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
    calc
      boolFiveValue' (degreePairBits13 g u v) =
          (List.range 13).foldl (fun count x => count + if adjUpper (n := 13) g v x then 1 else 0)
            (boolFiveValue' ((List.range 13).foldl
              (fun bits w => bits.increment (adjUpper (n := 13) g u w)) BoolFive.zero)) := by
          simpa [degreePairBits13] using hv
      _ = degreeUpperNat (n := 13) g u + degreeUpperNat (n := 13) g v := by
          simpa [hdeg_u, hsumv, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
  have hth :
      (degreePairAtLeast12Upper13 g u v = true) ↔
        (decide (12 ≤ degreeUpperNat (n := 13) g u + degreeUpperNat (n := 13) g v) = true) := by
    unfold degreePairAtLeast12Upper13 degreePairBits13
    rw [boolFiveAtLeast12_iff' (degreePairBits13 g u v)]
    constructor <;> intro h
    · have hnum : 12 ≤ boolFiveValue' (degreePairBits13 g u v) := by
        simpa [Bool.decide_eq_true_eq] using h
      have : 12 ≤ degreeUpperNat (n := 13) g u + degreeUpperNat (n := 13) g v := by
        simpa [hfoldv] using hnum
      simpa using this
    · have hnum : 12 ≤ degreeUpperNat (n := 13) g u + degreeUpperNat (n := 13) g v := by
        simpa using h
      have : 12 ≤ boolFiveValue' (degreePairBits13 g u v) := by
        simpa [hfoldv] using hnum
      simpa using this
  exact Bool.eq_iff_iff.mpr hth

#check degreePairAtLeast12Upper13_eq'
