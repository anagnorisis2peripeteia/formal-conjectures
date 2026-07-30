import WOWII217Closure13Fast

/-! Nat bridge for `degreePairAtLeast12Upper13`. -/

namespace WOWII217DegreePairBridge

open WOWII217FiniteBase WOWII217Closure WOWII217Closure13Fast

def boolFiveValue (x : BoolFive) : Nat :=
  (if x.b0 then 1 else 0) +
    2 * (if x.b1 then 1 else 0) +
    4 * (if x.b2 then 1 else 0) +
    8 * (if x.b3 then 1 else 0) +
    16 * (if x.b4 then 1 else 0)

theorem boolFiveValue_increment (x : BoolFive) (b : Bool)
    (hx : boolFiveValue x < 31) :
    boolFiveValue (x.increment b) =
      boolFiveValue x + if b then 1 else 0 := by
  rcases x with ⟨b0, b1, b2, b3, b4⟩
  fin_cases b0 <;> fin_cases b1 <;> fin_cases b2 <;> fin_cases b3 <;>
    fin_cases b4 <;> fin_cases b <;>
    simp [boolFiveValue, BoolFive.increment] at hx ⊢

theorem boolFiveValue_zero : boolFiveValue BoolFive.zero = 0 := by
  native_decide

theorem foldl_bool_le_length {α : Type*} (f : α → Bool) :
    ∀ (xs : List α) (a : Nat),
      xs.foldl (fun c x => c + if f x then 1 else 0) a ≤ a + xs.length := by
  intro xs
  induction xs with
  | nil => intro a; simp
  | cons x xs ih =>
      intro a
      simp only [List.foldl_cons, List.length_cons]
      by_cases hx : f x
      · have := ih (a + 1)
        simp [hx] at this ⊢
        omega
      · have := ih a
        simp [hx] at this ⊢
        omega

theorem boolFiveValue_foldl_increment {α : Type*} (f : α → Bool) :
    ∀ (xs : List α) (initial : BoolFive),
      boolFiveValue initial + xs.length < 32 →
      boolFiveValue (xs.foldl (fun bits x => bits.increment (f x)) initial) =
        xs.foldl (fun count x => count + if f x then 1 else 0)
          (boolFiveValue initial) := by
  intro xs
  induction xs with
  | nil => intro initial _; simp
  | cons x xs ih =>
      intro initial bound
      have hlen : (x :: xs).length = xs.length + 1 := rfl
      rw [hlen] at bound
      -- bound : boolFiveValue initial + (xs.length + 1) < 32
      have hlt : boolFiveValue initial < 31 := by
        have : boolFiveValue initial + xs.length + 1 < 32 := by
          simpa [Nat.add_assoc] using bound
        omega
      have hinc := boolFiveValue_increment initial (f x) hlt
      have hbit : (if f x then 1 else 0) ≤ 1 := by split <;> simp
      have hnext_bound :
          boolFiveValue (initial.increment (f x)) + xs.length < 32 := by
        rw [hinc]
        have : boolFiveValue initial + (if f x then 1 else 0) + xs.length < 32 := by
          have := bound
          omega
        simpa [Nat.add_assoc] using this
      have hnext := ih (initial.increment (f x)) hnext_bound
      simp only [List.foldl_cons]
      rw [hnext, hinc]

theorem foldl_count_add {α : Type*} (f : α → Bool) (a b : Nat) :
    ∀ xs : List α,
      xs.foldl (fun c x => c + if f x then 1 else 0) (a + b) =
        a + xs.foldl (fun c x => c + if f x then 1 else 0) b := by
  intro xs
  induction xs generalizing b with
  | nil => simp
  | cons x xs ih =>
      simp only [List.foldl_cons]
      by_cases hx : f x
      · simp [hx, Nat.add_assoc, ih]
      · simp [hx, ih]

private def countAdj (g : BitVec 78) (x : Nat) : Nat :=
  (List.range 13).foldl (fun c w => c + if adjUpper (n := 13) g x w then 1 else 0) 0

private def foldInc (g : BitVec 78) (x : Nat) (init : BoolFive) : BoolFive :=
  (List.range 13).foldl (fun c w => c.increment (adjUpper (n := 13) g x w)) init

theorem foldInc_value (g : BitVec 78) (x : Nat) (init : BoolFive)
    (hbound : boolFiveValue init + 13 < 32) :
    boolFiveValue (foldInc g x init) =
      countAdj g x + boolFiveValue init := by
  have hlen : (List.range 13).length = 13 := by decide
  have h :=
    boolFiveValue_foldl_increment (fun w => adjUpper (n := 13) g x w)
      (List.range 13) init (by simpa [hlen] using hbound)
  -- h : value (foldl inc) = foldl nat from value init
  -- Need = countAdj + value init
  have hadd :=
    foldl_count_add (fun w => adjUpper (n := 13) g x w) (boolFiveValue init) 0
      (List.range 13)
  simp only [foldInc, countAdj] at h hadd ⊢
  rw [h]
  -- hadd : foldl (init+0) = init + foldl 0; simplify init+0
  simpa [Nat.add_comm] using hadd

theorem degreePairBits13_value (g : BitVec 78) (u v : Nat) :
    boolFiveValue (degreePairBits13 g u v) =
      degreeUpperNat (n := 13) g u + degreeUpperNat (n := 13) g v := by
  have hU :=
    foldInc_value g u BoolFive.zero (by simp [boolFiveValue_zero])
  have hUval : boolFiveValue (foldInc g u BoolFive.zero) = countAdj g u := by
    simpa [boolFiveValue_zero] using hU
  have hUle : boolFiveValue (foldInc g u BoolFive.zero) ≤ 13 := by
    have := foldl_bool_le_length (fun w => adjUpper (n := 13) g u w) (List.range 13) 0
    simpa [hUval, countAdj] using this
  have hV :=
    foldInc_value g v (foldInc g u BoolFive.zero) (by omega)
  -- degreePairBits13 = foldInc v (foldInc u zero)
  have hdef : degreePairBits13 g u v = foldInc g v (foldInc g u BoolFive.zero) := by
    rfl
  have hdeg : degreeUpperNat (n := 13) g u = countAdj g u ∧
      degreeUpperNat (n := 13) g v = countAdj g v := by
    constructor <;> rfl
  rw [hdef, hV, hUval, hdeg.1, hdeg.2]
  abel

theorem boolFive_ge12_iff (x : BoolFive) :
    (x.b4 || (x.b3 && x.b2)) = true ↔ 12 ≤ boolFiveValue x := by
  rcases x with ⟨b0, b1, b2, b3, b4⟩
  fin_cases b0 <;> fin_cases b1 <;> fin_cases b2 <;> fin_cases b3 <;>
    fin_cases b4 <;> simp [boolFiveValue]

theorem degreePairAtLeast12Upper13_eq_decide (g : BitVec 78) (u v : Nat) :
    degreePairAtLeast12Upper13 g u v =
      decide (12 ≤ degreeUpperNat (n := 13) g u + degreeUpperNat (n := 13) g v) := by
  unfold degreePairAtLeast12Upper13
  have hval := degreePairBits13_value g u v
  have hiff := boolFive_ge12_iff (degreePairBits13 g u v)
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro h
    have : 12 ≤ boolFiveValue (degreePairBits13 g u v) := hiff.mp h
    simpa [hval, decide_eq_true_eq] using this
  · intro h
    have hP : 12 ≤ degreeUpperNat (n := 13) g u + degreeUpperNat (n := 13) g v := by
      simpa [decide_eq_true_eq] using h
    exact hiff.mpr (by simpa [hval] using hP)

end WOWII217DegreePairBridge
