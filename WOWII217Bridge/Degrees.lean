import WOWII217Closure
import WOWII217ClosureSemantics

namespace L145

open WOWII217FiniteBase WOWII217Closure

/-- L1. `|||` on the encoding is `||` on adjacency. -/
theorem adjUpper_or {n : Nat} (g m : BitVec (edgeCount n)) (u v : Nat) :
    adjUpper (n := n) (g ||| m) u v = (adjUpper g u v || adjUpper m u v) := by
  unfold adjUpper
  by_cases h1 : u < v
  · simp [h1, BitVec.getLsbD_or]
  · by_cases h2 : v < u
    · simp [h1, h2, BitVec.getLsbD_or]
    · simp [h1, h2]

/-- Degrees are bounded by the range folded over. -/
theorem degreeUpperNat_le {n : Nat} (g : BitVec (edgeCount n)) (u : Nat) :
    degreeUpperNat (n := n) g u ≤ n := by
  unfold degreeUpperNat
  have : ∀ (xs : List Nat) (init : Nat),
      xs.foldl (fun d v => d + if adjUpper (n := n) g u v then 1 else 0) init
        ≤ init + xs.length := by
    intro xs
    induction xs with
    | nil => intro init; simp
    | cons x xs ih =>
        intro init
        simp only [List.foldl_cons, List.length_cons]
        exact le_trans (ih _) (by split <;> omega)
  simpa using this (List.range n) 0

/-- L4. `BitVec.ofNat 5` is additive and `BitVec 5` addition is mod 32, so no bound
is needed here; the bound only matters for the comparison (L5). -/
theorem degreeUpperBv5_eq_ofNat {n : Nat} (g : BitVec (edgeCount n)) (u : Nat) :
    degreeUpperBv5 (n := n) g u = BitVec.ofNat 5 (degreeUpperNat (n := n) g u) := by
  unfold degreeUpperBv5 degreeUpperNat
  have key : ∀ (xs : List Nat) (init : Nat),
      xs.foldl (fun s v => s + bif adjUpper (n := n) g u v then 1#5 else 0#5)
          (BitVec.ofNat 5 init)
        = BitVec.ofNat 5 (xs.foldl (fun d v => d + if adjUpper (n := n) g u v then 1 else 0)
            init) := by
    intro xs
    induction xs with
    | nil => intro init; simp
    | cons x xs ih =>
        intro init
        simp only [List.foldl_cons]
        have step : (BitVec.ofNat 5 init + bif adjUpper (n := n) g u x then 1#5 else 0#5)
            = BitVec.ofNat 5 (init + if adjUpper (n := n) g u x then 1 else 0) := by
          cases h : adjUpper (n := n) g u x <;> simp [h, BitVec.ofNat_add]
        rw [step, ih]
  simpa using key (List.range n) 0


/-- L5. The closure test means what we want, given `n < 16`: degrees are `≤ n`, so the
sum is `≤ 30 < 32` and nothing wraps in `BitVec 5`. -/
theorem bv5_threshold_iff {n : Nat} (hn : n < 16) (g : BitVec (edgeCount n)) (u v : Nat) :
    (BitVec.ofNat 5 (n - 1) ≤ degreeUpperBv5 (n := n) g u + degreeUpperBv5 (n := n) g v)
      ↔ n - 1 ≤ degreeUpperNat (n := n) g u + degreeUpperNat (n := n) g v := by
  have hu := degreeUpperNat_le g u
  have hv := degreeUpperNat_le g v
  rw [degreeUpperBv5_eq_ofNat, degreeUpperBv5_eq_ofNat, ← BitVec.ofNat_add]
  rw [BitVec.le_def, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  constructor
  · intro h
    have h1 : (n - 1) % 2 ^ 5 = n - 1 := Nat.mod_eq_of_lt (by omega)
    have h2 : (degreeUpperNat (n := n) g u + degreeUpperNat (n := n) g v) % 2 ^ 5
        = degreeUpperNat (n := n) g u + degreeUpperNat (n := n) g v :=
      Nat.mod_eq_of_lt (by omega)
    omega
  · intro h
    have h1 : (n - 1) % 2 ^ 5 = n - 1 := Nat.mod_eq_of_lt (by omega)
    have h2 : (degreeUpperNat (n := n) g u + degreeUpperNat (n := n) g v) % 2 ^ 5
        = degreeUpperNat (n := n) g u + degreeUpperNat (n := n) g v :=
      Nat.mod_eq_of_lt (by omega)
    omega

end L145

