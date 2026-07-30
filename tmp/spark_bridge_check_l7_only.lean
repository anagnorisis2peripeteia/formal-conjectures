import WOWII217ClosureSemantics
import WOWII217Closure
import WOWII217BondyChvatal
import WOWII217Connected10

open SimpleGraph WOWII217FiniteBase WOWII217Closure WOWII217ClosureSemantics
open WOWII217BondyChvatal

open scoped BigOperators

lemma bitMask_getLsbD_copy {w : Nat} (b : Bool) (v : Fin w) :
    (bitMask (w := w) b).getLsbD v = b := by
  simpa using WOWII217Connected10.bitMask_getLsbD (w := w) b v

lemma setBit_getLsbD_fin_copy {w i : Nat} (x : BitVec w) (j : Fin w) (b : Bool) :
    (setBit x i b).getLsbD j = (x.getLsbD j || ((i = j) && b)) := by
  by_cases h' : i = j
  · subst h'
    simp [setBit, BitVec.getLsbD_or, BitVec.getLsbD_and, bitMask_getLsbD_copy, j.isLt]
  · simp [setBit, BitVec.getLsbD_or, BitVec.getLsbD_and, bitMask_getLsbD_copy, j.isLt, h']

lemma foldl_setBit_pair_eq_zero {w : Nat} (es : List (Nat × Nat)) (target : Fin w)
    (f : (Nat × Nat) → Bool) :
    (es.foldl (fun current p => setBit current (upperIndex p.1 p.2) (f p)) (BitVec.zero w)).getLsbD target = true ↔
      (∃ p ∈ es, (target : Nat) = upperIndex p.1 p.2 ∧ f p = true) := by
  induction es with
  | nil => simp
  | cons p es ih =>
      rcases p with ⟨pu, pv⟩
      by_cases hidx : upperIndex pu pv = (target : Nat)
      · by_cases hleg : f (pu, pv) = true
        · simp [List.foldl_cons, hidx, hleg, ih, setBit_getLsbD_fin_copy, List.mem_cons,
            and_left_comm, and_assoc, or_left_comm]
        · simp [List.foldl_cons, hidx, hleg, ih, setBit_getLsbD_fin_copy, List.mem_cons,
            and_left_comm, and_assoc, or_left_comm]
      · simp [List.foldl_cons, hidx, ih, setBit_getLsbD_fin_copy, List.mem_cons,
          and_left_comm, and_assoc, or_left_comm]

lemma setBit_eq_copy {w : Nat} {i : Nat} (x : BitVec w) {j : Fin w} (hij : i ≠ j) (b : Bool) :
    (setBit x i b).getLsbD j = x.getLsbD j := by
  cases b <;> simp [setBit_getLsbD_fin_copy, hij]

/-- Degrees are bounded by the range being folded over. -/
theorem degreeUpperNat_le {n : Nat} (g : BitVec (edgeCount n)) (u : Nat) :
    degreeUpperNat (n := n) g u ≤ n := by
  unfold degreeUpperNat
  have hbound : ∀ (l : List Nat) (m : Nat),
      l.foldl (fun d v => d + (if adjUpper g u v then 1 else 0)) m ≤ m + l.length := by
    intro l
    induction l with
    | nil =>
        intro m
        simp
    | cons v l ih =>
        intro m
        by_cases hv : adjUpper g u v = true
        · have h := ih (m + 1)
          simpa [List.foldl_cons, hv, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h
        · have h := ih m
          have h' : m + l.length ≤ m + (l.length + 1) := by omega
          calc
            List.foldl (fun d v => d + (if adjUpper g u v = true then 1 else 0)) m (v :: l)
                ≤ m + l.length := by simpa [List.foldl_cons, hv] using h
            _ ≤ m + (l.length + 1) := h'
  have := hbound (List.range n) 0
  simpa using this

/-- L4. -/
theorem degreeUpperBv5_eq_ofNat {n : Nat} (g : BitVec (edgeCount n)) (u : Nat) :
    degreeUpperBv5 (n := n) g u = BitVec.ofNat 5 (degreeUpperNat (n := n) g u) := by
  unfold degreeUpperBv5 degreeUpperNat
  have hstep : ∀ (t : Nat),
      (BitVec.ofNat 5 t + (1#5)) = BitVec.ofNat 5 (t + 1) := by
    intro t
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.add_mod]
  have hfold :
      ∀ (xs : List Nat) (t : Nat),
        xs.foldl (fun sum v => sum + (if adjUpper g u v then (1#5) else (0#5))) (BitVec.ofNat 5 t) =
          BitVec.ofNat 5 (xs.foldl (fun d v => d + (if adjUpper g u v then 1 else 0)) t) := by
    intro xs t
    induction xs generalizing t with
    | nil =>
        simp
    | cons v xs ih =>
        by_cases hv : adjUpper g u v = true
        · simp [hv, ih, hstep, Nat.add_assoc]
        · simp [hv, ih]
  have hbif : ∀ (b : Bool) (x y : BitVec 5), (if b = true then x else y) = (bif b then x else y) := by
    intro b x y
    cases b <;> simp
  simpa [hbif] using (hfold (List.range n) 0)

/-- L5. -/
theorem bv5_threshold_iff {n : Nat} (hn : n < 16)
    (g : BitVec (edgeCount n)) (u v : Nat) :
    (BitVec.ofNat 5 (n - 1) ≤ degreeUpperBv5 (n := n) g u + degreeUpperBv5 (n := n) g v) ↔
      n - 1 ≤ degreeUpperNat (n := n) g u + degreeUpperNat (n := n) g v := by
  have hleft : (BitVec.ofNat 5 (n - 1)).toNat = n - 1 := by
    rw [BitVec.toNat_ofNat]
    have hlt : n - 1 < 2 ^ 5 := by omega
    exact Nat.mod_eq_of_lt hlt
  have hdu : degreeUpperNat (n := n) g u ≤ n := degreeUpperNat_le (g := g) (u := u)
  have hdv : degreeUpperNat (n := n) g v ≤ n := degreeUpperNat_le (g := g) (u := v)
  have hsum_lt : degreeUpperNat (n := n) g u + degreeUpperNat (n := n) g v < 2 ^ 5 := by
    omega
  have hsu : (degreeUpperBv5 (n := n) g u).toNat =
      degreeUpperNat (n := n) g u := by
    rw [degreeUpperBv5_eq_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    omega
  have hsv : (degreeUpperBv5 (n := n) g v).toNat =
      degreeUpperNat (n := n) g v := by
    rw [degreeUpperBv5_eq_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    omega
  have htoNat :
      (degreeUpperBv5 (n := n) g u + degreeUpperBv5 (n := n) g v).toNat =
        degreeUpperNat (n := n) g u + degreeUpperNat (n := n) g v := by
    rw [BitVec.toNat_add, hsu, hsv]
    exact Nat.mod_eq_of_lt hsum_lt
  simpa [BitVec.le_def, hleft, htoNat]

/-- L7. -/
theorem adjUpper_mask_iff {n : Nat} (hn : n < 16) (g : BitVec (edgeCount n))
    (u v : Nat) (huv : u < v) (hv : v < n) :
    adjUpper (n := n) (pathClosureParallelMask (n := n) g) u v = true ↔
      adjUpper (n := n) g u v = false ∧
        n - 1 ≤ degreeUpperNat (n := n) g u + degreeUpperNat (n := n) g v := by
  have hidx : upperIndex u v < edgeCount n := by
    interval_cases n <;> interval_cases v <;> interval_cases u <;> decide
  let t : Fin (edgeCount n) := ⟨upperIndex u v, hidx⟩
  have hAdj :
      adjUpper (n := n) (pathClosureParallelMask (n := n) g) u v = true ↔
        (pathClosureParallelMask (n := n) g).getLsbD t = true := by
    simp [adjUpper, huv, t]
  rw [hAdj]
  rw [show (pathClosureParallelMask (n := n) g).getLsbD t = true ↔
      (∃ p ∈ (upperPairs n), (t : Nat) = upperIndex p.1 p.2 ∧
        (!adjUpper (n := n) g p.1 p.2 &&
          (BitVec.ofNat 5 (n - 1) ≤
            degreeUpperBv5 (n := n) g p.1 + degreeUpperBv5 (n := n) g p.2) = true) from
      (foldl_setBit_pair_eq_zero (w := edgeCount n) (es := upperPairs n)
        (target := t)
        (f := fun p =>
          !adjUpper (n := n) g p.1 p.2 &&
            (BitVec.ofNat 5 (n - 1) ≤
              degreeUpperBv5 (n := n) g p.1 + degreeUpperBv5 (n := n) g p.2))]
  constructor
  · rintro h
    rcases h with ⟨p, hpmem, hteq, hleg⟩
    have hp : p ∈ upperPairs n := hpmem
    have hpair : p.1 = u ∧ p.2 = v := by
      have hEq1 : upperIndex p.1 p.2 = upperIndex u v := by
        simpa using hteq
      omega
    rcases hpair with ⟨rfl, rfl⟩
    have hnotAdj : !adjUpper (n := n) g u v = true := by
      exact (Bool.and_eq_true.mp (by simpa using hleg)).1
    have hCond : n - 1 ≤ degreeUpperNat (n := n) g u + degreeUpperNat (n := n) g v := by
      have hBv : BitVec.ofNat 5 (n - 1) ≤
          degreeUpperBv5 (n := n) g u + degreeUpperBv5 (n := n) g v := by
        exact (Bool.and_eq_true.mp (by simpa using hleg)).2
      exact (bv5_threshold_iff (n := n) hn (g := g) (u := u) (v := v)).1 hBv
    exact ⟨by simpa using hnotAdj, hCond⟩
  · rintro ⟨hnotAdj, hcond⟩
    have hBv :
        BitVec.ofNat 5 (n - 1) ≤
          degreeUpperBv5 (n := n) g u + degreeUpperBv5 (n := n) g v := by
      exact (bv5_threshold_iff (n := n) hn (g := g) (u := u) (v := v)).2 hcond
    refine ⟨(u, v), mem_upperPairs_iff.mpr ⟨hv, huv⟩, by simp [t], ?_⟩
    simp [hnotAdj, hBv]
