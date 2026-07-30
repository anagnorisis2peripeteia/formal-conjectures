import WOWII217Closure
import WOWII217ClosureSemantics

namespace L7

open WOWII217FiniteBase WOWII217Closure

/-- One `setBit` seen at an arbitrary bit position. -/
theorem getLsbD_setBit {w : Nat} (x : BitVec w) (i : Nat) (b : Bool) (j : Nat) (hj : j < w) :
    (setBit x i b).getLsbD j = (x.getLsbD j || (b && decide (i = j))) := by
  simp only [setBit, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_twoPow, hj,
    decide_true, bitMask, BitVec.getLsbD_cast, BitVec.getLsbD_replicate,
    Nat.one_mul, Bool.true_and, Nat.mod_one, BitVec.getLsbD_ofBool]
  by_cases hij : i = j
  · subst hij; simp [hj]
  · simp [hij]

/-- Folding `setBit` over a list: bit `k` is the OR of the initial bit with every
`f q` whose index hits `k`. No injectivity or `Nodup` needed. -/
theorem foldl_setBit_getLsbD {w : Nat} (idx : Nat × Nat → Nat) (f : Nat × Nat → Bool)
    (k : Nat) (hk : k < w) :
    ∀ (xs : List (Nat × Nat)) (init : BitVec w),
      (xs.foldl (fun acc q => setBit acc (idx q) (f q)) init).getLsbD k
        = (init.getLsbD k || xs.any (fun q => f q && decide (idx q = k))) := by
  intro xs
  induction xs with
  | nil => intro init; simp
  | cons q rest ih =>
      intro init
      simp only [List.foldl_cons, ih, getLsbD_setBit _ _ _ _ hk, List.any_cons]
      cases h : init.getLsbD k <;>
        cases hf : f q <;>
        by_cases hidx : idx q = k <;>
        simp [h, hf, hidx, Bool.or_assoc, Bool.or_comm, Bool.or_left_comm]


/-- `v * (v-1)` is always even, so the triangular number is exact. -/
theorem two_dvd_mul_pred (v : Nat) : 2 ∣ v * (v - 1) := by
  rcases Nat.even_or_odd v with he | ho
  · exact Dvd.dvd.mul_right he.two_dvd _
  · have h : 2 ∣ (v - 1) := by rcases ho with ⟨k, hk⟩; omega
    exact Dvd.dvd.mul_left h _

theorem two_mul_tri (v : Nat) : 2 * (v * (v - 1) / 2) = v * (v - 1) :=
  Nat.mul_div_cancel' (two_dvd_mul_pred v)

/-- `upperIndex u v = v(v-1)/2 + u` is injective on pairs with `u < v`. -/
theorem upperIndex_inj {u v u' v' : Nat} (h : u < v) (h' : u' < v')
    (heq : upperIndex u v = upperIndex u' v') : u = u' ∧ v = v' := by
  unfold upperIndex at heq
  have e1 := two_mul_tri v
  have e2 := two_mul_tri v'
  rcases lt_trichotomy v v' with hv | hv | hv
  · exfalso
    have hmul : v * (v - 1) + 2 * v ≤ v' * (v' - 1) := by
      have : v + 1 ≤ v' := hv
      nlinarith [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (by omega : v ≠ 0)),
                 Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (by omega : v' ≠ 0))]
    omega
  · subst hv; exact ⟨by omega, rfl⟩
  · exfalso
    have hmul : v' * (v' - 1) + 2 * v' ≤ v * (v - 1) := by
      have : v' + 1 ≤ v := hv
      nlinarith [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (by omega : v' ≠ 0)),
                 Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (by omega : v ≠ 0))]
    omega


/-- Membership in `upperPairs`. -/
theorem mem_upperPairs {n u v : Nat} : (u, v) ∈ upperPairs n ↔ u < v ∧ v < n := by
  unfold upperPairs
  simp only [List.mem_flatMap, List.mem_map, List.mem_range, Prod.mk.injEq]
  constructor
  · rintro ⟨w, hw, x, hx, hxu, hwv⟩
    subst hxu; subst hwv; exact ⟨hx, hw⟩
  · rintro ⟨huv, hvn⟩
    exact ⟨v, hvn, u, huv, rfl, rfl⟩

/-- L7. What `pathClosureParallelMask` actually contains: exactly the eligible edges. -/
theorem getLsbD_mask {n : Nat} (g : BitVec (edgeCount n)) (u v : Nat)
    (huv : u < v) (hvn : v < n) (hlt : upperIndex u v < edgeCount n) :
    (pathClosureParallelMask (n := n) g).getLsbD (upperIndex u v)
      = (!adjUpper g u v &&
          (BitVec.ofNat 5 (n - 1) ≤ degreeUpperBv5 g u + degreeUpperBv5 g v)) := by
  unfold pathClosureParallelMask
  rw [foldl_setBit_getLsbD (fun e => upperIndex e.1 e.2)
        (fun e => !adjUpper g e.1 e.2 &&
          (BitVec.ofNat 5 (n - 1) ≤ degreeUpperBv5 g e.1 + degreeUpperBv5 g e.2))
        _ hlt]
  rw [show (BitVec.zero (edgeCount n)).getLsbD (upperIndex u v) = false by simp,
    Bool.false_or]
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨q, hq, hfq⟩
    obtain ⟨⟨hnadj, hdeg⟩, hidx⟩ := hfq
    obtain ⟨hq1, hq2⟩ := mem_upperPairs.mp (by simpa using hq)
    obtain ⟨rfl, rfl⟩ := upperIndex_inj hq1 huv hidx
    exact ⟨hnadj, hdeg⟩
  · intro hleg
    exact ⟨(u, v), mem_upperPairs.mpr ⟨huv, hvn⟩, hleg, rfl⟩

end L7


