import WOWII217Bridge.ChvBridge

/-!
Regular-degree-sequence residuals in the `SmallNExceptions` `else` branches.

The caller instantiates `t := card V / 2`, so `t` satisfies both
`card V - 1 <= 2 * t` and `2 * t <= card V`.  Passing the upper bound as well pins
`t` tightly enough that a regular graph forces `S = univ`, which makes the `hBig`
condition TRUE — contradicting the `hNotBig` hypothesis of the residual branch.
This is why no Held-Karp certificate is needed for 4-regular-on-9 or 2-regular-on-5.
-/

namespace RegCase

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A constant descending degree list makes every vertex degree equal to that constant. -/
theorem degree_eq_of_descSort_const (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ}
    (h : ∀ d ∈ (univ.val.map fun v : V => G.degree v).sort (· ≥ ·), d = k) :
    ∀ v, G.degree v = k := by
  classical
  intro v
  refine h _ ?_
  rw [← Multiset.mem_coe, ChvBridge.descSort_multiset, Multiset.mem_map]
  exact ⟨v, Finset.mem_val.mpr (Finset.mem_univ v), rfl⟩

/-- If every vertex has degree `k` and `t <= k`, the high-degree set is everything. -/
theorem set_eq_univ_of_regular (G : SimpleGraph V) [DecidableRel G.Adj] {t k : ℕ}
    {S : Finset V} (hS : ∀ v, v ∈ S ↔ t ≤ G.degree v)
    (hk : ∀ v, G.degree v = k) (hkt : t ≤ k) : S = univ := by
  classical
  apply Finset.eq_univ_of_forall
  intro v
  exact (hS v).mpr (by rw [hk v]; exact hkt)

/-- THE KEY LEMMA: a regular graph satisfies `hBig`, contradicting `hNotBig`. -/
theorem big_of_regular (G : SimpleGraph V) [DecidableRel G.Adj] {t k : ℕ}
    {S : Finset V} (hS : ∀ v, v ∈ S ↔ t ≤ G.degree v)
    (hk : ∀ v, G.degree v = k) (hkt : t ≤ k) (hne : 1 ≤ Fintype.card V) :
    Fintype.card V - 1 ≤ 2 * (S.card - 1) ∧ 1 ≤ S.card := by
  classical
  have hU : S = univ := set_eq_univ_of_regular G hS hk hkt
  have hcard : S.card = Fintype.card V := by rw [hU]; exact Finset.card_univ
  rw [hcard]
  omega

/-- A regular graph's max degree is the common degree. Lets `omega` connect the
`hNotStuck` hypothesis (`card V - 1 <= 2 * maxDegree`) to the constant degree `k`. -/
theorem maxDegree_eq_of_regular (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ}
    [Nonempty V] (hk : ∀ v, G.degree v = k) : G.maxDegree = k := by
  classical
  refine le_antisymm ?_ ?_
  · refine G.maxDegree_le_of_forall_degree_le k (fun v => by rw [hk v])
  · obtain ⟨v⟩ := ‹Nonempty V›
    have := G.degree_le_maxDegree v
    rw [hk v] at this
    exact this

/-- Regular graphs satisfy the `outOK` condition vacuously: every vertex has degree
`k >= t`, so the antecedent `¬ t <= degree v` never fires. -/
theorem outOK_of_regular (G : SimpleGraph V) [DecidableRel G.Adj] {t k m : ℕ}
    (hk : ∀ v, G.degree v = k) (hkt : t ≤ k) :
    ∀ v : V, ¬ t ≤ G.degree v → m ≤ G.degree v := by
  intro v hv
  exact absurd (by rw [hk v]; exact hkt) hv

/-! ### Min-degree forms

The regular lemmas above only need a LOWER bound on every degree, not equality.
Generalising lets the same argument handle non-regular residuals such as
`[6,6,6,6,4,4,4,4,4,4]` on 10 vertices, where every degree is at least 4. -/

/-- If every degree is at least `k` and `t <= k`, the high-degree set is everything. -/
theorem set_eq_univ_of_min_degree (G : SimpleGraph V) [DecidableRel G.Adj] {t k : ℕ}
    {S : Finset V} (hS : ∀ v, v ∈ S ↔ t ≤ G.degree v)
    (hk : ∀ v, k ≤ G.degree v) (hkt : t ≤ k) : S = univ := by
  classical
  exact Finset.eq_univ_of_forall fun v => (hS v).mpr (le_trans hkt (hk v))

/-- Min-degree form of `big_of_regular`. -/
theorem big_of_min_degree (G : SimpleGraph V) [DecidableRel G.Adj] {t k : ℕ}
    {S : Finset V} (hS : ∀ v, v ∈ S ↔ t ≤ G.degree v)
    (hk : ∀ v, k ≤ G.degree v) (hkt : t ≤ k) (hne : 1 ≤ Fintype.card V) :
    Fintype.card V - 1 ≤ 2 * (S.card - 1) ∧ 1 ≤ S.card := by
  classical
  have hcard : S.card = Fintype.card V := by
    rw [set_eq_univ_of_min_degree G hS hk hkt]; exact Finset.card_univ
  rw [hcard]; omega

/-- Min-degree form of `outOK_of_regular`. -/
theorem outOK_of_min_degree (G : SimpleGraph V) [DecidableRel G.Adj] {t k m : ℕ}
    (hk : ∀ v, k ≤ G.degree v) (hkt : t ≤ k) :
    ∀ v : V, ¬ t ≤ G.degree v → m ≤ G.degree v := by
  intro v hv
  exact absurd (le_trans hkt (hk v)) hv

/-- Every degree is at least the last entry of the descending sort. -/
theorem min_degree_of_descSort (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ}
    (h : ∀ d ∈ (univ.val.map fun v : V => G.degree v).sort (· ≥ ·), k ≤ d) :
    ∀ v, k ≤ G.degree v := by
  classical
  intro v
  refine h _ ?_
  rw [← Multiset.mem_coe, ChvBridge.descSort_multiset, Multiset.mem_map]
  exact ⟨v, Finset.mem_val.mpr (Finset.mem_univ v), rfl⟩

end RegCase
