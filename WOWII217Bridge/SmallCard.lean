import WOWII217BondyChvatal
import WOWII217Ore

namespace SmallCard

open SimpleGraph WOWII217BondyChvatal WOWII217Ore

/-- A connected graph on at most 3 vertices is traceable.

This is the obligation of the `_` catch-all arm in `WOWII217SmallNExceptions`: the match
covers `card V = 4 .. 12`, and `hCard12 : card V ≤ 12`, so the fallthrough is `card V ≤ 3`.
`G.Connected` supplies `Nonempty V`, so the empty case cannot arise. -/
theorem traceable_of_card_le_three {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (conn : G.Connected)
    (hcard : Fintype.card V ≤ 3) : Traceable G := by
  classical
  have hne : Nonempty V := conn.nonempty
  -- a connected graph on <= 3 vertices has a Hamiltonian path: minDegree is large enough
  have hmin : Fintype.card V - 1 ≤ 2 * G.minDegree := by
    rcases Nat.lt_or_ge (Fintype.card V) 2 with h | h
    · omega
    · have h2 : 1 ≤ G.minDegree := by
        rw [Nat.one_le_iff_ne_zero]
        intro hzero
        obtain ⟨v, hv⟩ := G.exists_minimal_degree_vertex
        have hdeg : G.degree v = 0 := by omega
        have : ∀ w, w ≠ v → ¬ G.Reachable v w := by
          intro w hw hreach
          obtain ⟨p⟩ := hreach
          cases p with
          | nil => exact hw rfl
          | cons hadj _ =>
              have : v ∈ G.neighborFinset v ∨ True := Or.inr trivial
              rw [← SimpleGraph.card_neighborFinset_eq_degree] at hdeg
              have hmem : _ ∈ G.neighborFinset v := SimpleGraph.mem_neighborFinset .. |>.mpr hadj
              simp [Finset.card_eq_zero.mp hdeg] at hmem
        obtain ⟨w, hw⟩ := Fintype.exists_ne_of_one_lt_card (by omega) v
        exact this w hw (conn.preconnected v w)
      omega
  by_cases h1 : Fintype.card V ≤ 1
  · -- a single vertex: the nil walk is Hamiltonian
    obtain ⟨v⟩ := hne
    refine ⟨v, v, SimpleGraph.Walk.nil, ?_⟩
    have : ∀ w : V, w = v := by
      intro w
      have := Fintype.card_le_one_iff.mp h1 w v
      exact this
    simp [SimpleGraph.Walk.IsHamiltonian, this]
  · haveI : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
    exact traceable_of_minDegree_half G hmin

end SmallCard

