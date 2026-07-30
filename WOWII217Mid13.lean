import WOWII217Chvatal
import WOWII217Ore

/-!
# Order-13 mid residual sequences

The five non-residual, non-6-regular residue-2 sequences on 13 vertices each
have at least nine degree-6 vertices and minimum degree ≥ 4.  Path-closure
adds every missing edge among degree-6 vertices in round 1 (`6+6 ≥ 12`).  Those
vertices then have degree ≥ 8, so round 2 joins them to every remaining vertex.
Every vertex then has degree ≥ 8, so round 3 is Ore-complete.  Traceability of
the path-closure transfers back to the original graph.
-/

namespace WOWII217Mid13

open Classical SimpleGraph Finset
open WOWII217Chvatal
open WOWII217Ore
open WOWII217BondyChvatal
open WOWII217ClosureSemantics

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem pathClosureRound_adj_of_degree_sum
    (G : SimpleGraph V) [DecidableRel G.Adj] {u v : V}
    (hne : u ≠ v)
    (hsum : Fintype.card V - 1 ≤ G.degree u + G.degree v) :
    (pathClosureRound G).Adj u v := by
  classical
  simp only [pathClosureRound]
  rw [adj_addEligibleEdgesFrom_iff]
  refine Or.inr ⟨(u, v), mem_allDistinctPairs hne, ?_, ?_⟩
  · convert hsum
  · simp [SimpleGraph.edge, SimpleGraph.fromEdgeSet_adj, hne]

theorem pathClosureRound_adj_of_two_deg_six
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn : Fintype.card V = 13) {u v : V} (hne : u ≠ v)
    (hu : G.degree u = 6) (hv : G.degree v = 6) :
    (pathClosureRound G).Adj u v := by
  apply pathClosureRound_adj_of_degree_sum G hne
  simp [hn, hu, hv]

theorem degree_pathClosureRound_ge_card_S_sub_one
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn : Fintype.card V = 13)
    (x : V) (hx : G.degree x = 6)
    (hS : 9 ≤ card (univ.filter fun v : V => G.degree v = 6)) :
    card (univ.filter fun v : V => G.degree v = 6) - 1 ≤
      (pathClosureRound G).degree x := by
  classical
  let S : Finset V := univ.filter fun v => G.degree v = 6
  have hxS : x ∈ S := mem_filter.mpr ⟨mem_univ x, hx⟩
  have hsub : S.erase x ⊆ (pathClosureRound G).neighborFinset x := by
    intro y hy
    obtain ⟨hyx, hyS⟩ := mem_erase.mp hy
    have hy6 : G.degree y = 6 := (mem_filter.mp hyS).2
    rw [mem_neighborFinset]
    exact pathClosureRound_adj_of_two_deg_six G hn (Ne.symm hyx) hx hy6
  have hcard : card (S.erase x) = card S - 1 := card_erase_of_mem hxS
  have := card_le_card hsub
  rwa [hcard, (pathClosureRound G).card_neighborFinset_eq_degree] at this

theorem degree_pathClosureRound_ge_eight
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn : Fintype.card V = 13)
    (x : V) (hx : G.degree x = 6)
    (hS : 9 ≤ card (univ.filter fun v : V => G.degree v = 6)) :
    8 ≤ (pathClosureRound G).degree x := by
  have := degree_pathClosureRound_ge_card_S_sub_one G hn x hx hS
  omega

theorem pathClosureRound_adj_high_to_low
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn : Fintype.card V = 13)
    (hS : 9 ≤ card (univ.filter fun v : V => G.degree v = 6))
    {u v : V} (hne : u ≠ v)
    (hu : G.degree u = 6) (hv : 4 ≤ G.degree v) :
    (pathClosureRound (pathClosureRound G)).Adj u v := by
  classical
  let G1 := pathClosureRound G
  have hu1 : 8 ≤ G1.degree u := degree_pathClosureRound_ge_eight G hn u hu hS
  have hv1 : G.degree v ≤ G1.degree v := G.degree_le_of_le (le_pathClosureRound G)
  have hsum : Fintype.card V - 1 ≤ G1.degree u + G1.degree v := by
    rw [hn]; omega
  exact pathClosureRound_adj_of_degree_sum G1 hne hsum

theorem pathClosureIter_three_eq_top_of_nine_deg_six
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn : Fintype.card V = 13)
    (hmax : G.maxDegree ≤ 6)
    (hmin : 4 ≤ G.minDegree)
    (hS : 9 ≤ card (univ.filter fun v : V => G.degree v = 6)) :
    pathClosureIter G 3 = (⊤ : SimpleGraph V) := by
  classical
  let S : Finset V := univ.filter fun w => G.degree w = 6
  let G1 := pathClosureRound G
  let G2 := pathClosureRound G1
  let G3 := pathClosureRound G2
  change G3 = ⊤
  have hS_deg1 : ∀ x ∈ S, 8 ≤ G1.degree x := by
    intro x hx
    exact degree_pathClosureRound_ge_eight G hn x (mem_filter.mp hx).2 hS
  have hS_to_all : ∀ x y : V, x ∈ S → y ∉ S → x ≠ y → G2.Adj x y := by
    intro x y hx hy hxy
    have hx6 : G.degree x = 6 := (mem_filter.mp hx).2
    have hyge : 4 ≤ G.degree y := hmin.trans (G.minDegree_le_degree y)
    exact pathClosureRound_adj_high_to_low G hn hS hxy hx6 hyge
  have hdeg2 : ∀ w : V, 8 ≤ G2.degree w := by
    intro w
    by_cases hwS : w ∈ S
    · exact (hS_deg1 w hwS).trans (G1.degree_le_of_le (le_pathClosureRound G1))
    · have hsub' : S ⊆ G2.neighborFinset w := by
        intro x hx
        have hxw : x ≠ w := by intro rfl; exact hwS hx
        have hadj := hS_to_all x w hx hwS hxw
        simpa [mem_neighborFinset, G2.adj_comm] using hadj
      have hle : card S ≤ card (G2.neighborFinset w) := card_le_card hsub'
      have hle' : card S ≤ G2.degree w := by
        rwa [G2.card_neighborFinset_eq_degree] at hle
      exact Nat.le_trans (by decide : 8 ≤ 9) (hS.trans hle')
  ext u v
  constructor
  · exact fun h => Adj.ne h
  · intro hTop
    have hne : u ≠ v := by simpa [top_adj] using hTop
    apply pathClosureRound_adj_of_degree_sum G2 hne
    rw [hn]
    have hu := hdeg2 u
    have hv := hdeg2 v
    omega

theorem traceable_of_nine_deg_six_card_thirteen [Nontrivial V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn : Fintype.card V = 13)
    (hmax : G.maxDegree ≤ 6)
    (hmin : 4 ≤ G.minDegree)
    (hS : 9 ≤ card (univ.filter fun v : V => G.degree v = 6)) :
    Traceable G := by
  classical
  have hTop := pathClosureIter_three_eq_top_of_nine_deg_six G hn hmax hmin hS
  have hTrace : Traceable (pathClosureIter G 3) := by
    rw [hTop]
    exact traceable_top
  exact (traceable_pathClosureIter_iff G 3).mp hTrace

theorem card_filter_deg_eq_list_count
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : List ℕ)
    (hs : (Finset.univ.val.map fun v : V => G.degree v).sort (· ≥ ·) = s) :
    card (univ.filter fun v : V => G.degree v = 6) = List.count 6 s := by
  classical
  have hcoe :
      Multiset.map (fun v : V => G.degree v) Finset.univ.val = (↑s : Multiset ℕ) := by
    have h :=
      Multiset.sort_eq
        (Finset.univ.val.map fun v : V => G.degree v) (· ≥ ·)
    -- h : ↑(sort (map) (≥)) = map
    simpa [hs] using h.symm
  have hcnt :
      (Multiset.map (fun v : V => G.degree v) Finset.univ.val).count 6 =
        List.count 6 s := by
    rw [hcoe, Multiset.coe_count]
  have hmap := Multiset.count_map (fun v : V => G.degree v) Finset.univ.val (b := 6)
  rw [← hcnt, hmap]
  simp [Finset.filter, Finset.card, eq_comm]

end WOWII217Mid13
