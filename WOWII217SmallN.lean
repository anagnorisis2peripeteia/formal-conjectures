import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Data.Finset.Card
import WOWII217Chvatal
import WOWII217Ore
import WOWII217SmallNExceptions
import WOWII217Mid13
import WOWII217Cubic8
import WOWII217Regular10

/-!
# Order ≤ 12 residual exceptions under residue = 2

Under `residue = 2`, `maxDegree ≤ 6`, not Ore-half, and not Chvátal-path, residual
graphs on `n ≤ 12` vertices fall into:

1. **Stuck regulars** (`2 · maxDegree < n - 1`): path-closure adds nothing.
   Connected residue-2 realisations are 2-regular-6, 3-regular-8, 4-regular-10,
   and 5-regular-12 (the last already certified).

2. **Non-stuck** (`2 · maxDegree ≥ n - 1`): high-degree pairs are path-closure
   eligible.  When the high set is large enough, the Mid13 three-round cascade
   produces the complete graph.
-/

namespace WOWII217SmallN

open Classical SimpleGraph Finset
open WOWII217BondyChvatal
open WOWII217Chvatal
open WOWII217Ore
open WOWII217Mid13
open WOWII217ClosureSemantics
open WOWII217Cubic8
open WOWII217Regular10

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Connected 2-regular ⇒ traceable -/

theorem isCycles_of_isRegularOfDegree_two
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hReg : G.IsRegularOfDegree 2) :
    G.IsCycles := by
  intro v _hv
  have hdeg : G.degree v = 2 := hReg v
  -- `degree v = #(neighborFinset v) = (neighborSet v).ncard`
  have hcard : (G.neighborSet v).ncard = G.degree v := by
    rw [Set.ncard_eq_toFinset_card (G.neighborSet v)]
    simp [SimpleGraph.neighborFinset, SimpleGraph.degree]
  rwa [hcard]

/-- Connected 2-regular graphs are Hamiltonian-cyclic, hence traceable.

`IsCycles` + connectedness ⇒ a single cycle through every vertex
(`IsCycles.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp`); the tail of
that cycle is a Hamiltonian path. -/
theorem traceable_of_connected_isRegularOfDegree_two
    [Nontrivial V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (connected : G.Connected)
    (hReg : G.IsRegularOfDegree 2) :
    Traceable G := by
  classical
  obtain ⟨u⟩ := connected.nonempty
  have hCycG : G.IsCycles := isCycles_of_isRegularOfDegree_two G hReg
  have hne : (G.neighborSet u).Nonempty :=
    G.degree_pos_iff_nonempty.mp (by have := hReg u; omega)
  have huniv : (G.connectedComponentMk u).supp = (Set.univ : Set V) := by
    ext v
    constructor
    · intro; trivial
    · intro
      rw [ConnectedComponent.mem_supp_iff, ConnectedComponent.eq]
      exact connected.preconnected v u
  obtain ⟨p, hp, hverts⟩ :=
    IsCycles.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp
      (G := G) (v := u) (c := G.connectedComponentMk u) hCycG
      (by simp [ConnectedComponent.mem_supp_iff]) hne
  have hvertsU : p.toSubgraph.verts = Set.univ := hverts.trans huniv
  have hmem : ∀ w : V, w ∈ p.support := by
    intro w
    have : w ∈ p.toSubgraph.verts := by rw [hvertsU]; trivial
    simpa [Walk.mem_verts_toSubgraph] using this
  have hHamCyc : p.IsHamiltonianCycle := by
    refine (Walk.isHamiltonianCycle_iff_isCycle_and_support_count_tail_eq_one).2 ⟨hp, ?_⟩
    intro a
    have ha : a ∈ p.support := hmem a
    have hcons : p.support = u :: p.support.tail := p.support_eq_cons
    by_cases ha0 : a = u
    · subst a
      have h2 : p.support.count u = 2 := hp.count_support
      rw [hcons, List.count_cons_self] at h2
      omega
    · have h1 : p.support.count a = 1 := hp.count_support_of_mem ha ha0
      rw [hcons, List.count_cons_of_ne (Ne.symm ha0)] at h1
      exact h1
  refine ⟨p.getVert 1, u, p.tail, hHamCyc.isHamiltonian_tail⟩

theorem hamiltonian_of_two_regular
    [Nontrivial V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (connected : G.Connected)
    (hReg : ∀ v : V, G.degree v = 2) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian :=
  traceable_of_connected_isRegularOfDegree_two G connected hReg

/-! ## Generalised high-set path-closure (Mid13-style) -/

theorem pathClosureRound_adj_of_two_high
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (t : ℕ) (ht : Fintype.card V - 1 ≤ 2 * t)
    {u v : V} (hne : u ≠ v)
    (hu : t ≤ G.degree u) (hv : t ≤ G.degree v) :
    (pathClosureRound G).Adj u v := by
  apply pathClosureRound_adj_of_degree_sum G hne
  omega

theorem degree_pathClosureRound_ge_card_S_sub_one_high
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (t : ℕ) (ht : Fintype.card V - 1 ≤ 2 * t)
    (S : Finset V) (hSdef : S = univ.filter fun v => t ≤ G.degree v)
    (x : V) (hx : x ∈ S) :
    card S - 1 ≤ (pathClosureRound G).degree x := by
  classical
  have hxS : t ≤ G.degree x := by
    rw [hSdef] at hx
    exact (mem_filter.mp hx).2
  have hsub : S.erase x ⊆ (pathClosureRound G).neighborFinset x := by
    intro y hy
    obtain ⟨hyx, hyS⟩ := mem_erase.mp hy
    have hydeg : t ≤ G.degree y := by
      rw [hSdef] at hyS
      exact (mem_filter.mp hyS).2
    rw [mem_neighborFinset]
    exact pathClosureRound_adj_of_two_high G t ht (Ne.symm hyx) hxS hydeg
  have hcard : card (S.erase x) = card S - 1 := card_erase_of_mem hx
  have := card_le_card hsub
  rwa [hcard, (pathClosureRound G).card_neighborFinset_eq_degree] at this

/-- Mid13 cascade at a general high-degree threshold `t`. -/
theorem pathClosureIter_three_eq_top_of_high_set
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (t : ℕ) (ht : Fintype.card V - 1 ≤ 2 * t)
    (hOut : ∀ v : V, ¬ t ≤ G.degree v →
      Fintype.card V - 1 -
          (card (univ.filter fun w => t ≤ G.degree w) - 1) ≤ G.degree v)
    (hCard : Fintype.card V - 1 ≤
        2 * (card (univ.filter fun v : V => t ≤ G.degree v) - 1))
    (hSpos : 1 ≤ card (univ.filter fun v : V => t ≤ G.degree v)) :
    pathClosureIter G 3 = (⊤ : SimpleGraph V) := by
  classical
  let S : Finset V := univ.filter fun w => t ≤ G.degree w
  let G1 := pathClosureRound G
  let G2 := pathClosureRound G1
  let G3 := pathClosureRound G2
  change G3 = ⊤
  have hS_eq : S = univ.filter fun w => t ≤ G.degree w := rfl
  have hS_deg1 : ∀ x ∈ S, card S - 1 ≤ G1.degree x := fun x hx =>
    degree_pathClosureRound_ge_card_S_sub_one_high G t ht S hS_eq x hx
  have hS_to_all : ∀ x y : V, x ∈ S → y ∉ S → x ≠ y → G2.Adj x y := by
    intro x y hx hy hxy
    have hx1 : card S - 1 ≤ G1.degree x := hS_deg1 x hx
    have hy0 : G.degree y ≤ G1.degree y := G.degree_le_of_le (le_pathClosureRound G)
    have hydeg :
        Fintype.card V - 1 - (card S - 1) ≤ G.degree y := by
      have hnot : ¬ t ≤ G.degree y := by
        intro ht'
        exact hy (by simp [S, ht'])
      simpa [S] using hOut y hnot
    have hsum : Fintype.card V - 1 ≤ G1.degree x + G1.degree y := by
      have : Fintype.card V - 1 - (card S - 1) ≤ G1.degree y := hydeg.trans hy0
      -- Need card S ≥ 1 so subtraction is well-behaved
      have hpos : 1 ≤ card S := by simpa [S] using hSpos
      omega
    exact pathClosureRound_adj_of_degree_sum G1 hxy hsum
  have hdeg2 : ∀ w : V, card S - 1 ≤ G2.degree w := by
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
      have hpos : 1 ≤ card S := by simpa [S] using hSpos
      omega
  have hOre : Fintype.card V - 1 ≤ 2 * (card S - 1) := by simpa [S] using hCard
  have hpos : 1 ≤ card S := by simpa [S] using hSpos
  ext u v
  constructor
  · exact fun h => Adj.ne h
  · intro hTop
    have hne : u ≠ v := by simpa [top_adj] using hTop
    apply pathClosureRound_adj_of_degree_sum G2 hne
    have hu := hdeg2 u
    have hv := hdeg2 v
    -- 2 * (card S - 1) ≤ deg u + deg v and n - 1 ≤ 2 * (card S - 1)
    have hsum : 2 * (card S - 1) ≤ G2.degree u + G2.degree v := by omega
    omega

theorem hamiltonian_of_high_set_path_closure
    [Nontrivial V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (t : ℕ) (ht : Fintype.card V - 1 ≤ 2 * t)
    (hOut : ∀ v : V, ¬ t ≤ G.degree v →
      Fintype.card V - 1 -
          (card (univ.filter fun w => t ≤ G.degree w) - 1) ≤ G.degree v)
    (hCard : Fintype.card V - 1 ≤
        2 * (card (univ.filter fun v : V => t ≤ G.degree v) - 1))
    (hSpos : 1 ≤ card (univ.filter fun v : V => t ≤ G.degree v)) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  have hTop := pathClosureIter_three_eq_top_of_high_set G t ht hOut hCard hSpos
  have hTrace : Traceable (pathClosureIter G 3) := by
    rw [hTop]
    exact traceable_top
  exact (traceable_pathClosureIter_iff G 3).mp hTrace

/-! ## Classification entry for n ≤ 12 -/

/-- Residual n≤12 entry point.

Stuck regulars:
* 2-regular (any order under stuck) — cycle theorem;
* 3-regular order 8 — Held–Karp cubic certificate (`WOWII217Cubic8`);
* 4-regular order 10 — Held–Karp certificate (in progress);
* 5-regular order 12 — already excluded by `hNotFive12`.

Open bulk tail: non-stuck residual sequences whose high set is too small for
the three-round cascade.
-/
theorem hamiltonian_of_residue_eq_two_card_le_twelve
    [Nontrivial V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (connected : G.Connected)
    (_hResidue : residue G = 2)
    (hMaxDeg : G.maxDegree ≤ 6)
    (hn : Fintype.card V ≤ 12)
    (hNotHalf : ¬ Fintype.card V - 1 ≤ 2 * G.minDegree)
    (_hNotChv : ¬ MeetsChvatalPath G)
    (hNotFive12 : ¬ (Fintype.card V = 12 ∧ ∀ v : V, G.degree v = 5)) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  by_cases hStuck : 2 * G.maxDegree < Fintype.card V - 1
  · by_cases h2 : G.IsRegularOfDegree 2
    · exact hamiltonian_of_two_regular G connected h2
    · by_cases h5 : Fintype.card V = 12 ∧ ∀ v : V, G.degree v = 5
      · exact absurd h5 hNotFive12
      · by_cases h3 : Fintype.card V = 8 ∧ G.IsRegularOfDegree 3
        · exact hamiltonian_of_order8_three_regular G h3.1 connected h3.2
        · by_cases h4 : Fintype.card V = 10 ∧ G.IsRegularOfDegree 4
          · -- 4-regular-10 Held–Karp certificate
            exact hamiltonian_of_order10_four_regular G h4.1 connected h4.2
          · -- Stuck non-regular residue-2 classes are empty (force regular).
            exact WOWII217SmallNExceptions.exception_stuck_non_regular G hn _hResidue hStuck h2 h3 h4
  · let t : ℕ := Fintype.card V / 2
    have ht : Fintype.card V - 1 ≤ 2 * t := by
      dsimp [t]; omega
    let S := univ.filter fun v : V => t ≤ G.degree v
    by_cases hBig :
        Fintype.card V - 1 ≤ 2 * (card S - 1) ∧ 1 ≤ card S
    · by_cases hOutOK :
          ∀ v : V, ¬ t ≤ G.degree v →
            Fintype.card V - 1 - (card S - 1) ≤ G.degree v
      · exact hamiltonian_of_high_set_path_closure G t ht
          (by simpa [S] using hOutOK)
          (by simpa [S] using hBig.1)
          (by simpa [S] using hBig.2)
      · exact WOWII217SmallNExceptions.exception_not_hOutOK G hn _hResidue t S (by intro v; simp [S]) hBig hOutOK
    · exact WOWII217SmallNExceptions.exception_not_hBig G hn _hResidue t S (by intro v; simp [S]) hBig

end WOWII217SmallN
