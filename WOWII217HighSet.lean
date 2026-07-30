/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Card
import WOWII217Chvatal
import WOWII217Ore
import WOWII217Mid13
import WOWII217ClosureSemantics

/-!
# High Set closure

Extracted lemmas for generalized high-set path-closure.
-/

namespace WOWII217HighSet

open Classical SimpleGraph Finset
open WOWII217BondyChvatal
open WOWII217Chvatal
open WOWII217ClosureSemantics
open WOWII217Mid13
open WOWII217Ore

variable {V : Type*} [Fintype V] [DecidableEq V]

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

end WOWII217HighSet
