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
import WOWII217HighSet

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
open WOWII217HighSet

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
    (hLs : Ls G ≤ 6)
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
            exact WOWII217SmallNExceptions.exception_stuck_non_regular (G := G) (connected := connected) (hLs := hLs) (hCard := hn) (hResidue := _hResidue) (hMaxDeg := hMaxDeg) (hStuck := hStuck) (hNot2 := h2) (hNot3 := h3) (hNot4 := h4) (hNot5 := hNotFive12)
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
      · exact WOWII217SmallNExceptions.exception_not_hOutOK (G := G) (connected := connected) (hLs := hLs) (hCard := hn) (hResidue := _hResidue) (hMaxDeg := hMaxDeg) (t := t) (S := S) (hS := by intro v; simp [S]) (hBig := hBig) (hNotOutOK := hOutOK) (hT2 := by dsimp [t]; omega) (hNotStuck := hStuck)
    · exact WOWII217SmallNExceptions.exception_not_hBig (G := G) (connected := connected) (hLs := hLs) (hCard := hn) (hResidue := _hResidue) (hMaxDeg := hMaxDeg) (t := t) (S := S) (hS := by intro v; simp [S]) (hNotBig := hBig) (hT2 := by dsimp [t]; omega) (hNotStuck := hStuck)

end WOWII217SmallN
