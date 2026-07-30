import FormalConjecturesUtil
import WOWII217SpanningTree
import Mathlib.Combinatorics.SimpleGraph.Hamiltonian

/-!
# Hamiltonian Path for Ls ≤ 2
This module provides the final global proof that Ls G ≤ 2 implies G contains a Hamiltonian path.
-/

open Classical SimpleGraph WOWII217SpanningTree

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem exists_hamiltonianPath_of_Ls_le_two (G : SimpleGraph V) [DecidableRel G.Adj]
    [Nontrivial V] (connected : G.Connected) (hL : Ls G ≤ 2) :
    ∃ a b, ∃ p : G.Walk a b, p.IsHamiltonian := by
  obtain ⟨v0, _⟩ := exists_pair_ne V
  have hT := exists_spanningTree_preserving_degree G connected v0
  obtain ⟨T, hspanning, htree, _hdeg⟩ := hT
  have hLsT : spanningLeafCount T ≤ 2 := by
    have h1 : (spanningLeafCount T : ℝ) ≤ Ls G := spanningTree_leafCount_le_Ls G T hspanning htree
    exact_mod_cast h1.trans hL
  have hTleaves_ge_2 : 2 ≤ spanningLeafCount T := spanningTree_two_le_leafCount T hspanning htree
  have hTleaves : spanningLeafCount T = 2 := by omega
  have hfilter : (T.verts.toFinset.filter fun (w : V) => T.degree w = 1).card = 2 := hTleaves
  rw [Finset.card_eq_two] at hfilter
  obtain ⟨a, b, hab, hset⟩ := hfilter
  have ha1 : T.degree a = 1 := by
    have ha_in : a ∈ ({a, b} : Finset V) := by simp
    rw [← hset, Finset.mem_filter, Set.mem_toFinset] at ha_in
    exact ha_in.2
  have hb1 : T.degree b = 1 := by
    have hb_in : b ∈ ({a, b} : Finset V) := by simp
    rw [← hset, Finset.mem_filter, Set.mem_toFinset] at hb_in
    exact hb_in.2
  have hTdeg : ∀ v : T.verts, T.coe.degree v ≤ 2 := by
    intro v
    have hd := spanningTree_degree_le_leafCount T hspanning htree v.val
    have h1 := hd.trans (by omega : spanningLeafCount T ≤ 2)
    rw [Subgraph.coe_degree T v]
    convert h1
  have Tconn : T.coe.Connected := htree.isConnected
  have ha_vert : a ∈ T.verts := by
    have ha_in : a ∈ ({a, b} : Finset V) := by simp
    rw [← hset, Finset.mem_filter, Set.mem_toFinset] at ha_in
    exact ha_in.1
  have hb_vert : b ∈ T.verts := by
    have hb_in : b ∈ ({a, b} : Finset V) := by simp
    rw [← hset, Finset.mem_filter, Set.mem_toFinset] at hb_in
    exact hb_in.1
  let a_v : T.verts := ⟨a, ha_vert⟩
  let b_v : T.verts := ⟨b, hb_vert⟩
  have hab_v : a_v ≠ b_v := fun h => hab (congr_arg Subtype.val h)
  have ha1_v : T.coe.degree a_v = 1 := by
    rw [Subgraph.coe_degree T a_v]
    convert ha1
  have hb1_v : T.coe.degree b_v = 1 := by
    rw [Subgraph.coe_degree T b_v]
    convert hb1
  obtain ⟨p', hp'⟩ := (Tconn.preconnected a_v b_v).exists_isPath
  have T_ham : p'.IsHamiltonian := by
    apply isHamiltonian_of_path_degree_le_two T.coe Tconn hp' hab_v
    · convert ha1_v
    · convert hb1_v
    · intro v; convert hTdeg v
  have h_bij : Function.Bijective T.hom := by
    constructor
    · intro x y hxy
      exact Subtype.ext hxy
    · intro y
      have hy : y ∈ T.verts := hspanning.verts_eq_univ ▸ Set.mem_univ y
      exact ⟨⟨y, hy⟩, rfl⟩
  exact ⟨a, b, p'.map T.hom, T_ham.map T.hom h_bij⟩
