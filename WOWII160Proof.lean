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

import WOWII2Proof
import FormalConjectures.WrittenOnTheWallII.«160»

/-!
# Development for WOWII Conjecture 160

This file reuses the connected-domination and pendant-attachment construction
from the verified proof of WOWII Conjecture 2.
-/

open Classical SimpleGraph Finset

namespace Gc160Dev

variable {α : Type*} [Fintype α] [DecidableEq α]

noncomputable section

/-- A connected seed whose closed neighborhood has surplus `c` produces a
spanning tree with at least `c` leaves. -/
lemma seed_bound (G : SimpleGraph α) (instD : DecidableRel G.Adj)
    (hG : G.Connected) (H : G.Subgraph) (hH : H.Connected) (c : ℕ)
    (hc : c + H.verts.toFinset.card ≤ (Gc2Dev.cnf G H.verts.toFinset).card) :
    (c : ℝ) ≤ @Ls α _ G instD := by
  obtain ⟨H', hH'c, hH'dom, hH'card⟩ :=
    Gc2Dev.greedy G hG (Fintype.card α) H hH (by omega)
  obtain ⟨T, hsp, htree, hcount⟩ :=
    Gc2Dev.exists_spanning_tree_leaves G H' hH'c hH'dom
  have hleaves : c ≤
      ((Set.toFinset T.verts).filter fun v => T.degree v = 1).card := by
    omega
  exact Gc2Dev.card_leaves_le_Ls G instD T hsp htree c hleaves

omit [Fintype α] in
/-- In a graph with no four-cycle, two distinct vertices have at most one
common neighbor. -/
lemma common_neighbor_unique (G : SimpleGraph α)
    (hC4 : ¬ ∃ v : α, ∃ c : G.Walk v v, c.IsCycle ∧ c.length = 4)
    {a b c d : α} (hac : a ≠ c)
    (hab : G.Adj a b) (hcb : G.Adj c b) (had : G.Adj a d) (hcd : G.Adj c d) :
    b = d := by
  by_contra hbd
  apply hC4
  let w : G.Walk a a :=
    .cons hab (.cons hcb.symm (.cons hcd (.cons had.symm .nil)))
  refine ⟨a, w, ?_, by simp [w]⟩
  simp [w, Walk.isCycle_def, Walk.isTrail_def, hac, hac.symm, hbd,
    hab.ne, hab.ne.symm, hcb.ne.symm, had.ne, had.ne.symm, hcd.ne]

omit [Fintype α] in
/-- A triangle containing `v` consists of `v` and an adjacent pair in its
neighborhood. -/
lemma triangle_through_exists_pair (G : SimpleGraph α) {s : Finset α} {v : α}
    (hs : G.IsNClique 3 s) (hv : v ∈ s) :
    ∃ a b, G.Adj v a ∧ G.Adj v b ∧ G.Adj a b ∧ s = {v, a, b} := by
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := is3Clique_iff.mp hs
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl | rfl
  · exact ⟨b, c, hab, hac, hbc, rfl⟩
  · refine ⟨a, c, hab.symm, hbc, hac, ?_⟩
    ext x
    simp [or_left_comm]
  · refine ⟨a, b, hac.symm, hbc.symm, hab, ?_⟩
    ext x
    simp [or_comm, or_left_comm]

omit [Fintype α] in
/-- A graph with no four-cycle has edge-disjoint triangles. -/
lemma edgeDisjointTriangles_of_no_c4 (G : SimpleGraph α)
    (hC4 : ¬ ∃ v : α, ∃ c : G.Walk v v, c.IsCycle ∧ c.length = 4) :
    G.EdgeDisjointTriangles := by
  classical
  have hrepr (a b : α) (hab : a ≠ b) :
      {s ∈ (G.cliqueSet 3 : Set (Finset α)) | s(a, b) ∈ (s : Finset α).sym2}
        = {s | G.Adj a b ∧ ∃ c, G.Adj a c ∧ G.Adj b c ∧ s = {a, b, c}} := by
    ext s
    simp only [mem_sym2_iff, Sym2.mem_iff, forall_eq_or_imp, forall_eq,
      mem_cliqueSet_iff, Set.mem_setOf_eq, is3Clique_iff]
    constructor
    · rintro ⟨⟨c, d, e, hcd, hce, hde, rfl⟩, hab'⟩
      simp only [mem_insert, mem_singleton] at hab'
      obtain ⟨rfl | rfl | rfl, rfl | rfl | rfl⟩ := hab'
      any_goals simp only [*, adj_comm, true_and, Ne, not_true] at *
      any_goals
        first
        | exact ⟨c, by aesop⟩
        | exact ⟨d, by aesop⟩
        | exact ⟨e, by aesop⟩
        | simp only [*, true_and] at *
          exact ⟨c, by aesop⟩
        | simp only [*, true_and] at *
          exact ⟨d, by aesop⟩
        | simp only [*, true_and] at *
          exact ⟨e, by aesop⟩
    · rintro ⟨hab', c, hac, hbc, rfl⟩
      refine ⟨⟨a, b, c, ?_⟩, ?_⟩ <;> simp [*]
  rw [edgeDisjointTriangles_iff_mem_sym2_subsingleton, Sym2.forall]
  rintro a b hab
  simp only [Sym2.isDiag_iff_proj_eq] at hab
  rw [hrepr a b (Sym2.mk_isDiag_iff.not.mp hab)]
  rintro _ ⟨hab', c, hac, hbc, rfl⟩ _ ⟨_, d, had, hbd, rfl⟩
  have hcd : c = d := common_neighbor_unique G hC4 hab'.ne hac hbc had hbd
  subst d
  rfl

/-- An independent set in `N(v)` omits at least one of the two non-`v`
vertices of every triangle through `v`. -/
lemma triangle_has_outside_indep (G : SimpleGraph α) (v : α) (S s : Finset α)
    (hSindep : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → ¬ G.Adj a b)
    (hs : G.IsNClique 3 s) (hv : v ∈ s) :
    ∃ u, u ∈ G.neighborFinset v \ S ∧ u ∈ s := by
  obtain ⟨a, b, hva, hvb, hab, rfl⟩ := triangle_through_exists_pair G hs hv
  by_cases ha : a ∈ S
  · have hb : b ∉ S := by
      intro hb
      exact hSindep a ha b hb hab.ne hab
    exact ⟨b, by simp [hvb, hb], by simp⟩
  · exact ⟨a, by simp [hva, ha], by simp⟩

/-- Distinct triangles through `v` consume distinct vertices outside every
independent set in `N(v)`. -/
lemma triangles_le_outside_indep (G : SimpleGraph α) [DecidableRel G.Adj]
    (hC4 : ¬ ∃ x : α, ∃ c : G.Walk x x, c.IsCycle ∧ c.length = 4)
    (v : α) (S : Finset α)
    (hSindep : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → ¬ G.Adj a b) :
    numTrianglesAtVertex G v ≤ (G.neighborFinset v \ S).card := by
  classical
  let tris := (G.cliqueFinset 3).filter fun s => v ∈ s
  let outside := G.neighborFinset v \ S
  have hpick : ∀ s : ↥tris, ∃ u, u ∈ outside ∧ u ∈ s.1 := by
    intro s
    have hs := Finset.mem_filter.mp s.2
    simpa [outside] using
      (triangle_has_outside_indep G v S s.1 hSindep
        (mem_cliqueFinset_iff.mp hs.1) hs.2)
  choose pick hpick_out hpick_mem using hpick
  let f : ↥tris → ↥outside := fun s => ⟨pick s, hpick_out s⟩
  have hf : Function.Injective f := by
    intro s t hst
    apply Subtype.ext
    by_contra hne
    have hs := Finset.mem_filter.mp s.2
    have ht := Finset.mem_filter.mp t.2
    have hsub : ((s.1 : Set α) ∩ (t.1 : Set α)).Subsingleton :=
      (edgeDisjointTriangles_of_no_c4 G hC4)
        (by simpa [mem_cliqueSet_iff] using hs.1)
        (by simpa [mem_cliqueSet_iff] using ht.1) hne
    have hvint : v ∈ (s.1 : Set α) ∩ (t.1 : Set α) := ⟨hs.2, ht.2⟩
    have hfst : (f s).1 = (f t).1 := congrArg Subtype.val hst
    have huint : (f s).1 ∈ (s.1 : Set α) ∩ (t.1 : Set α) := by
      refine ⟨hpick_mem s, ?_⟩
      rw [hfst]
      exact hpick_mem t
    have hvu : v = (f s).1 := hsub hvint huint
    have hadj : G.Adj v (f s).1 :=
      (G.mem_neighborFinset v (f s).1).mp (Finset.mem_sdiff.mp (f s).2).1
    exact hadj.ne hvu
  have hcard := Finset.card_le_card_of_injective hf
  simpa [tris, outside, numTrianglesAtVertex] using hcard

/-- At every vertex of a four-cycle-free graph, local independence plus the
number of incident triangles is at most the degree. -/
lemma indepNeighborsCard_add_numTrianglesAtVertex_le_degree
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (hC4 : ¬ ∃ x : α, ∃ c : G.Walk x x, c.IsCycle ∧ c.length = 4)
    (v : α) :
    indepNeighborsCard G v + numTrianglesAtVertex G v ≤ G.degree v := by
  obtain ⟨S, hsub, hcard, hSindep⟩ := Gc2Dev.exists_indep_in_neighborhood G v
  have htri := triangles_le_outside_indep G hC4 v S hSindep
  have hsub' : S ⊆ G.neighborFinset v := by
    intro u hu
    simp only [SimpleGraph.mem_neighborFinset]
    simpa only [SimpleGraph.mem_neighborFinset] using hsub hu
  have hpartition : (G.neighborFinset v \ S).card + S.card = G.degree v := by
    calc
      (G.neighborFinset v \ S).card + S.card = (G.neighborFinset v).card :=
        Finset.card_sdiff_add_card_eq_card hsub'
      _ = G.degree v := rfl
  omega

/-- If the local independence number at `v` is one, every two distinct
neighbors of `v` are adjacent. -/
lemma adj_of_indepNeighborsCard_eq_one (G : SimpleGraph α) {v a b : α}
    (hva : G.Adj v a) (hvb : G.Adj v b) (hab : a ≠ b)
    (hα : indepNeighborsCard G v = 1) : G.Adj a b := by
  classical
  by_contra hn
  let a' : G.neighborSet v := ⟨a, hva⟩
  let b' : G.neighborSet v := ⟨b, hvb⟩
  have hab' : a' ≠ b' := by
    intro h
    exact hab (congrArg Subtype.val h)
  let S : Finset (G.neighborSet v) := {a', b'}
  have hsymm : Symmetric (fun x y : G.neighborSet v =>
      ¬ (G.induce (G.neighborSet v)).Adj x y) := by
    intro x y hxy hyx
    exact hxy ((G.induce (G.neighborSet v)).symm hyx)
  have hSindep : (G.induce (G.neighborSet v)).IsIndepSet (S : Set _) := by
    rw [SimpleGraph.isIndepSet_iff]
    simp only [S, Finset.coe_insert, Finset.coe_singleton]
    rw [Set.pairwise_pair_of_symmetric hsymm]
    intro _
    simpa [S, a', b', SimpleGraph.induce_adj] using hn
  have hle := hSindep.card_le_indepNum
  have hScard : S.card = 2 := by simp [S, Finset.card_pair hab']
  change (G.induce (G.neighborSet v)).indepNum = 1 at hα
  omega

omit [DecidableEq α] in
/-- Every vertex of a connected nontrivial finite graph has positive local
independence number. -/
lemma one_le_indepNeighborsCard [Nontrivial α] (G : SimpleGraph α)
    [DecidableRel G.Adj] (hG : G.Connected) (v : α) :
    1 ≤ indepNeighborsCard G v := by
  classical
  have hdeg : 0 < G.degree v := hG.preconnected.degree_pos_of_nontrivial v
  have hn : (G.neighborSet v).Nonempty := G.degree_pos_iff_nonempty.mp hdeg
  obtain ⟨u, hu⟩ := hn
  let u' : G.neighborSet v := ⟨u, hu⟩
  let S : Finset (G.neighborSet v) := {u'}
  have hSindep : (G.induce (G.neighborSet v)).IsIndepSet (S : Set _) := by
    simp [S, SimpleGraph.isIndepSet_iff]
  have hle := hSindep.card_le_indepNum
  change 1 ≤ (G.induce (G.neighborSet v)).indepNum
  simpa [S] using hle

/-- In a four-cycle-free graph, a vertex with local independence one that
lies in a triangle lies in exactly one triangle. -/
lemma numTrianglesAtVertex_eq_one_of_indepNeighborsCard_eq_one
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (hC4 : ¬ ∃ x : α, ∃ c : G.Walk x x, c.IsCycle ∧ c.length = 4)
    (v : α) (hα : indepNeighborsCard G v = 1)
    (ht : 0 < numTrianglesAtVertex G v) :
    numTrianglesAtVertex G v = 1 := by
  classical
  have htris : ((G.cliqueFinset 3).filter fun s => v ∈ s).Nonempty := by
    rw [← Finset.card_pos]
    simpa [numTrianglesAtVertex] using ht
  obtain ⟨s, hs⟩ := htris
  have hs' := Finset.mem_filter.mp hs
  obtain ⟨a, b, hva, hvb, hab, -⟩ :=
    triangle_through_exists_pair G (mem_cliqueFinset_iff.mp hs'.1) hs'.2
  have hNsub : G.neighborFinset v ⊆ {a, b} := by
    intro c hc
    simp only [Finset.mem_insert, Finset.mem_singleton]
    by_contra hcnot
    have hca : c ≠ a := fun h => hcnot (Or.inl h)
    have hcb : c ≠ b := fun h => hcnot (Or.inr h)
    have hvc : G.Adj v c := (G.mem_neighborFinset v c).mp hc
    have hac : G.Adj a c :=
      adj_of_indepNeighborsCard_eq_one G hva hvc hca.symm hα
    have hbc : b = c :=
      common_neighbor_unique G hC4 hva.ne hvb hab hvc hac
    exact hcb hbc.symm
  have hdeg : G.degree v ≤ 2 := by
    change (G.neighborFinset v).card ≤ 2
    calc
      (G.neighborFinset v).card ≤ ({a, b} : Finset α).card :=
        Finset.card_le_card hNsub
      _ = 2 := Finset.card_pair hab.ne
  have hlocal :=
    indepNeighborsCard_add_numTrianglesAtVertex_le_degree G hC4 v
  omega

/-- There is a closest pair consisting of a local-independence maximizer and
a triangle-count maximizer. -/
lemma exists_closest_maximizers [Nonempty α]
    (G : SimpleGraph α) [DecidableRel G.Adj] :
    ∃ x y : α,
      (∀ z, indepNeighborsCard G z ≤ indepNeighborsCard G x) ∧
      (∀ z, numTrianglesAtVertex G z ≤ numTrianglesAtVertex G y) ∧
      ∀ x' y', indepNeighborsCard G x' = indepNeighborsCard G x →
        numTrianglesAtVertex G y' = numTrianglesAtVertex G y →
        G.dist x y ≤ G.dist x' y' := by
  classical
  obtain ⟨x₀, -, hx₀⟩ :=
    Finset.exists_max_image Finset.univ (indepNeighborsCard G) Finset.univ_nonempty
  obtain ⟨y₀, -, hy₀⟩ :=
    Finset.exists_max_image Finset.univ (numTrianglesAtVertex G) Finset.univ_nonempty
  let P := (Finset.univ ×ˢ Finset.univ).filter fun p : α × α =>
    indepNeighborsCard G p.1 = indepNeighborsCard G x₀ ∧
      numTrianglesAtVertex G p.2 = numTrianglesAtVertex G y₀
  have hP : P.Nonempty := by
    exact ⟨(x₀, y₀), by simp [P]⟩
  obtain ⟨p, hp, hpmin⟩ :=
    Finset.exists_min_image P (fun q => G.dist q.1 q.2) hP
  have hp' := Finset.mem_filter.mp hp
  refine ⟨p.1, p.2, ?_, ?_, ?_⟩
  · intro z
    rw [hp'.2.1]
    exact hx₀ z (Finset.mem_univ z)
  · intro z
    rw [hp'.2.2]
    exact hy₀ z (Finset.mem_univ z)
  · intro x' y' hx' hy'
    apply hpmin (x', y')
    simp only [P, Finset.mem_filter, Finset.mem_product, Finset.mem_univ,
      true_and]
    exact ⟨hx'.trans hp'.2.1, hy'.trans hp'.2.2⟩

omit [Fintype α] in
/-- A neighbor of the start vertex that lies on a shortest path is its second
vertex. -/
lemma eq_snd_of_adj_start_of_mem_shortestPath {G : SimpleGraph α}
    {u v z : α} (p : G.Walk u v) (hpdist : p.length = G.dist u v)
    (hz : z ∈ p.support) (huz : G.Adj u z) : z = p.snd := by
  let q := p.takeUntil z hz
  let r := p.dropUntil z hz
  have hlen : q.length + r.length = p.length := by
    have h := congrArg Walk.length (p.take_spec hz)
    rw [Walk.length_append] at h
    exact h
  have hshort : G.dist u v ≤ 1 + r.length := by
    have h := dist_le (r.cons huz)
    simpa [Nat.add_comm] using h
  have hqle : q.length ≤ 1 := by omega
  have hqpos : 0 < q.length := by
    have hdistpos : 0 < G.dist u z :=
      q.reachable.pos_dist_of_ne huz.ne
    exact hdistpos.trans_le (dist_le q)
  have hqlen : q.length = 1 := by omega
  have hzget : p.getVert q.length = z := by
    simpa [q] using p.getVert_length_takeUntil hz
  rw [hqlen] at hzget
  exact hzget.symm

omit [Fintype α] in
/-- A neighbor of the endpoint that lies on a shortest path is its
penultimate vertex. -/
lemma eq_penultimate_of_adj_end_of_mem_shortestPath {G : SimpleGraph α}
    {u v z : α} (p : G.Walk u v) (hpdist : p.length = G.dist u v)
    (hz : z ∈ p.support) (hvz : G.Adj v z) : z = p.penultimate := by
  have hzrev : z ∈ p.reverse.support := by
    simpa [Walk.support_reverse] using hz
  have hprev : p.reverse.length = G.dist v u := by
    simpa [G.dist_comm] using hpdist
  have h :=
    eq_snd_of_adj_start_of_mem_shortestPath p.reverse hprev hzrev hvz
  simpa [Walk.snd_reverse] using h

/-- A nontrivial shortest path has exactly one neighbor of its start vertex
on its support. -/
lemma card_neighborFinset_sdiff_support_start {G : SimpleGraph α}
    [DecidableRel G.Adj] {u v : α} (p : G.Walk u v)
    (hpdist : p.length = G.dist u v) (hp : 0 < p.length) :
    (G.neighborFinset u \ p.support.toFinset).card + 1 = G.degree u := by
  have hnp : ¬ p.Nil := Walk.not_nil_iff_lt_length.mpr hp
  have hinter : G.neighborFinset u ∩ p.support.toFinset = {p.snd} := by
    ext z
    simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset,
      List.mem_toFinset, Finset.mem_singleton]
    constructor
    · rintro ⟨huz, hz⟩
      exact eq_snd_of_adj_start_of_mem_shortestPath p hpdist hz huz
    · rintro rfl
      exact ⟨p.adj_snd hnp, List.mem_of_mem_tail (p.snd_mem_tail_support hnp)⟩
  have hpart :=
    Finset.card_sdiff_add_card_inter (G.neighborFinset u) p.support.toFinset
  rw [hinter] at hpart
  simpa using hpart

/-- A nontrivial shortest path has exactly one neighbor of its endpoint on
its support. -/
lemma card_neighborFinset_sdiff_support_end {G : SimpleGraph α}
    [DecidableRel G.Adj] {u v : α} (p : G.Walk u v)
    (hpdist : p.length = G.dist u v) (hp : 0 < p.length) :
    (G.neighborFinset v \ p.support.toFinset).card + 1 = G.degree v := by
  have hprev : p.reverse.length = G.dist v u := by
    simpa [G.dist_comm] using hpdist
  have hprevpos : 0 < p.reverse.length := by simpa using hp
  have h := card_neighborFinset_sdiff_support_start p.reverse hprev hprevpos
  simpa [Walk.support_reverse] using h

/-- For a shortest path of length at least two in a four-cycle-free graph,
the external neighborhoods of its endpoints are disjoint. -/
lemma disjoint_endpoint_external_neighbors {G : SimpleGraph α}
    [DecidableRel G.Adj]
    (hC4 : ¬ ∃ x : α, ∃ c : G.Walk x x, c.IsCycle ∧ c.length = 4)
    {u v : α} (p : G.Walk u v) (hpdist : p.length = G.dist u v)
    (hp : 2 ≤ p.length) :
    Disjoint (G.neighborFinset u \ p.support.toFinset)
      (G.neighborFinset v \ p.support.toFinset) := by
  rw [Finset.disjoint_left]
  intro z hzu hzv
  have hzu' := Finset.mem_sdiff.mp hzu
  have hzv' := Finset.mem_sdiff.mp hzv
  have huz : G.Adj u z := (G.mem_neighborFinset u z).mp hzu'.1
  have hvz : G.Adj v z := (G.mem_neighborFinset v z).mp hzv'.1
  have hdist2 : G.dist u v ≤ 2 := by
    let q : G.Walk u v := .cons huz (.cons hvz.symm .nil)
    simpa [q] using dist_le q
  have hplen : p.length = 2 := by omega
  have huv : u ≠ v := by
    intro h
    subst v
    rw [G.dist_self] at hpdist
    omega
  have hnp : ¬ p.Nil := by
    rw [Walk.not_nil_iff_lt_length]
    omega
  have hsndpen : p.snd = p.penultimate := by
    change p.getVert 1 = p.getVert (p.length - 1)
    rw [hplen]
  have hus : G.Adj u p.snd := p.adj_snd hnp
  have hvs : G.Adj v p.snd := by
    have hvp : G.Adj v p.penultimate := by
      simpa [Walk.snd_reverse] using p.reverse.adj_snd (by simpa using hnp)
    rwa [← hsndpen] at hvp
  have hzs : z = p.snd :=
    common_neighbor_unique G hC4 huv huz hvz hus hvs
  have hsndmem : p.snd ∈ p.support.toFinset := by
    rw [List.mem_toFinset]
    exact List.mem_of_mem_tail (p.snd_mem_tail_support hnp)
  exact hzu'.2 (hzs ▸ hsndmem)

/-- For adjacent endpoints in a four-cycle-free graph, their external
neighborhoods overlap in at most one vertex. -/
lemma card_inter_endpoint_external_neighbors_le_one {G : SimpleGraph α}
    [DecidableRel G.Adj]
    (hC4 : ¬ ∃ x : α, ∃ c : G.Walk x x, c.IsCycle ∧ c.length = 4)
    {u v : α} (huv : u ≠ v) (W : Finset α) :
    ((G.neighborFinset u \ W) ∩ (G.neighborFinset v \ W)).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro z hz w hw
  have hz' := Finset.mem_inter.mp hz
  have hw' := Finset.mem_inter.mp hw
  have huz : G.Adj u z :=
    (G.mem_neighborFinset u z).mp (Finset.mem_sdiff.mp hz'.1).1
  have hvz : G.Adj v z :=
    (G.mem_neighborFinset v z).mp (Finset.mem_sdiff.mp hz'.2).1
  have huw : G.Adj u w :=
    (G.mem_neighborFinset u w).mp (Finset.mem_sdiff.mp hw'.1).1
  have hvw : G.Adj v w :=
    (G.mem_neighborFinset v w).mp (Finset.mem_sdiff.mp hw'.2).1
  exact common_neighbor_unique G hC4 huv huz hvz huw hvw

/-- A single vertex is a connected seed whose surplus is its degree. -/
lemma singleton_seed_bound (G : SimpleGraph α) (instD : DecidableRel G.Adj)
    (hG : G.Connected) (v : α) (c : ℕ) (hc : c ≤ G.degree v) :
    (c : ℝ) ≤ @Ls α _ G instD := by
  let H := G.singletonSubgraph v
  have hH : H.Connected :=
    Subgraph.singletonSubgraph_connected (G := G) (v := v)
  apply seed_bound G instD hG H hH c
  have hvnot : v ∉ G.neighborFinset v := by
    simp [SimpleGraph.mem_neighborFinset]
  have hcnf : Gc2Dev.cnf G {v} = insert v (G.neighborFinset v) := by
    ext z
    simp [Gc2Dev.cnf, SimpleGraph.mem_neighborFinset]
  have hgoal : c + ({v} : Finset α).card ≤ (Gc2Dev.cnf G {v}).card := by
    rw [hcnf, Finset.card_insert_of_notMem hvnot]
    change c + 1 ≤ G.degree v + 1
    omega
  simpa [H] using hgoal

/-- Three pairwise adjacent vertices witness a positive triangle count at
each of them. -/
lemma numTrianglesAtVertex_pos_of_triangle (G : SimpleGraph α)
    [DecidableRel G.Adj] {x y z : α}
    (hxy : G.Adj x y) (hxz : G.Adj x z) (hyz : G.Adj y z) :
    0 < numTrianglesAtVertex G x := by
  classical
  have hs : G.IsNClique 3 {x, y, z} := by
    exact is3Clique_iff.mpr ⟨x, y, z, hxy, hxz, hyz, rfl⟩
  unfold numTrianglesAtVertex
  rw [Finset.card_pos]
  exact ⟨{x, y, z}, Finset.mem_filter.mpr
    ⟨mem_cliqueFinset_iff.mpr hs, by simp⟩⟩

/-- If `v` has local independence one and lies in a triangle, every edge at
`v` lies in a triangle. -/
lemma exists_common_neighbor_of_indepNeighborsCard_eq_one
    (G : SimpleGraph α) [DecidableRel G.Adj] {v x : α}
    (hα : indepNeighborsCard G v = 1)
    (ht : 0 < numTrianglesAtVertex G v) (hvx : G.Adj v x) :
    ∃ z, G.Adj v z ∧ G.Adj x z := by
  classical
  have htris : ((G.cliqueFinset 3).filter fun s => v ∈ s).Nonempty := by
    rw [← Finset.card_pos]
    simpa [numTrianglesAtVertex] using ht
  obtain ⟨s, hs⟩ := htris
  have hs' := Finset.mem_filter.mp hs
  obtain ⟨a, b, hva, hvb, hab, -⟩ :=
    triangle_through_exists_pair G (mem_cliqueFinset_iff.mp hs'.1) hs'.2
  by_cases hxa : x = a
  · subst x
    exact ⟨b, hvb, hab⟩
  · exact ⟨a, hva,
      adj_of_indepNeighborsCard_eq_one G hvx hva hxa hα⟩

set_option maxHeartbeats 1000000 in
/-- The closest pair of a local-independence maximizer and a triangle-count
maximizer supplies a connected seed with their combined surplus. -/
lemma c4free_closest_maximizers_bound [Nontrivial α]
    (G : SimpleGraph α) [instD : DecidableRel G.Adj] (hG : G.Connected)
    (hC4 : ¬ ∃ x : α, ∃ c : G.Walk x x, c.IsCycle ∧ c.length = 4) :
    ∃ x y : α,
      (∀ z, indepNeighborsCard G z ≤ indepNeighborsCard G x) ∧
      (∀ z, numTrianglesAtVertex G z ≤ numTrianglesAtVertex G y) ∧
      ((indepNeighborsCard G x + numTrianglesAtVertex G y : ℕ) : ℝ) ≤
        @Ls α _ G instD := by
  classical
  obtain ⟨x, y, hxmax, hymax, hclose⟩ := exists_closest_maximizers G
  refine ⟨x, y, hxmax, hymax, ?_⟩
  by_cases hty0 : numTrianglesAtVertex G y = 0
  · have htx0 : numTrianglesAtVertex G x = 0 := by
      have := hymax x
      omega
    have hxlocal :=
      indepNeighborsCard_add_numTrianglesAtVertex_le_degree G hC4 x
    have hxdeg : indepNeighborsCard G x ≤ G.degree x := by omega
    rw [hty0, Nat.add_zero]
    exact singleton_seed_bound G instD hG x (indepNeighborsCard G x) hxdeg
  have htypos : 0 < numTrianglesAtVertex G y := Nat.pos_of_ne_zero hty0
  obtain ⟨p, hpPath, hpdist⟩ := hG.exists_path_of_dist x y
  by_cases hp0 : p.length = 0
  · have hxy : x = y := p.eq_of_length_eq_zero hp0
    have hdeg :=
      indepNeighborsCard_add_numTrianglesAtVertex_le_degree G hC4 x
    subst y
    exact singleton_seed_bound G instD hG x
      (indepNeighborsCard G x + numTrianglesAtVertex G x) hdeg
  have hppos : 0 < p.length := Nat.pos_of_ne_zero hp0
  let W := p.support.toFinset
  let Bx := G.neighborFinset x \ W
  let By := G.neighborFinset y \ W
  let U := Bx ∪ By
  have hxcard : Bx.card + 1 = G.degree x := by
    simpa [Bx, W] using
      card_neighborFinset_sdiff_support_start p hpdist hppos
  have hycard : By.card + 1 = G.degree y := by
    simpa [By, W] using
      card_neighborFinset_sdiff_support_end p hpdist hppos
  have hxlocal :=
    indepNeighborsCard_add_numTrianglesAtVertex_le_degree G hC4 x
  have hylocal :=
    indepNeighborsCard_add_numTrianglesAtVertex_le_degree G hC4 y
  have haypos : 1 ≤ indepNeighborsCard G y :=
    one_le_indepNeighborsCard G hG y
  have hUbound :
      indepNeighborsCard G x + numTrianglesAtVertex G y ≤ U.card := by
    by_cases hp1 : p.length = 1
    · have hnp : ¬ p.Nil := Walk.not_nil_iff_lt_length.mpr hppos
      have hsndy : p.snd = y := by
        simpa [hp1] using p.getVert_length
      have hxy : G.Adj x y := by
        simpa [hsndy] using p.adj_snd hnp
      have hxyne : x ≠ y := hxy.ne
      have hIle : (Bx ∩ By).card ≤ 1 := by
        exact card_inter_endpoint_external_neighbors_le_one
          (G := G) hC4 hxyne W
      by_cases hI0 : Bx ∩ By = ∅
      · have hdisj : Disjoint Bx By :=
          Finset.disjoint_iff_inter_eq_empty.mpr hI0
        have hUcard : U.card = Bx.card + By.card := by
          simpa [U] using Finset.card_union_of_disjoint hdisj
        by_contra hbound
        have hsum : numTrianglesAtVertex G x + indepNeighborsCard G y < 2 := by
          omega
        have htx0 : numTrianglesAtVertex G x = 0 := by omega
        have hay1 : indepNeighborsCard G y = 1 := by omega
        obtain ⟨z, hyz, hxz⟩ :=
          exists_common_neighbor_of_indepNeighborsCard_eq_one G hay1 htypos hxy.symm
        have hznot : z ∉ W := by
          intro hzW
          have hzsupport : z ∈ p.support := by simpa [W] using hzW
          have hzsy :=
            eq_snd_of_adj_start_of_mem_shortestPath p hpdist hzsupport hxz
          exact hyz.ne (hzsy.trans hsndy).symm
        have hzI : z ∈ Bx ∩ By := by
          apply Finset.mem_inter.mpr
          exact ⟨Finset.mem_sdiff.mpr
              ⟨(G.mem_neighborFinset x z).mpr hxz, hznot⟩,
            Finset.mem_sdiff.mpr
              ⟨(G.mem_neighborFinset y z).mpr hyz, hznot⟩⟩
        simp [hI0] at hzI
      · obtain ⟨z, hzI⟩ := Finset.nonempty_iff_ne_empty.mpr hI0
        have hzI' := Finset.mem_inter.mp hzI
        have hxz : G.Adj x z :=
          (G.mem_neighborFinset x z).mp (Finset.mem_sdiff.mp hzI'.1).1
        have hyz : G.Adj y z :=
          (G.mem_neighborFinset y z).mp (Finset.mem_sdiff.mp hzI'.2).1
        have htxpos : 0 < numTrianglesAtVertex G x :=
          numTrianglesAtVertex_pos_of_triangle G hxy hxz hyz
        have hUcard := Finset.card_union_add_card_inter Bx By
        change U.card + (Bx ∩ By).card = Bx.card + By.card at hUcard
        by_contra hbound
        have hsum : numTrianglesAtVertex G x + indepNeighborsCard G y < 3 := by
          omega
        have htx1 : numTrianglesAtVertex G x = 1 := by omega
        have hay1 : indepNeighborsCard G y = 1 := by omega
        have hty1 :=
          numTrianglesAtVertex_eq_one_of_indepNeighborsCard_eq_one
            G hC4 y hay1 htypos
        have hmin := hclose x x rfl (htx1.trans hty1.symm)
        rw [G.dist_self] at hmin
        omega
    · have hp2 : 2 ≤ p.length := by omega
      have hdisj : Disjoint Bx By := by
        simpa [Bx, By, W] using
          disjoint_endpoint_external_neighbors (G := G) hC4 p hpdist hp2
      have hUcard : U.card = Bx.card + By.card := by
        simpa [U] using Finset.card_union_of_disjoint hdisj
      by_contra hbound
      have hsum : numTrianglesAtVertex G x + indepNeighborsCard G y < 2 := by
        omega
      have htx0 : numTrianglesAtVertex G x = 0 := by omega
      have hay1 : indepNeighborsCard G y = 1 := by omega
      have hty1 :=
        numTrianglesAtVertex_eq_one_of_indepNeighborsCard_eq_one
          G hC4 y hay1 htypos
      have hnprev : ¬ p.reverse.Nil := by
        simpa using (Walk.not_nil_iff_lt_length.mpr hppos)
      have hypen : G.Adj y p.penultimate := by
        simpa [Walk.snd_reverse] using p.reverse.adj_snd hnprev
      obtain ⟨z, hyz, hpz⟩ :=
        exists_common_neighbor_of_indepNeighborsCard_eq_one
          G hay1 htypos hypen
      have htpenpos : 0 < numTrianglesAtVertex G p.penultimate :=
        numTrianglesAtVertex_pos_of_triangle G hypen.symm hpz hyz
      have htpenle := hymax p.penultimate
      have htpeneq :
          numTrianglesAtVertex G p.penultimate = numTrianglesAtVertex G y := by
        omega
      have hmin := hclose x p.penultimate rfl htpeneq
      have hsub : (p.take (p.length - 1)).IsSubwalk p :=
        p.isSubwalk_take (p.length - 1)
      have hshortpen := length_eq_dist_of_subwalk hpdist hsub
      have hdistpen : G.dist x p.penultimate = p.length - 1 := by
        rw [← hshortpen]
        simp
      rw [← hpdist, hdistpen] at hmin
      omega
  have hxW : x ∈ W := by
    simp [W]
  have hyW : y ∈ W := by
    simp [W]
  have hUsub : U ⊆ Gc2Dev.cnf G W \ W := by
    intro z hz
    have hz' := Finset.mem_union.mp hz
    apply Finset.mem_sdiff.mpr
    rcases hz' with hzx | hzy
    · have hzx' := Finset.mem_sdiff.mp hzx
      exact ⟨Gc2Dev.mem_cnf.mpr
          (Or.inr ⟨x, hxW, (G.mem_neighborFinset x z).mp hzx'.1⟩), hzx'.2⟩
    · have hzy' := Finset.mem_sdiff.mp hzy
      exact ⟨Gc2Dev.mem_cnf.mpr
          (Or.inr ⟨y, hyW, (G.mem_neighborFinset y z).mp hzy'.1⟩), hzy'.2⟩
  have hboundary : U.card ≤ (Gc2Dev.cnf G W \ W).card :=
    Finset.card_le_card hUsub
  have hpartition :
      (Gc2Dev.cnf G W \ W).card + W.card = (Gc2Dev.cnf G W).card :=
    Finset.card_sdiff_add_card_eq_card Gc2Dev.subset_cnf
  have hseed : indepNeighborsCard G x + numTrianglesAtVertex G y + W.card ≤
      (Gc2Dev.cnf G W).card := by omega
  have hverts : p.toSubgraph.verts.toFinset = W := by
    ext z
    simp [W]
  apply seed_bound G instD hG p.toSubgraph p.toSubgraph_connected
    (indepNeighborsCard G x + numTrianglesAtVertex G y)
  rw [hverts]
  exact hseed

omit [DecidableEq α] in
/-- Identify the image maximum with any vertex that dominates all local
independence values. -/
lemma max_indepNeighborsCard_eq [Nonempty α] (G : SimpleGraph α)
    (x : α) (hx : ∀ z, indepNeighborsCard G z ≤ indepNeighborsCard G x) :
    (Finset.univ.image (indepNeighborsCard G)).max' (by simp) =
      indepNeighborsCard G x := by
  apply (Finset.max'_eq_iff _ _ _).mpr
  constructor
  · exact Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩
  · intro n hn
    obtain ⟨z, -, rfl⟩ := Finset.mem_image.mp hn
    exact hx z

/-- Identify `maxTrianglesAtVertex` with any vertex that dominates all local
triangle counts. -/
lemma maxTrianglesAtVertex_eq [Nontrivial α] (G : SimpleGraph α)
    [DecidableRel G.Adj] (y : α)
    (hy : ∀ z, numTrianglesAtVertex G z ≤ numTrianglesAtVertex G y) :
    WrittenOnTheWallII.GraphConjecture160.maxTrianglesAtVertex G =
      numTrianglesAtVertex G y := by
  unfold WrittenOnTheWallII.GraphConjecture160.maxTrianglesAtVertex
  apply (Finset.max'_eq_iff _ _ _).mpr
  constructor
  · exact Finset.mem_image.mpr ⟨y, Finset.mem_univ y, rfl⟩
  · intro n hn
    obtain ⟨z, -, rfl⟩ := Finset.mem_image.mp hn
    exact hy z

/-- The local independence number is bounded by degree, with the active
adjacency decision procedure kept definitionally fixed. -/
lemma indepNeighborsCard_le_degree (G : SimpleGraph α)
    [DecidableRel G.Adj] (v : α) : indepNeighborsCard G v ≤ G.degree v := by
  obtain ⟨S, hsub, hcard, -⟩ := Gc2Dev.exists_indep_in_neighborhood G v
  have hsub' : S ⊆ G.neighborFinset v := by
    intro u hu
    simp only [SimpleGraph.mem_neighborFinset]
    simpa only [SimpleGraph.mem_neighborFinset] using hsub hu
  calc
    indepNeighborsCard G v = S.card := hcard.symm
    _ ≤ (G.neighborFinset v).card := Finset.card_le_card hsub'
    _ = G.degree v := rfl

end

end Gc160Dev

namespace WrittenOnTheWallII.GraphConjecture160

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

set_option maxHeartbeats 1000000 in
/-- Proof of the corrected WOWII Conjecture 160 statement. -/
theorem conjecture160_proved (G : SimpleGraph α) [DecidableRel G.Adj]
    (h : G.Connected) :
    let maxL := (Finset.univ.image (indepNeighborsCard G)).max' (by simp)
    let maxT := maxTrianglesAtVertex G
    let cC4 : ℕ :=
      if ∃ v : α, ∃ c : G.Walk v v, c.IsCycle ∧ c.length = 4 then 0 else 1
    (maxL : ℝ) + (maxT : ℝ) * (cC4 : ℝ) ≤ Ls G := by
  dsimp
  by_cases hC4 : ∃ v : α, ∃ c : G.Walk v v, c.IsCycle ∧ c.length = 4
  · rw [if_pos hC4]
    simp only [Nat.cast_zero, mul_zero, add_zero]
    obtain ⟨x, y, hxmax, hymax, hclose⟩ :=
      Gc160Dev.exists_closest_maximizers G
    rw [Gc160Dev.max_indepNeighborsCard_eq G x hxmax]
    exact Gc160Dev.singleton_seed_bound G _ h x
      (indepNeighborsCard G x) (Gc160Dev.indepNeighborsCard_le_degree G x)
  · rw [if_neg hC4]
    simp only [Nat.cast_one, mul_one]
    obtain ⟨x, y, hxmax, hymax, hbound⟩ :=
      Gc160Dev.c4free_closest_maximizers_bound G h hC4
    rw [Gc160Dev.max_indepNeighborsCard_eq G x hxmax,
      Gc160Dev.maxTrianglesAtVertex_eq G y hymax]
    simpa [Nat.cast_add] using hbound

#print axioms conjecture160_proved

end WrittenOnTheWallII.GraphConjecture160
