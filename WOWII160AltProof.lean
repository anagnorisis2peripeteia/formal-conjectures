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
import WOWII160Proof

/-!
# WOWII Conjecture 160 — second proof, after vulnix0x4

A Lean formalization of the informal argument published by vulnix0x4 in
google-deepmind/formal-conjectures issue #4569: in a `C₄`-free graph every open
neighborhood induces a matching together with isolated vertices, so
`degree v = indepNeighborsCard v + numTrianglesAtVertex v`, and a short case
analysis on a `λ`-maximizer `x` and a `T`-maximizer `y` gives the corrected
Conjecture 160 bound.

One presentational substitution: issue #4569 extends explicit two-star trees to
spanning trees (its Lemma 1); here each of its constructions is fed to the
connected-seed machinery of the Conjecture 2 proof (`Gc160Dev.seed_bound`),
which converts a connected subgraph whose closed neighborhood carries surplus
`c` into a spanning tree with at least `c` leaves. The case structure and the
degree identity are #4569's.
-/

open Classical SimpleGraph Finset

namespace Gc160Alt

variable {α : Type*} [Fintype α] [DecidableEq α]

/- ### The neighborhood matching structure of a `C₄`-free graph -/

/-- The edges of the neighborhood of `v`: the two-element sets obtained by
deleting `v` from a triangle through `v`. -/
noncomputable def nbrEdges (G : SimpleGraph α) [DecidableRel G.Adj] (v : α) :
    Finset (Finset α) :=
  ((G.cliqueFinset 3).filter (fun s => v ∈ s)).image (fun s => s.erase v)

/-- The matched vertices of the neighborhood of `v`: endpoints of triangles
through `v`. -/
noncomputable def matched (G : SimpleGraph α) [DecidableRel G.Adj] (v : α) :
    Finset α :=
  (nbrEdges G v).biUnion id

lemma nbrEdges_shape (G : SimpleGraph α) [DecidableRel G.Adj] {v : α}
    {e : Finset α} (he : e ∈ nbrEdges G v) :
    ∃ a b : α, e = {a, b} ∧ a ≠ b ∧ G.Adj v a ∧ G.Adj v b ∧ G.Adj a b := by
  obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp he
  have hs' := Finset.mem_filter.mp hs
  obtain ⟨a, b, hva, hvb, hab, hset⟩ :=
    Gc160Dev.triangle_through_exists_pair G
      (SimpleGraph.mem_cliqueFinset_iff.mp hs'.1) hs'.2
  refine ⟨a, b, ?_, hab.ne, hva, hvb, hab⟩
  subst hset
  ext z
  simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hzv, rfl | rfl | rfl⟩
    · exact absurd rfl hzv
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨hva.ne', Or.inr (Or.inl rfl)⟩
    · exact ⟨hvb.ne', Or.inr (Or.inr rfl)⟩

lemma mem_nbrEdges_of_adj (G : SimpleGraph α) [DecidableRel G.Adj] {v a b : α}
    (hva : G.Adj v a) (hvb : G.Adj v b) (hab : G.Adj a b) :
    ({a, b} : Finset α) ∈ nbrEdges G v := by
  refine Finset.mem_image.mpr ⟨{v, a, b}, Finset.mem_filter.mpr ⟨?_, by simp⟩, ?_⟩
  · rw [SimpleGraph.mem_cliqueFinset_iff]
    refine ⟨?_, ?_⟩
    · intro x hx y hy hxy
      simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.coe_singleton,
        Finset.mem_singleton, Set.mem_singleton_iff] at hx hy
      rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
        first
          | exact absurd rfl hxy
          | assumption
          | exact hva.symm
          | exact hvb.symm
          | exact hab.symm
    · rw [Finset.card_insert_of_notMem (by simp [hva.ne, hvb.ne]),
        Finset.card_insert_of_notMem (by simp [hab.ne])]
      simp
  · ext z
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hzv, rfl | rfl | rfl⟩
      · exact absurd rfl hzv
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rintro (rfl | rfl)
      · exact ⟨hva.ne', Or.inr (Or.inl rfl)⟩
      · exact ⟨hvb.ne', Or.inr (Or.inr rfl)⟩

/-- In a `C₄`-free graph, distinct neighborhood edges at `v` are disjoint. -/
lemma nbrEdges_pairwiseDisjoint (G : SimpleGraph α) [DecidableRel G.Adj]
    (hC4 : ¬ ∃ x : α, ∃ c : G.Walk x x, c.IsCycle ∧ c.length = 4) (v : α) :
    ∀ e₁ ∈ nbrEdges G v, ∀ e₂ ∈ nbrEdges G v, e₁ ≠ e₂ → Disjoint e₁ e₂ := by
  intro e₁ he₁ e₂ he₂ hne
  obtain ⟨a, b, rfl, hab, hva, hvb, hadjab⟩ := nbrEdges_shape G he₁
  obtain ⟨c, d, rfl, hcd, hvc, hvd, hadjcd⟩ := nbrEdges_shape G he₂
  rw [Finset.disjoint_left]
  rintro z hz₁ hz₂
  apply hne
  -- `z` is a common member; its unique in-neighborhood partner forces equality.
  simp only [Finset.mem_insert, Finset.mem_singleton] at hz₁ hz₂
  have hvz : G.Adj v z := by
    rcases hz₁ with rfl | rfl
    · exact hva
    · exact hvb
  -- the partner of `z` inside the neighborhood of `v` is unique
  have hkey : ∀ p q : α, G.Adj v p → G.Adj v q → G.Adj z p → G.Adj z q →
      p = q := fun p q hvp hvq hzp hzq =>
    Gc160Dev.common_neighbor_unique G hC4 hvz.ne hvp hzp hvq hzq
  rcases hz₁ with rfl | rfl
  · rcases hz₂ with rfl | rfl
    · -- z = a = c : partners b and d coincide
      rw [hkey b d hvb hvd hadjab hadjcd]
    · -- z = a = d : partners b and c coincide
      rw [hkey b c hvb hvc hadjab hadjcd.symm, Finset.pair_comm]
  · rcases hz₂ with rfl | rfl
    · -- z = b = c : partners a and d coincide
      rw [hkey a d hva hvd hadjab.symm hadjcd, Finset.pair_comm]
    · -- z = b = d : partners a and c coincide
      rw [hkey a c hva hvc hadjab.symm hadjcd.symm]

lemma card_nbrEdges (G : SimpleGraph α) [DecidableRel G.Adj] (v : α) :
    (nbrEdges G v).card = numTrianglesAtVertex G v := by
  unfold nbrEdges numTrianglesAtVertex
  apply Finset.card_image_of_injOn
  intro s hs t ht hst
  have hst' : s.erase v = t.erase v := hst
  have hs' := Finset.mem_filter.mp hs
  have ht' := Finset.mem_filter.mp ht
  have hins : insert v (s.erase v) = s := Finset.insert_erase hs'.2
  have hint : insert v (t.erase v) = t := Finset.insert_erase ht'.2
  rw [← hins, ← hint, hst']

lemma matched_subset (G : SimpleGraph α) [DecidableRel G.Adj] (v : α) :
    matched G v ⊆ G.neighborFinset v := by
  intro z hz
  obtain ⟨e, he, hze⟩ := Finset.mem_biUnion.mp hz
  obtain ⟨a, b, rfl, -, hva, hvb, -⟩ := nbrEdges_shape G he
  simp only [id] at hze
  rw [SimpleGraph.mem_neighborFinset]
  rcases Finset.mem_insert.mp hze with rfl | hzb
  · exact hva
  · rw [Finset.mem_singleton.mp hzb]
    exact hvb

lemma card_matched (G : SimpleGraph α) [DecidableRel G.Adj]
    (hC4 : ¬ ∃ x : α, ∃ c : G.Walk x x, c.IsCycle ∧ c.length = 4) (v : α) :
    (matched G v).card = 2 * numTrianglesAtVertex G v := by
  unfold matched
  rw [Finset.card_biUnion]
  · rw [← card_nbrEdges G v, Finset.card_eq_sum_ones (nbrEdges G v),
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e he
    obtain ⟨a, b, rfl, hab, -, -, -⟩ := nbrEdges_shape G he
    simp [Finset.card_insert_of_notMem, hab]
  · intro e₁ he₁ e₂ he₂ hne
    exact nbrEdges_pairwiseDisjoint G hC4 v e₁ he₁ e₂ he₂ hne

/-- A vertex adjacent to `v` and to a neighbor of `v` is matched at `v`. -/
lemma mem_matched_of_adj (G : SimpleGraph α) [DecidableRel G.Adj] {v a b : α}
    (hva : G.Adj v a) (hvb : G.Adj v b) (hab : G.Adj a b) :
    a ∈ matched G v := by
  refine Finset.mem_biUnion.mpr ⟨{a, b}, mem_nbrEdges_of_adj G hva hvb hab, ?_⟩
  simp

/-- An independent subset of the open neighborhood of `v` bounds
`indepNeighborsCard` from below. -/
lemma le_indepNeighborsCard_of_indep (G : SimpleGraph α) [DecidableRel G.Adj]
    (v : α) (S : Finset α) (hsub : S ⊆ G.neighborFinset v)
    (hind : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → ¬ G.Adj a b) :
    S.card ≤ indepNeighborsCard G v := by
  classical
  unfold indepNeighborsCard
  -- lift `S` to the vertex type of the induced neighborhood graph
  have hmem : ∀ a ∈ S, a ∈ G.neighborSet v := by
    intro a ha
    simpa [SimpleGraph.mem_neighborFinset] using hsub ha
  let f : {a // a ∈ S} → ↥(G.neighborSet v) := fun a => ⟨a.1, hmem a.1 a.2⟩
  have hf : Function.Injective f := by
    intro a b hab
    have hval : (a.1 : α) = b.1 := congrArg (fun t => (t : ↥(G.neighborSet v)).1) hab
    exact Subtype.ext hval
  let S' : Finset ↥(G.neighborSet v) := S.attach.map ⟨f, hf⟩
  have hcard : S'.card = S.card := by simp [S']
  have hindep : (G.induce (G.neighborSet v)).IsIndepSet (S' : Set ↥(G.neighborSet v)) := by
    intro x hx y hy hxy hadj
    simp only [S', Finset.coe_map, Set.mem_image, Finset.mem_coe,
      Finset.mem_attach, true_and, Function.Embedding.coeFn_mk] at hx hy
    obtain ⟨⟨x', hx'⟩, rfl⟩ := hx
    obtain ⟨⟨y', hy'⟩, rfl⟩ := hy
    have hne : x' ≠ y' := fun h => hxy (by simp [f, h])
    exact hind x' hx' y' hy' hne hadj
  calc S.card = S'.card := hcard.symm
    _ ≤ (G.induce (G.neighborSet v)).indepNum := hindep.card_le_indepNum

/-- A choice of one endpoint from every neighborhood edge at `v`. -/
lemma exists_pick (G : SimpleGraph α) [DecidableRel G.Adj]
    (hC4 : ¬ ∃ x : α, ∃ c : G.Walk x x, c.IsCycle ∧ c.length = 4) (v : α) :
    ∃ P : Finset α, P ⊆ matched G v ∧
      P.card = numTrianglesAtVertex G v ∧
      ∀ a ∈ P, ∀ b ∈ P, a ≠ b → ¬ G.Adj a b := by
  classical
  letI : LinearOrder α := LinearOrder.lift' (Fintype.equivFin α)
    (Fintype.equivFin α).injective
  have hne : ∀ e ∈ nbrEdges G v, e.Nonempty := by
    intro e he
    obtain ⟨a, b, rfl, -, -, -, -⟩ := nbrEdges_shape G he
    exact ⟨a, Finset.mem_insert_self a {b}⟩
  refine ⟨(nbrEdges G v).attach.image (fun e => e.1.min' (hne e.1 e.2)), ?_, ?_, ?_⟩
  · intro z hz
    obtain ⟨e, -, rfl⟩ := Finset.mem_image.mp hz
    exact Finset.mem_biUnion.mpr ⟨e.1, e.2, e.1.min'_mem (hne e.1 e.2)⟩
  · have hinj : Set.InjOn (fun e : {e // e ∈ nbrEdges G v} => e.1.min' (hne e.1 e.2))
        ((nbrEdges G v).attach : Finset {e // e ∈ nbrEdges G v}) := by
      rintro e₁ - e₂ - hmin
      have h₁ : e₁.1.min' (hne e₁.1 e₁.2) ∈ e₁.1 := e₁.1.min'_mem _
      have hmin' : e₁.1.min' (hne e₁.1 e₁.2) = e₂.1.min' (hne e₂.1 e₂.2) := hmin
      have h₂ : e₁.1.min' (hne e₁.1 e₁.2) ∈ e₂.1 := by
        rw [hmin']
        exact e₂.1.min'_mem _
      by_contra hne'
      have hne'' : e₁.1 ≠ e₂.1 := fun h => hne' (Subtype.ext h)
      exact (Finset.disjoint_left.mp
        (nbrEdges_pairwiseDisjoint G hC4 v e₁.1 e₁.2 e₂.1 e₂.2 hne'') h₁) h₂
    rw [Finset.card_image_of_injOn hinj, Finset.card_attach, card_nbrEdges G v]
  · intro a ha b hb hab hadj
    obtain ⟨e₁, -, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨e₂, -, rfl⟩ := Finset.mem_image.mp hb
    have haN : e₁.1.min' (hne e₁.1 e₁.2) ∈ G.neighborFinset v := by
      exact matched_subset G v (Finset.mem_biUnion.mpr
        ⟨e₁.1, e₁.2, e₁.1.min'_mem _⟩)
    have hbN : e₂.1.min' (hne e₂.1 e₂.2) ∈ G.neighborFinset v := by
      exact matched_subset G v (Finset.mem_biUnion.mpr
        ⟨e₂.1, e₂.2, e₂.1.min'_mem _⟩)
    set a' := e₁.1.min' (hne e₁.1 e₁.2)
    set b' := e₂.1.min' (hne e₂.1 e₂.2)
    have hedge : ({a', b'} : Finset α) ∈ nbrEdges G v :=
      mem_nbrEdges_of_adj G ((G.mem_neighborFinset v a').mp haN)
        ((G.mem_neighborFinset v b').mp hbN) hadj
    have he₁ : ({a', b'} : Finset α) = e₁.1 := by
      by_contra h
      exact (Finset.disjoint_left.mp
        (nbrEdges_pairwiseDisjoint G hC4 v _ hedge e₁.1 e₁.2 h)
        (Finset.mem_insert_self a' {b'})) (e₁.1.min'_mem _)
    have he₂ : ({a', b'} : Finset α) = e₂.1 := by
      by_contra h
      exact (Finset.disjoint_left.mp
        (nbrEdges_pairwiseDisjoint G hC4 v _ hedge e₂.1 e₂.2 h)
        (Finset.mem_insert_of_mem (Finset.mem_singleton_self b')))
        (e₂.1.min'_mem _)
    have heq : e₁ = e₂ := Subtype.ext (he₁ ▸ he₂)
    exact hab (by simp only [a', b', heq])

/-- #4569, identity (1): in a `C₄`-free graph the degree of every vertex splits
as local independence plus local triangle count. -/
lemma degree_eq_indep_add_triangles (G : SimpleGraph α) [DecidableRel G.Adj]
    (hC4 : ¬ ∃ x : α, ∃ c : G.Walk x x, c.IsCycle ∧ c.length = 4) (v : α) :
    G.degree v = indepNeighborsCard G v + numTrianglesAtVertex G v := by
  classical
  refine le_antisymm ?_
    (Gc160Dev.indepNeighborsCard_add_numTrianglesAtVertex_le_degree G hC4 v)
  -- d ≤ λ + T : exhibit an independent set of size d - T
  obtain ⟨P, hPM, hPcard, hPind⟩ := exists_pick G hC4 v
  set S := (G.neighborFinset v \ matched G v) ∪ P with hS
  have hSsub : S ⊆ G.neighborFinset v := by
    intro z hz
    rcases Finset.mem_union.mp hz with hz | hz
    · exact (Finset.mem_sdiff.mp hz).1
    · exact matched_subset G v (hPM hz)
  have hSind : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → ¬ G.Adj a b := by
    intro a ha b hb hab hadj
    have hedge : ∀ c d : α, c ∈ G.neighborFinset v → d ∈ G.neighborFinset v →
        G.Adj c d → c ∈ matched G v := by
      intro c d hc hd hcd
      exact mem_matched_of_adj G ((G.mem_neighborFinset v c).mp hc)
        ((G.mem_neighborFinset v d).mp hd) hcd
    rcases Finset.mem_union.mp ha with ha' | ha'
    · exact (Finset.mem_sdiff.mp ha').2
        (hedge a b (hSsub ha) (hSsub hb) hadj)
    · rcases Finset.mem_union.mp hb with hb' | hb'
      · exact (Finset.mem_sdiff.mp hb').2
          (hedge b a (hSsub hb) (hSsub ha) hadj.symm)
      · exact hPind a ha' b hb' hab hadj
  have hlam := le_indepNeighborsCard_of_indep G v S hSsub hSind
  have hdisj : Disjoint (G.neighborFinset v \ matched G v) P := by
    rw [Finset.disjoint_left]
    intro z hz hz'
    exact (Finset.mem_sdiff.mp hz).2 (hPM hz')
  have hScard : S.card = (G.neighborFinset v \ matched G v).card + P.card :=
    Finset.card_union_of_disjoint hdisj
  have hsdiff : (G.neighborFinset v \ matched G v).card
      = G.degree v - 2 * numTrianglesAtVertex G v := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr (matched_subset G v),
      card_matched G hC4 v, SimpleGraph.card_neighborFinset_eq_degree]
  have hMle : 2 * numTrianglesAtVertex G v ≤ G.degree v := by
    rw [← card_matched G hC4 v, ← SimpleGraph.card_neighborFinset_eq_degree]
    exact Finset.card_le_card (matched_subset G v)
  omega

/-- #4569, inequality (2): `λ(v) ≥ T(v)` in a `C₄`-free graph. -/
lemma triangles_le_indepNeighborsCard (G : SimpleGraph α) [DecidableRel G.Adj]
    (hC4 : ¬ ∃ x : α, ∃ c : G.Walk x x, c.IsCycle ∧ c.length = 4) (v : α) :
    numTrianglesAtVertex G v ≤ indepNeighborsCard G v := by
  have hid := degree_eq_indep_add_triangles G hC4 v
  have hM : (matched G v).card ≤ G.degree v := by
    calc (matched G v).card ≤ (G.neighborFinset v).card :=
          Finset.card_le_card (matched_subset G v)
      _ = G.degree v := by rw [SimpleGraph.card_neighborFinset_eq_degree]
  have h2T := card_matched G hC4 v
  omega

/- ### Seed constructions for the #4569 case analysis -/

/-- An edge is a connected seed: two adjacent vertices whose external
neighborhoods are large force many spanning-tree leaves. -/
lemma edge_seed_bound (G : SimpleGraph α) (instD : DecidableRel G.Adj)
    (hG : G.Connected) {x y : α} (hxy : G.Adj x y) (c : ℕ)
    (hc : c + 2 ≤ (Gc2Dev.cnf G {x, y}).card) :
    (c : ℝ) ≤ @Ls α _ G instD := by
  apply Gc160Dev.seed_bound G instD hG (G.subgraphOfAdj hxy)
    (SimpleGraph.Subgraph.subgraphOfAdj_connected hxy) c
  have hverts : (G.subgraphOfAdj hxy).verts.toFinset = {x, y} := by
    ext z
    simp [SimpleGraph.subgraphOfAdj]
  rw [hverts]
  have hcardxy : ({x, y} : Finset α).card = 2 :=
    Finset.card_pair hxy.ne
  omega

/-- The closed neighborhood of `{x, y}` contains both external neighborhoods
and the pair itself. -/
lemma card_cnf_pair (G : SimpleGraph α) [DecidableRel G.Adj] {x y : α}
    (hxy : G.Adj x y) :
    (G.neighborFinset x \ {x, y}).card + (G.neighborFinset y \ {x, y}).card
      - ((G.neighborFinset x \ {x, y}) ∩ (G.neighborFinset y \ {x, y})).card
      + 2 ≤ (Gc2Dev.cnf G {x, y}).card := by
  classical
  set A := G.neighborFinset x \ {x, y}
  set B := G.neighborFinset y \ {x, y}
  have hsub : ({x, y} : Finset α) ∪ (A ∪ B) ⊆ Gc2Dev.cnf G {x, y} := by
    intro z hz
    rcases Finset.mem_union.mp hz with hz | hz
    · exact Gc2Dev.subset_cnf hz
    · rcases Finset.mem_union.mp hz with hz | hz
      · have hz' := Finset.mem_sdiff.mp hz
        exact Gc2Dev.mem_cnf.mpr (Or.inr ⟨x, by simp,
          (G.mem_neighborFinset x z).mp hz'.1⟩)
      · have hz' := Finset.mem_sdiff.mp hz
        exact Gc2Dev.mem_cnf.mpr (Or.inr ⟨y, by simp,
          (G.mem_neighborFinset y z).mp hz'.1⟩)
  have hdisj : Disjoint ({x, y} : Finset α) (A ∪ B) := by
    rw [Finset.disjoint_left]
    intro z hz hz'
    rcases Finset.mem_union.mp hz' with h | h
    · exact (Finset.mem_sdiff.mp h).2 hz
    · exact (Finset.mem_sdiff.mp h).2 hz
  have hcard : ({x, y} : Finset α).card = 2 := Finset.card_pair hxy.ne
  calc A.card + B.card - (A ∩ B).card + 2
      = (A ∪ B).card + 2 := by rw [Finset.card_union]
    _ = (A ∪ B).card + ({x, y} : Finset α).card := by rw [hcard]
    _ = (({x, y} : Finset α) ∪ (A ∪ B)).card := by
        rw [Finset.card_union_of_disjoint hdisj, Nat.add_comm]
    _ ≤ (Gc2Dev.cnf G {x, y}).card := Finset.card_le_card hsub

/-- #4569 construction (1) as a seed: a geodesic of length at least two gives
`Ls ≥ d(x) + d(y) - 2`. -/
lemma geodesic_seed_bound (G : SimpleGraph α) (instD : DecidableRel G.Adj)
    (hG : G.Connected)
    (hC4 : ¬ ∃ x : α, ∃ c : G.Walk x x, c.IsCycle ∧ c.length = 4)
    {x y : α} (p : G.Walk x y) (hpdist : p.length = G.dist x y)
    (hp : 2 ≤ p.length) (c : ℕ)
    (hc : c + 2 ≤ G.degree x + G.degree y) :
    (c : ℝ) ≤ @Ls α _ G instD := by
  classical
  set W := p.support.toFinset with hW
  set Bx := G.neighborFinset x \ W with hBx
  set By := G.neighborFinset y \ W with hBy
  have hppos : 0 < p.length := by omega
  have hxcount := Gc160Dev.card_neighborFinset_sdiff_support_start p hpdist hppos
  have hycount := Gc160Dev.card_neighborFinset_sdiff_support_end p hpdist hppos
  have hdisj : Disjoint Bx By :=
    Gc160Dev.disjoint_endpoint_external_neighbors hC4 p hpdist hp
  have hBx1 : Bx.card + 1 = G.degree x := hxcount
  have hBy1 : By.card + 1 = G.degree y := hycount
  apply Gc160Dev.seed_bound G instD hG p.toSubgraph p.toSubgraph_connected
  have hverts : p.toSubgraph.verts.toFinset = W := by
    ext z
    simp [hW, SimpleGraph.Walk.mem_verts_toSubgraph]
  rw [hverts]
  have hsub : Bx ∪ By ⊆ Gc2Dev.cnf G W \ W := by
    intro z hz
    apply Finset.mem_sdiff.mpr
    rcases Finset.mem_union.mp hz with hz | hz
    · have hz' := Finset.mem_sdiff.mp hz
      refine ⟨Gc2Dev.mem_cnf.mpr (Or.inr ⟨x, ?_, (G.mem_neighborFinset x z).mp hz'.1⟩), hz'.2⟩
      simp [hW]
    · have hz' := Finset.mem_sdiff.mp hz
      refine ⟨Gc2Dev.mem_cnf.mpr (Or.inr ⟨y, ?_, (G.mem_neighborFinset y z).mp hz'.1⟩), hz'.2⟩
      simp [hW]
  have hUcard : (Bx ∪ By).card = Bx.card + By.card :=
    Finset.card_union_of_disjoint hdisj
  have hbound : (Bx ∪ By).card ≤ (Gc2Dev.cnf G W \ W).card :=
    Finset.card_le_card hsub
  have hpart : (Gc2Dev.cnf G W \ W).card + W.card = (Gc2Dev.cnf G W).card :=
    Finset.card_sdiff_add_card_eq_card Gc2Dev.subset_cnf
  omega

/-- Deleting the two endpoints of an edge from an endpoint's neighborhood
removes exactly the other endpoint. -/
lemma card_sdiff_pair_left (G : SimpleGraph α) [DecidableRel G.Adj] {x y : α}
    (hxy : G.Adj x y) :
    (G.neighborFinset x \ {x, y}).card + 1 = G.degree x := by
  have h1 : G.neighborFinset x \ {x, y} = (G.neighborFinset x).erase y := by
    ext z
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton,
      Finset.mem_erase]
    constructor
    · rintro ⟨hz, hne⟩
      exact ⟨fun h => hne (Or.inr h), hz⟩
    · rintro ⟨hne, hz⟩
      refine ⟨hz, ?_⟩
      rintro (rfl | rfl)
      · exact G.irrefl ((G.mem_neighborFinset z z).mp hz)
      · exact hne rfl
  rw [h1, Finset.card_erase_add_one ((G.mem_neighborFinset x y).mpr hxy),
    SimpleGraph.card_neighborFinset_eq_degree]

/- ### The main #4569 case analysis -/

set_option maxHeartbeats 1000000 in
/-- The #4569 proof of the corrected Conjecture 160, by cases on the two
maximizers. -/
theorem conjecture160_alt_core [Nontrivial α] (G : SimpleGraph α)
    (instD : DecidableRel G.Adj) (hG : G.Connected)
    (hC4 : ¬ ∃ v : α, ∃ c : G.Walk v v, c.IsCycle ∧ c.length = 4)
    {x y : α}
    (hxmax : ∀ z, indepNeighborsCard G z ≤ indepNeighborsCard G x)
    (hymax : ∀ z, numTrianglesAtVertex G z ≤ numTrianglesAtVertex G y) :
    ((indepNeighborsCard G x + numTrianglesAtVertex G y : ℕ) : ℝ) ≤
      @Ls α _ G instD := by
  classical
  set LL := indepNeighborsCard G x with hLL
  set TT := numTrianglesAtVertex G y with hTT
  -- the degree identities at both maximizers
  have hidx := degree_eq_indep_add_triangles G hC4 x
  have hidy := degree_eq_indep_add_triangles G hC4 y
  -- trivial case: no triangles anywhere
  by_cases hT0 : TT = 0
  · rw [hT0, Nat.add_zero]
    exact Gc160Dev.singleton_seed_bound G instD hG x LL
      (Gc160Dev.indepNeighborsCard_le_degree G x)
  have hTTpos : 0 < TT := Nat.pos_of_ne_zero hT0
  -- coincident maximizers
  by_cases hxy : x = y
  · subst hxy
    have : G.degree x = LL + TT := hidx
    exact Gc160Dev.singleton_seed_bound G instD hG x (LL + TT) (le_of_eq this.symm)
  -- the two λ/T bounds used throughout
  have hlamy : TT ≤ indepNeighborsCard G y := triangles_le_indepNeighborsCard G hC4 y
  have hLLy : indepNeighborsCard G y ≤ LL := hxmax y
  have hTx : numTrianglesAtVertex G x ≤ TT := hymax x
  rcases Nat.lt_or_ge 1 (G.dist x y) with hdist | hdist
  · -- Case 1 : d(x, y) ≥ 2
    obtain ⟨p, hppath, hplen⟩ := hG.exists_path_of_dist x y
    have hp2 : 2 ≤ p.length := by omega
    by_cases hgen : 2 ≤ numTrianglesAtVertex G x + indepNeighborsCard G y
    · exact geodesic_seed_bound G instD hG hC4 p hplen hp2 (LL + TT) (by omega)
    · -- tight sub-case : t(x) = 0 and λ(y) = TT = 1
      push_neg at hgen
      have htx0 : numTrianglesAtVertex G x = 0 := by omega
      have hlamy1 : indepNeighborsCard G y = 1 := by omega
      have hTT1 : TT = 1 := by omega
      have hdy2 : G.degree y = 2 := by omega
      -- the neighborhood of y is a single adjacent pair {w', z'}
      have hone : (nbrEdges G y).card = 1 := by
        rw [card_nbrEdges G y]; omega
      obtain ⟨e, he⟩ := Finset.card_eq_one.mp hone
      have heMem : e ∈ nbrEdges G y := he ▸ Finset.mem_singleton_self e
      obtain ⟨a, b, rfl, hab, hya, hyb, hadjab⟩ := nbrEdges_shape G heMem
      have hNy : G.neighborFinset y = {a, b} := by
        apply (Finset.eq_of_subset_of_card_le ?_ ?_).symm
        · intro z hz
          rcases Finset.mem_insert.mp hz with rfl | hz
          · exact (G.mem_neighborFinset y z).mpr hya
          · rw [Finset.mem_singleton.mp hz]
            exact (G.mem_neighborFinset y b).mpr hyb
        · rw [SimpleGraph.card_neighborFinset_eq_degree, hdy2,
            Finset.card_pair hab]
      -- the penultimate vertex of the geodesic is a or b; name its partner z'
      have hnprev : ¬ p.reverse.Nil := by
        simpa using (Walk.not_nil_iff_lt_length.mpr (by omega : 0 < p.length))
      have hypen : G.Adj y p.penultimate := by
        simpa [Walk.snd_reverse] using p.reverse.adj_snd hnprev
      have hpenN : p.penultimate ∈ G.neighborFinset y :=
        (G.mem_neighborFinset y _).mpr hypen
      rw [hNy] at hpenN
      -- partner selection
      obtain ⟨z', hyz', hwz', hz'ne⟩ :
          ∃ z', G.Adj y z' ∧ G.Adj p.penultimate z' ∧ z' ≠ p.penultimate := by
        rcases Finset.mem_insert.mp hpenN with hpa | hpb
        · exact ⟨b, hyb, by rw [hpa]; exact hadjab, by
            rw [hpa]; exact fun h => hab h.symm⟩
        · rw [Finset.mem_singleton.mp hpb]
          exact ⟨a, hya, hadjab.symm, fun h => hab h⟩
      -- the sub-geodesic from x to the penultimate vertex
      have hsub : (p.take (p.length - 1)).IsSubwalk p := p.isSubwalk_take _
      have hqlen : (p.take (p.length - 1)).length = p.length - 1 := by
        simp
      have hqdist := length_eq_dist_of_subwalk hplen hsub
      set q := p.take (p.length - 1) with hq
      have hqpos : 0 < q.length := by rw [hqlen]; omega
      have hxcount := Gc160Dev.card_neighborFinset_sdiff_support_start q hqdist hqpos
      set Wq := q.support.toFinset with hWq
      -- y is not on the sub-geodesic
      have hyW : y ∉ Wq := by
        intro hy
        have hy' : y ∈ q.support := List.mem_toFinset.mp hy
        have : G.dist x y ≤ q.length := by
          calc G.dist x y ≤ (q.takeUntil y hy').length :=
                SimpleGraph.dist_le _
            _ ≤ q.length := Walk.length_takeUntil_le q hy'
        omega
      -- z' is not on the geodesic at all
      have hz'p : z' ∉ p.support := by
        intro hz'
        exact hz'ne (Gc160Dev.eq_penultimate_of_adj_end_of_mem_shortestPath
          p hplen hz' hyz')
      have hz'W : z' ∉ Wq := by
        intro h
        exact hz'p (hsub.support_subset (List.mem_toFinset.mp h))
      -- neither y nor z' is a neighbor of x
      have hyNx : y ∉ G.neighborFinset x := by
        intro h
        have hadjxy := (G.mem_neighborFinset x y).mp h
        have : G.dist x y ≤ 1 := by
          have := SimpleGraph.dist_le (Walk.cons hadjxy Walk.nil)
          simpa using this
        omega
      have hz'Nx : z' ∉ G.neighborFinset x := by
        intro h
        have hadjxz' := (G.mem_neighborFinset x z').mp h
        -- x–z'–y is a walk of length 2, so dist = 2 and q has length 1
        have hd2 : G.dist x y ≤ 2 := by
          have := SimpleGraph.dist_le (Walk.cons hadjxz' (Walk.cons hyz'.symm Walk.nil))
          simpa using this
        have hdxy2 : G.dist x y = 2 := by omega
        have hplen2 : p.length = 2 := by rw [hplen, hdxy2]
        have hq1 : q.length = 1 := by rw [hqlen, hplen2]
        have hadjxw : G.Adj x p.penultimate := by
          have hqnn : ¬ q.Nil := Walk.not_nil_iff_lt_length.mpr (by omega)
          have hsnd : q.snd = p.penultimate := by
            have h := q.getVert_length
            rw [hq1] at h
            exact h
          rw [← hsnd]
          exact q.adj_snd hqnn
        exact hz'ne (Gc160Dev.common_neighbor_unique G hC4 hxy
          hadjxz' hyz' hadjxw hypen)
      -- assemble the boundary count
      have hseed : (LL + TT) + Wq.card ≤ (Gc2Dev.cnf G Wq).card := by
        have hpenW : p.penultimate ∈ Wq := by
          simpa [hWq] using List.mem_toFinset.mpr q.end_mem_support
        have hxW : x ∈ Wq := by
          simpa [hWq] using List.mem_toFinset.mpr q.start_mem_support
        have hynez' : y ≠ z' := fun h => G.irrefl (h ▸ hyz')
        set A := G.neighborFinset x \ Wq with hA
        have hz'A : z' ∉ A := fun h => hz'Nx (Finset.mem_sdiff.mp h).1
        have hyA : y ∉ insert z' A := by
          intro h
          rcases Finset.mem_insert.mp h with h | h
          · exact hynez' h
          · exact hyNx (Finset.mem_sdiff.mp h).1
        have hEsub : insert y (insert z' A) ⊆ Gc2Dev.cnf G Wq \ Wq := by
          intro u hu
          apply Finset.mem_sdiff.mpr
          rcases Finset.mem_insert.mp hu with rfl | hu
          · exact ⟨Gc2Dev.mem_cnf.mpr (Or.inr ⟨p.penultimate, hpenW, hypen.symm⟩), hyW⟩
          rcases Finset.mem_insert.mp hu with rfl | hu
          · exact ⟨Gc2Dev.mem_cnf.mpr (Or.inr ⟨p.penultimate, hpenW, hwz'⟩), hz'W⟩
          · have hu' := Finset.mem_sdiff.mp hu
            exact ⟨Gc2Dev.mem_cnf.mpr (Or.inr ⟨x, hxW,
              (G.mem_neighborFinset x u).mp hu'.1⟩), hu'.2⟩
        have hEcard : (insert y (insert z' A)).card = A.card + 2 := by
          rw [Finset.card_insert_of_notMem hyA, Finset.card_insert_of_notMem hz'A]
        have hbound : (insert y (insert z' A)).card ≤ (Gc2Dev.cnf G Wq \ Wq).card :=
          Finset.card_le_card hEsub
        have hpart : (Gc2Dev.cnf G Wq \ Wq).card + Wq.card = (Gc2Dev.cnf G Wq).card :=
          Finset.card_sdiff_add_card_eq_card Gc2Dev.subset_cnf
        omega
      apply Gc160Dev.seed_bound G instD hG q.toSubgraph q.toSubgraph_connected
        (LL + TT)
      have hverts : q.toSubgraph.verts.toFinset = Wq := by
        ext z
        simp [hWq, SimpleGraph.Walk.mem_verts_toSubgraph]
      rw [hverts]
      exact hseed
  · -- adjacent (dist = 1 since x ≠ y and G connected)
    have hdist1 : G.dist x y = 1 := by
      have h0 : 0 < G.dist x y := by
        have h := (hG.preconnected x y).pos_dist_of_ne hxy
        exact h
      omega
    have hadj : G.Adj x y := by
      obtain ⟨p, hppath, hplen⟩ := hG.exists_path_of_dist x y
      rw [hdist1] at hplen
      cases p with
      | nil => simp at hplen
      | cons h q =>
        cases q with
        | nil => exact h
        | cons h' q' => simp [Walk.length_cons] at hplen
    by_cases hcommon : ∃ z, G.Adj x z ∧ G.Adj y z
    · -- Case 3 : adjacent with a (unique) common neighbor
      obtain ⟨z₀, hxz₀, hyz₀⟩ := hcommon
      by_cases htxT : numTrianglesAtVertex G x = TT
      · -- the full star at x already carries LL + TT
        apply Gc160Dev.singleton_seed_bound G instD hG x (LL + TT)
        rw [hidx, htxT]
      · -- t(x) < TT forces TT ≥ 2 and the edge seed carries LL + TT
        have htxlt : numTrianglesAtVertex G x < TT := lt_of_le_of_ne hTx htxT
        have htx1 : 0 < numTrianglesAtVertex G x :=
          Gc160Dev.numTrianglesAtVertex_pos_of_triangle G hadj hxz₀ hyz₀
        have hTT2 : 2 ≤ TT := by omega
        apply edge_seed_bound G instD hG hadj (LL + TT)
        have hcnf := card_cnf_pair G hadj
        have hint := Gc160Dev.card_inter_endpoint_external_neighbors_le_one
          hC4 hxy ({x, y} : Finset α)
        have hAx := card_sdiff_pair_left G hadj
        have hAy := card_sdiff_pair_left G hadj.symm
        have hAy' : (G.neighborFinset y \ {x, y}).card + 1 = G.degree y := by
          have hswap : ({y, x} : Finset α) = {x, y} := Finset.pair_comm y x
          rw [← hswap]
          exact hAy
        omega
    · -- Case 2 : adjacent with no common neighbor
      push_neg at hcommon
      -- x is unmatched at y, so λ(y) ≥ TT + 1
      have hxunmatched : x ∉ matched G y := by
        intro hx
        obtain ⟨e, he, hxe⟩ := Finset.mem_biUnion.mp hx
        obtain ⟨a, b, rfl, hab, hya, hyb, hadjab⟩ := nbrEdges_shape G he
        simp only [id, Finset.mem_insert, Finset.mem_singleton] at hxe
        rcases hxe with rfl | rfl
        · exact hcommon b hadjab hyb
        · exact hcommon a hadjab.symm hya
      have hxmemNy : x ∈ G.neighborFinset y := by
        rw [SimpleGraph.mem_neighborFinset]
        exact hadj.symm
      have hMx : (matched G y).card + 1 ≤ G.degree y := by
        have hins : insert x (matched G y) ⊆ G.neighborFinset y := by
          intro z hz
          rcases Finset.mem_insert.mp hz with rfl | hz
          · exact hxmemNy
          · exact matched_subset G y hz
        calc (matched G y).card + 1
            = (insert x (matched G y)).card :=
              (Finset.card_insert_of_notMem hxunmatched).symm
          _ ≤ (G.neighborFinset y).card := Finset.card_le_card hins
          _ = G.degree y := by rw [SimpleGraph.card_neighborFinset_eq_degree]
      have h2T := card_matched G hC4 y
      -- λ(y) ≥ TT + 1, hence the edge seed carries LL + TT
      have hlamy1 : TT + 1 ≤ indepNeighborsCard G y := by omega
      apply edge_seed_bound G instD hG hadj (LL + TT)
      have hcnf := card_cnf_pair G hadj
      -- no common neighbor: the two external neighborhoods are disjoint
      have hinter : (G.neighborFinset x \ {x, y}) ∩ (G.neighborFinset y \ {x, y}) = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro z hz
        have hz' := Finset.mem_inter.mp hz
        exact hcommon z
          ((G.mem_neighborFinset x z).mp (Finset.mem_sdiff.mp hz'.1).1)
          ((G.mem_neighborFinset y z).mp (Finset.mem_sdiff.mp hz'.2).1)
      rw [hinter] at hcnf
      simp only [Finset.card_empty, Nat.sub_zero] at hcnf
      -- |N(x) \ {x,y}| = d(x) - 1 and |N(y) \ {x,y}| = d(y) - 1
      have hAx := card_sdiff_pair_left G hadj
      have hAy' : (G.neighborFinset y \ {x, y}).card + 1 = G.degree y := by
        have hswap : ({y, x} : Finset α) = {x, y} := Finset.pair_comm y x
        rw [← hswap]
        exact card_sdiff_pair_left G hadj.symm
      omega

end Gc160Alt

namespace WrittenOnTheWallII.GraphConjecture160

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

set_option maxHeartbeats 1000000 in
/-- Second proof of the corrected WOWII Conjecture 160 statement, after the
argument of vulnix0x4 (google-deepmind/formal-conjectures#4569). -/
theorem conjecture160_alt (G : SimpleGraph α) [DecidableRel G.Adj]
    (h : G.Connected) :
    let maxL := (Finset.univ.image (indepNeighborsCard G)).max' (by simp)
    let maxT := maxTrianglesAtVertex G
    let cC4 : ℕ :=
      if ∃ v : α, ∃ c : G.Walk v v, c.IsCycle ∧ c.length = 4 then 0 else 1
    (maxL : ℝ) + (maxT : ℝ) * (cC4 : ℝ) ≤ Ls G := by
  dsimp
  obtain ⟨x, y, hxmax, hymax, -⟩ := Gc160Dev.exists_closest_maximizers G
  by_cases hC4 : ∃ v : α, ∃ c : G.Walk v v, c.IsCycle ∧ c.length = 4
  · rw [if_pos hC4]
    simp only [Nat.cast_zero, mul_zero, add_zero]
    rw [Gc160Dev.max_indepNeighborsCard_eq G x hxmax]
    exact Gc160Dev.singleton_seed_bound G _ h x
      (indepNeighborsCard G x) (Gc160Dev.indepNeighborsCard_le_degree G x)
  · rw [if_neg hC4]
    simp only [Nat.cast_one, mul_one]
    rw [Gc160Dev.max_indepNeighborsCard_eq G x hxmax,
      Gc160Dev.maxTrianglesAtVertex_eq G y hymax]
    simpa [Nat.cast_add] using
      Gc160Alt.conjecture160_alt_core G inferInstance h hC4 hxmax hymax

#print axioms conjecture160_alt

end WrittenOnTheWallII.GraphConjecture160
