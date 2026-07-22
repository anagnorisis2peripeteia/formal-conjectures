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

import FormalConjectures.WrittenOnTheWallII.GraphConjecture194

/-!
# A parametric family of counterexamples to WOWII Conjecture 194

This file formalises the equality family `G(s,t)` from the accompanying note.  Its vertices are
a clique of order `(s + 1) * t * (t - 1) - 1`, an independent set of order `t + 1`, and `t`
pairwise disjoint end cliques of order `s`.  End clique `i` is attached only to hub `i`.
-/

namespace WrittenOnTheWallII.GraphConjecture194.Family

open Classical SimpleGraph

/-- The order of the central clique in the equality family. -/
def cliqueSize (s t : ℕ) : ℕ := (s + 1) * t * (t - 1) - 1

/-- Vertices are central-clique vertices, hubs, or vertices in one of the end cliques. -/
abbrev Vertex (s t : ℕ) :=
  Fin (cliqueSize s t) ⊕ (Fin (t + 1) ⊕ (Fin t × Fin s))

/-- The equality-family graph `G(s,t)`. -/
def graph (s t : ℕ) : SimpleGraph (Vertex s t) :=
  SimpleGraph.fromRel fun u v =>
    match u, v with
    | .inl _, .inl _ => True
    | .inl _, .inr (.inl _) => True
    | .inr (.inl h), .inr (.inr (i, _)) => h.val = i.val
    | .inr (.inr (i, _)), .inr (.inr (j, _)) => i = j
    | _, _ => False

noncomputable instance (s t : ℕ) : DecidableRel (graph s t).Adj := by
  unfold graph
  infer_instance

@[simp, category API, AMS 5]
theorem adj_clique_clique {s t : ℕ} (c d : Fin (cliqueSize s t)) :
    (graph s t).Adj (.inl c) (.inl d) ↔ c ≠ d := by
  simp [graph, SimpleGraph.fromRel_adj]

@[simp, category API, AMS 5]
theorem adj_clique_hub {s t : ℕ} (c : Fin (cliqueSize s t)) (h : Fin (t + 1)) :
    (graph s t).Adj (.inl c) (.inr (.inl h)) := by
  simp [graph, SimpleGraph.fromRel_adj]

@[simp, category API, AMS 5]
theorem adj_hub_clique {s t : ℕ} (h : Fin (t + 1)) (c : Fin (cliqueSize s t)) :
    (graph s t).Adj (.inr (.inl h)) (.inl c) := by
  rw [SimpleGraph.adj_comm]
  exact adj_clique_hub c h

@[simp, category API, AMS 5]
theorem adj_hub_hub {s t : ℕ} (h k : Fin (t + 1)) :
    ¬(graph s t).Adj (.inr (.inl h)) (.inr (.inl k)) := by
  simp [graph, SimpleGraph.fromRel_adj]

@[simp, category API, AMS 5]
theorem adj_hub_block {s t : ℕ} (h : Fin (t + 1)) (i : Fin t) (b : Fin s) :
    (graph s t).Adj (.inr (.inl h)) (.inr (.inr (i, b))) ↔ h.val = i.val := by
  simp [graph, SimpleGraph.fromRel_adj]

@[simp, category API, AMS 5]
theorem adj_block_hub {s t : ℕ} (i : Fin t) (b : Fin s) (h : Fin (t + 1)) :
    (graph s t).Adj (.inr (.inr (i, b))) (.inr (.inl h)) ↔ h.val = i.val := by
  rw [SimpleGraph.adj_comm]
  exact adj_hub_block h i b

@[simp, category API, AMS 5]
theorem adj_clique_block {s t : ℕ} (c : Fin (cliqueSize s t))
    (i : Fin t) (b : Fin s) :
    ¬(graph s t).Adj (.inl c) (.inr (.inr (i, b))) := by
  simp [graph, SimpleGraph.fromRel_adj]

@[simp, category API, AMS 5]
theorem adj_block_clique {s t : ℕ} (i : Fin t) (b : Fin s)
    (c : Fin (cliqueSize s t)) :
    ¬(graph s t).Adj (.inr (.inr (i, b))) (.inl c) := by
  rw [SimpleGraph.adj_comm]
  exact adj_clique_block c i b

@[simp, category API, AMS 5]
theorem adj_block_block {s t : ℕ} (i j : Fin t) (b c : Fin s) :
    (graph s t).Adj (.inr (.inr (i, b))) (.inr (.inr (j, c))) ↔
      i = j ∧ b ≠ c := by
  simp [graph, SimpleGraph.fromRel_adj, eq_comm]
  constructor
  · rintro ⟨hbc, hij⟩
    exact ⟨hij, hbc hij⟩
  · rintro ⟨hij, hbc⟩
    exact ⟨fun _ => hbc, hij⟩

/-- Under the paper's hypotheses, the central clique is nonempty. -/
@[category API, AMS 5]
theorem cliqueSize_pos {s t : ℕ} (hs : 1 ≤ s) (ht : 3 ≤ t) : 0 < cliqueSize s t := by
  have hst : 12 ≤ (s + 1) * t * (t - 1) := by
    calc
      12 = 2 * 3 * 2 := by norm_num
      _ ≤ (s + 1) * t * (t - 1) :=
        Nat.mul_le_mul (Nat.mul_le_mul (by omega) ht) (by omega)
  unfold cliqueSize
  omega

/-- The equality-family graph has `(s + 1) * t^2` vertices. -/
@[category API, AMS 5]
theorem card_vertex {s t : ℕ} (hs : 1 ≤ s) (ht : 3 ≤ t) :
    Fintype.card (Vertex s t) = (s + 1) * t ^ 2 := by
  have hpos := cliqueSize_pos hs ht
  simp only [Vertex, Fintype.card_sum, Fintype.card_fin, Fintype.card_prod]
  unfold cliqueSize at hpos ⊢
  have hA : 1 ≤ (s + 1) * t * (t - 1) := by omega
  calc
    (s + 1) * t * (t - 1) - 1 + (t + 1 + t * s) =
        ((s + 1) * t * (t - 1) - 1 + 1) + (t + t * s) := by omega
    _ = (s + 1) * t * (t - 1) + (t + t * s) := by
      rw [Nat.sub_add_cancel hA]
    _ = (s + 1) * t * (t - 1) + (s + 1) * t := by ring
    _ = (s + 1) * t * ((t - 1) + 1) := by ring
    _ = (s + 1) * t ^ 2 := by
      rw [Nat.sub_add_cancel (by omega : 1 ≤ t)]
      ring

/-- Every equality-family graph is connected. -/
@[category API, AMS 5]
theorem connected {s t : ℕ} (hs : 1 ≤ s) (ht : 3 ≤ t) : (graph s t).Connected := by
  let c₀ : Fin (cliqueSize s t) := ⟨0, cliqueSize_pos hs ht⟩
  rw [connected_iff_exists_forall_reachable]
  refine ⟨.inl c₀, ?_⟩
  rintro (c | h | ⟨i, b⟩)
  · by_cases hc : c₀ = c
    · subst c
      exact .rfl
    · exact ((adj_clique_clique c₀ c).2 hc).reachable
  · exact (adj_clique_hub c₀ h).reachable
  · let h : Fin (t + 1) := i.castSucc
    exact (adj_clique_hub c₀ h).reachable.trans ((adj_hub_block h i b).2 rfl).reachable

/-- A coloring-like slot map used to bound independent sets. -/
def slot {s t : ℕ} : Vertex s t → Fin (t + 1)
  | .inl _ => Fin.last t
  | .inr (.inl h) => h
  | .inr (.inr (i, _)) => i.castSucc

/-- Distinct vertices occupying one slot are adjacent. -/
@[category API, AMS 5]
theorem adj_of_ne_of_slot_eq {s t : ℕ} {u v : Vertex s t} (huv : u ≠ v)
    (hslot : slot u = slot v) : (graph s t).Adj u v := by
  rcases u with c | h | ⟨i, b⟩ <;>
    rcases v with d | k | ⟨j, c⟩ <;>
    simp_all [slot]
  · exact Fin.castSucc_ne_last j hslot.symm
  · exact (congrArg Fin.val hslot).symm

/-- A slot map whose fibers are cliques bounds the independence number. -/
@[category API, AMS 5]
theorem indepNum_le_of_slot {α : Type*} [Fintype α] (G : SimpleGraph α) (n : ℕ)
    (f : α → Fin n) (hf : ∀ ⦃u v⦄, u ≠ v → f u = f v → G.Adj u v) : G.indepNum ≤ n := by
  obtain ⟨A, hA⟩ := G.exists_isNIndepSet_indepNum
  rw [← hA.card_eq]
  let e : A → Fin n := fun x => f x
  have he : Function.Injective e := by
    intro u v huv
    apply Subtype.ext
    by_contra hne
    exact (hA.isIndepSet u.property v.property hne) (hf hne huv)
  simpa [e] using Fintype.card_le_of_injective e he

/-- A matching independent set turns a slot upper bound into an exact independence number. -/
@[category API, AMS 5]
theorem indepNum_eq_of_slot {α : Type*} [Fintype α] (G : SimpleGraph α) (n : ℕ)
    (f : α → Fin n) (hf : ∀ ⦃u v⦄, u ≠ v → f u = f v → G.Adj u v)
    (A : Finset α) (hA : G.IsIndepSet (A : Set α)) (hcard : A.card = n) : G.indepNum = n := by
  apply le_antisymm
  · exact indepNum_le_of_slot G n f hf
  · rw [← hcard]
    exact hA.card_le_indepNum

/-- A nonempty complete graph has independence number one. -/
@[category API, AMS 5]
theorem indepNum_eq_one_of_complete {α : Type*} [Fintype α] (G : SimpleGraph α) (x : α)
    (hcomplete : ∀ {u v : α}, u ≠ v → G.Adj u v) : G.indepNum = 1 := by
  refine indepNum_eq_of_slot G 1 (fun _ => 0) (fun {_ _} huv _ => hcomplete huv) {x} ?_ ?_
  · simp [SimpleGraph.IsIndepSet]
  · simp

/-- The independent set consisting of all hubs. -/
def hubs (s t : ℕ) : Finset (Vertex s t) :=
  Finset.univ.map
    { toFun := fun h : Fin (t + 1) => .inr (.inl h)
      inj' := by
        intro h k hhk
        exact Sum.inl.inj (Sum.inr.inj hhk) }

@[category API, AMS 5]
theorem hubs_independent (s t : ℕ) : (graph s t).IsIndepSet (hubs s t : Set (Vertex s t)) := by
  intro u hu v hv _
  simp only [hubs, Finset.mem_coe, Finset.mem_map, Finset.mem_univ, true_and] at hu hv
  obtain ⟨h, rfl⟩ := hu
  obtain ⟨k, rfl⟩ := hv
  exact adj_hub_hub h k

@[simp, category API, AMS 5]
theorem card_hubs (s t : ℕ) : (hubs s t).card = t + 1 := by
  simp [hubs]

/-- The equality-family graph has independence number `t + 1`. -/
@[category API, AMS 5]
theorem indepNum_eq {s t : ℕ} : (graph s t).indepNum = t + 1 := by
  apply le_antisymm
  · exact indepNum_le_of_slot (graph s t) (t + 1) slot fun _ _ => adj_of_ne_of_slot_eq
  · simpa using (hubs_independent s t).card_le_indepNum

/-- All hubs, regarded as vertices in the neighbourhood of a central-clique vertex. -/
def cliqueNeighborHubs {s t : ℕ} (c : Fin (cliqueSize s t)) :
    Finset ((graph s t).neighborSet (.inl c)) :=
  Finset.univ.map
    { toFun := fun h : Fin (t + 1) =>
        ⟨.inr (.inl h), by simp⟩
      inj' := by
        intro h k hhk
        exact Sum.inl.inj (Sum.inr.inj (Subtype.ext_iff.mp hhk)) }

@[category API, AMS 5]
theorem cliqueNeighborHubs_independent {s t : ℕ} (c : Fin (cliqueSize s t)) :
    ((graph s t).induce ((graph s t).neighborSet (.inl c))).IsIndepSet
      (cliqueNeighborHubs c : Set _) := by
  intro u hu v hv _
  simp only [cliqueNeighborHubs, Finset.mem_coe, Finset.mem_map, Finset.mem_univ,
    true_and] at hu hv
  obtain ⟨h, rfl⟩ := hu
  obtain ⟨k, rfl⟩ := hv
  exact adj_hub_hub h k

@[simp, category API, AMS 5]
theorem card_cliqueNeighborHubs {s t : ℕ} (c : Fin (cliqueSize s t)) :
    (cliqueNeighborHubs c).card = t + 1 := by
  simp [cliqueNeighborHubs]

/-- A central-clique vertex has local independence number `t + 1`. -/
@[category API, AMS 5]
theorem localIndep_clique {s t : ℕ} (c : Fin (cliqueSize s t)) :
    indepNeighborsCard (graph s t) (.inl c) = t + 1 := by
  unfold indepNeighborsCard
  refine indepNum_eq_of_slot _ _ (fun x => slot x.1) ?_ (cliqueNeighborHubs c) ?_ ?_
  · intro u v huv hslot
    exact adj_of_ne_of_slot_eq (Subtype.coe_injective.ne huv) hslot
  · exact cliqueNeighborHubs_independent c
  · exact card_cliqueNeighborHubs c

/-- One central-clique neighbor of a support hub. -/
def supportCliqueNeighbor {s t : ℕ} (hs : 1 ≤ s) (ht : 3 ≤ t) (i : Fin t) :
    (graph s t).neighborSet (.inr (.inl i.castSucc)) :=
  ⟨.inl ⟨0, cliqueSize_pos hs ht⟩, by simp⟩

/-- One end-clique neighbor of a support hub. -/
def supportBlockNeighbor {s t : ℕ} (hs : 1 ≤ s) (i : Fin t) :
    (graph s t).neighborSet (.inr (.inl i.castSucc)) :=
  ⟨.inr (.inr (i, ⟨0, hs⟩)), by simp⟩

/-- The two-vertex independent witness in a support hub's neighbourhood. -/
def supportWitness {s t : ℕ} (hs : 1 ≤ s) (ht : 3 ≤ t) (i : Fin t) :
    Finset ((graph s t).neighborSet (.inr (.inl i.castSucc))) :=
  {supportCliqueNeighbor hs ht i, supportBlockNeighbor hs i}

@[category API, AMS 5]
theorem supportWitness_independent {s t : ℕ} (hs : 1 ≤ s) (ht : 3 ≤ t) (i : Fin t) :
    ((graph s t).induce ((graph s t).neighborSet (.inr (.inl i.castSucc)))).IsIndepSet
      (supportWitness hs ht i : Set _) := by
  intro u hu v hv huv
  simp only [supportWitness, Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hu hv
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
  · exact (huv rfl).elim
  · exact adj_clique_block _ _ _
  · exact adj_block_clique _ _ _
  · exact (huv rfl).elim

@[simp, category API, AMS 5]
theorem card_supportWitness {s t : ℕ} (hs : 1 ≤ s) (ht : 3 ≤ t) (i : Fin t) :
    (supportWitness hs ht i).card = 2 := by
  simp [supportWitness, supportCliqueNeighbor, supportBlockNeighbor]

/-- Slots for independent sets in a support hub's neighbourhood. -/
def supportSlot {s t : ℕ} {i : Fin t}
    (x : (graph s t).neighborSet (.inr (.inl i.castSucc))) : Fin 2 :=
  match x.1 with
  | .inl _ => 0
  | .inr (.inl _) => 0
  | .inr (.inr _) => 1

@[category API, AMS 5]
theorem supportSlot_adj {s t : ℕ} {i : Fin t}
    {u v : (graph s t).neighborSet (.inr (.inl i.castSucc))} (huv : u ≠ v)
    (hslot : supportSlot u = supportSlot v) :
    ((graph s t).induce ((graph s t).neighborSet (.inr (.inl i.castSucc)))).Adj u v := by
  rcases u with ⟨u, hu⟩
  rcases v with ⟨v, hv⟩
  rw [mem_neighborSet] at hu hv
  rcases u with c | h | ⟨j, b⟩ <;>
    rcases v with d | k | ⟨l, c⟩ <;>
    simp_all [supportSlot]
  exact ⟨Fin.ext hv, huv (Fin.ext hv)⟩

/-- A support hub has local independence number two. -/
@[category API, AMS 5]
theorem localIndep_support {s t : ℕ} (hs : 1 ≤ s) (ht : 3 ≤ t) (i : Fin t) :
    indepNeighborsCard (graph s t) (.inr (.inl i.castSucc)) = 2 := by
  unfold indepNeighborsCard
  refine indepNum_eq_of_slot _ 2 (supportSlot (s := s) (t := t) (i := i))
    (fun {_ _} huv hslot => supportSlot_adj (s := s) (t := t) (i := i) huv hslot)
    (supportWitness hs ht i) ?_ ?_
  · exact supportWitness_independent hs ht i
  · exact card_supportWitness hs ht i

/-- One central-clique neighbor of the extra (non-support) hub. -/
def extraCliqueNeighbor {s t : ℕ} (hs : 1 ≤ s) (ht : 3 ≤ t) :
    (graph s t).neighborSet (.inr (.inl (Fin.last t))) :=
  ⟨.inl ⟨0, cliqueSize_pos hs ht⟩, by simp⟩

@[category API, AMS 5]
theorem extraNeighborhood_complete {s t : ℕ}
    {u v : (graph s t).neighborSet (.inr (.inl (Fin.last t)))} (huv : u ≠ v) :
    ((graph s t).induce ((graph s t).neighborSet (.inr (.inl (Fin.last t))))).Adj u v := by
  rcases u with ⟨u, hu⟩
  rcases v with ⟨v, hv⟩
  rw [mem_neighborSet] at hu hv
  have onlyClique : ∀ {x : Vertex s t},
      (graph s t).Adj (.inr (.inl (Fin.last t))) x → ∃ c, x = .inl c := by
    rintro (c | h | ⟨i, b⟩) hx
    · exact ⟨c, rfl⟩
    · exact (adj_hub_hub _ _ hx).elim
    · have hval := (adj_hub_block (Fin.last t) i b).mp hx
      simp at hval
      omega
  obtain ⟨c, rfl⟩ := onlyClique hu
  obtain ⟨d, rfl⟩ := onlyClique hv
  apply (adj_clique_clique c d).2
  intro hcd
  subst d
  exact huv rfl

/-- The extra hub has local independence number one. -/
@[category API, AMS 5]
theorem localIndep_extra {s t : ℕ} (hs : 1 ≤ s) (ht : 3 ≤ t) :
    indepNeighborsCard (graph s t) (.inr (.inl (Fin.last t))) = 1 := by
  unfold indepNeighborsCard
  exact indepNum_eq_one_of_complete _ (extraCliqueNeighbor hs ht) extraNeighborhood_complete

/-- The support hub, regarded as a neighbor of a vertex in its end clique. -/
def blockHubNeighbor {s t : ℕ} (i : Fin t) (b : Fin s) :
    (graph s t).neighborSet (.inr (.inr (i, b))) :=
  ⟨.inr (.inl i.castSucc), by simp⟩

@[category API, AMS 5]
theorem blockNeighborhood_complete {s t : ℕ} {i : Fin t} {b : Fin s}
    {u v : (graph s t).neighborSet (.inr (.inr (i, b)))} (huv : u ≠ v) :
    ((graph s t).induce ((graph s t).neighborSet (.inr (.inr (i, b))))).Adj u v := by
  rcases u with ⟨u, hu⟩
  rcases v with ⟨v, hv⟩
  rw [mem_neighborSet] at hu hv
  rcases u with c | h | ⟨j, d⟩ <;>
    rcases v with e | k | ⟨l, f⟩ <;>
    simp_all
  omega

/-- Every end-clique vertex has local independence number one. -/
@[category API, AMS 5]
theorem localIndep_block {s t : ℕ} (i : Fin t) (b : Fin s) :
    indepNeighborsCard (graph s t) (.inr (.inr (i, b))) = 1 := by
  unfold indepNeighborsCard
  exact indepNum_eq_one_of_complete _ (blockHubNeighbor i b) blockNeighborhood_complete

/-- The sum of the local independence numbers is `(s + 1) * t³`. -/
@[category API, AMS 5]
theorem localIndep_sum {s t : ℕ} (hs : 1 ≤ s) (ht : 3 ≤ t) :
    (∑ v : Vertex s t, indepNeighborsCard (graph s t) v) = (s + 1) * t ^ 3 := by
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fin.sum_univ_castSucc,
    Fintype.sum_prod_type]
  simp_rw [localIndep_clique, localIndep_support hs ht, localIndep_extra hs ht,
    localIndep_block]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  unfold cliqueSize
  have hA : 1 ≤ (s + 1) * t * (t - 1) := by
    exact Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)
  have htSub : t - 1 + 1 = t := Nat.sub_add_cancel (by omega)
  have hquad : (t - 1) * (t + 1) + 1 = t ^ 2 := by
    nlinarith
  calc
    ((s + 1) * t * (t - 1) - 1) * (t + 1) + (t * 2 + 1 + t * s) =
        (((s + 1) * t * (t - 1) - 1) + 1) * (t + 1) + (t + t * s) := by ring
    _ = ((s + 1) * t * (t - 1)) * (t + 1) + (t + t * s) := by
      rw [Nat.sub_add_cancel hA]
    _ = (s + 1) * t * ((t - 1) * (t + 1) + 1) := by ring
    _ = (s + 1) * t ^ 3 := by rw [hquad]; ring

/-- The average local independence number is exactly `t`. -/
@[category API, AMS 5]
theorem averageIndepNeighbors_eq {s t : ℕ} (hs : 1 ≤ s) (ht : 3 ≤ t) :
    averageIndepNeighbors (graph s t) = t := by
  unfold averageIndepNeighbors indepNeighbors
  rw [show (∑ v : Vertex s t, (indepNeighborsCard (graph s t) v : ℝ)) =
      (((s + 1) * t ^ 3 : ℕ) : ℝ) by exact_mod_cast localIndep_sum hs ht]
  rw [card_vertex hs ht]
  have hsR : ((s + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have htR : (t : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp

/-- The neighbor corresponding to an index in an end clique: the support hub replaces the
vertex itself. -/
def blockNeighborOfIndex {s t : ℕ} (i : Fin t) (b d : Fin s) :
    (graph s t).neighborSet (.inr (.inr (i, b))) :=
  if h : d = b then blockHubNeighbor i b
  else ⟨.inr (.inr (i, d)), by simp [Ne.symm h]⟩

/-- Recover the end-clique index represented by a neighbor. -/
def blockNeighborIndex {s t : ℕ} {i : Fin t} {b : Fin s}
    (x : (graph s t).neighborSet (.inr (.inr (i, b)))) : Fin s :=
  match x.1 with
  | .inl _ => b
  | .inr (.inl _) => b
  | .inr (.inr (_, d)) => d

/-- The neighborhood of an end-clique vertex is in bijection with `Fin s`. -/
def blockNeighborEquiv {s t : ℕ} (i : Fin t) (b : Fin s) :
    Fin s ≃ (graph s t).neighborSet (.inr (.inr (i, b))) where
  toFun := blockNeighborOfIndex i b
  invFun := blockNeighborIndex
  left_inv := by
    intro d
    by_cases h : d = b
    · subst d
      simp [blockNeighborOfIndex, blockNeighborIndex, blockHubNeighbor]
    · simp [blockNeighborOfIndex, blockNeighborIndex, h]
  right_inv := by
    rintro ⟨x, hx⟩
    apply Subtype.ext
    rw [mem_neighborSet] at hx
    rcases x with c | h | ⟨j, d⟩
    · exact (adj_block_clique i b c hx).elim
    · have hhi := (adj_block_hub i b h).mp hx
      have : h = i.castSucc := Fin.ext hhi
      subst h
      simp [blockNeighborOfIndex, blockNeighborIndex, blockHubNeighbor]
    · obtain ⟨rfl, hbd⟩ := (adj_block_block i j b d).mp hx
      simp [blockNeighborOfIndex, blockNeighborIndex, Ne.symm hbd]

/-- Every vertex in an end clique has degree `s`. -/
@[category API, AMS 5]
theorem degree_block {s t : ℕ} (i : Fin t) (b : Fin s) :
    (graph s t).degree (.inr (.inr (i, b))) = s := by
  rw [← card_neighborSet_eq_degree]
  simpa using Fintype.card_congr (blockNeighborEquiv i b).symm

/-- The central clique is large enough to supply `s` distinct neighbors. -/
@[category API, AMS 5]
theorem s_le_cliqueSize {s t : ℕ} (hs : 1 ≤ s) (ht : 3 ≤ t) :
    s ≤ cliqueSize s t := by
  have hA : 1 ≤ (s + 1) * t * (t - 1) :=
    Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)
  have hEq : cliqueSize s t + 1 = (s + 1) * t * (t - 1) := by
    unfold cliqueSize
    exact Nat.sub_add_cancel hA
  have hlarge : 6 * (s + 1) ≤ (s + 1) * t * (t - 1) := by
    calc
      6 * (s + 1) = (s + 1) * 3 * 2 := by ring
      _ ≤ (s + 1) * t * (t - 1) :=
        Nat.mul_le_mul (Nat.mul_le_mul (by omega) ht) (by omega)
  omega

/-- Inject `Fin s` into the neighborhood of a central-clique vertex, replacing the vertex itself
by the extra hub if it occurs among the chosen indices. -/
def cliqueDegreeInjection {s t : ℕ} (hs : 1 ≤ s) (ht : 3 ≤ t)
    (c : Fin (cliqueSize s t)) (d : Fin s) : (graph s t).neighborSet (.inl c) :=
  let q : Fin (cliqueSize s t) := Fin.castLE (s_le_cliqueSize hs ht) d
  if h : q = c then ⟨.inr (.inl (Fin.last t)), by simp⟩
  else ⟨.inl q, (adj_clique_clique c q).2 (Ne.symm h)⟩

@[category API, AMS 5]
theorem cliqueDegreeInjection_injective {s t : ℕ} (hs : 1 ≤ s) (ht : 3 ≤ t)
    (c : Fin (cliqueSize s t)) : Function.Injective (cliqueDegreeInjection hs ht c) := by
  intro d e hde
  let qd : Fin (cliqueSize s t) := Fin.castLE (s_le_cliqueSize hs ht) d
  let qe : Fin (cliqueSize s t) := Fin.castLE (s_le_cliqueSize hs ht) e
  by_cases hd : qd = c
  · by_cases he : qe = c
    · apply Fin.ext
      simpa [qd, qe] using
        congrArg (fun z : Fin (cliqueSize s t) => z.val) (hd.trans he.symm)
    · have := congrArg Subtype.val hde
      simp [cliqueDegreeInjection, qd, qe, hd, he] at this
  · by_cases he : qe = c
    · have := congrArg Subtype.val hde
      simp [cliqueDegreeInjection, qd, qe, hd, he] at this
    · have hq : qd = qe := by
        have hval := congrArg Subtype.val hde
        simpa [cliqueDegreeInjection, qd, qe, hd, he] using hval
      apply Fin.ext
      simpa [qd, qe] using congrArg (fun z : Fin (cliqueSize s t) => z.val) hq

/-- The `s` end-clique vertices give distinct neighbors of their support hub. -/
def supportDegreeInjection {s t : ℕ} (i : Fin t) (d : Fin s) :
    (graph s t).neighborSet (.inr (.inl i.castSucc)) :=
  ⟨.inr (.inr (i, d)), by simp⟩

@[category API, AMS 5]
theorem supportDegreeInjection_injective {s t : ℕ} (i : Fin t) :
    Function.Injective (supportDegreeInjection (s := s) i) := by
  intro d e hde
  simpa [supportDegreeInjection] using congrArg Subtype.val hde

/-- The first `s` central-clique vertices give distinct neighbors of the extra hub. -/
def extraDegreeInjection {s t : ℕ} (hs : 1 ≤ s) (ht : 3 ≤ t) (d : Fin s) :
    (graph s t).neighborSet (.inr (.inl (Fin.last t))) :=
  ⟨.inl (Fin.castLE (s_le_cliqueSize hs ht) d), by simp⟩

@[category API, AMS 5]
theorem extraDegreeInjection_injective {s t : ℕ} (hs : 1 ≤ s) (ht : 3 ≤ t) :
    Function.Injective (extraDegreeInjection hs ht) := by
  intro d e hde
  have hq : Fin.castLE (s_le_cliqueSize hs ht) d =
      Fin.castLE (s_le_cliqueSize hs ht) e := by
    simpa [extraDegreeInjection] using congrArg Subtype.val hde
  apply Fin.ext
  exact congrArg (fun z : Fin (cliqueSize s t) => z.val) hq

/-- Every vertex has degree at least `s`. -/
@[category API, AMS 5]
theorem s_le_degree {s t : ℕ} (hs : 1 ≤ s) (ht : 3 ≤ t) (v : Vertex s t) :
    s ≤ (graph s t).degree v := by
  rw [← card_neighborSet_eq_degree]
  rcases v with c | h | ⟨i, b⟩
  · simpa using Fintype.card_le_of_injective (cliqueDegreeInjection hs ht c)
      (cliqueDegreeInjection_injective hs ht c)
  · refine Fin.lastCases ?_ (fun i => ?_) h
    · simpa using Fintype.card_le_of_injective (extraDegreeInjection hs ht)
        (extraDegreeInjection_injective hs ht)
    · simpa using Fintype.card_le_of_injective (supportDegreeInjection (s := s) i)
        (supportDegreeInjection_injective i)
  · rw [card_neighborSet_eq_degree, degree_block]

/-- The equality-family graph has minimum degree `s`. -/
@[category API, AMS 5]
theorem minDegree_eq {s t : ℕ} (hs : 1 ≤ s) (ht : 3 ≤ t) :
    (graph s t).minDegree = s := by
  letI : Nonempty (Vertex s t) := ⟨.inl ⟨0, cliqueSize_pos hs ht⟩⟩
  apply le_antisymm
  · let i : Fin t := ⟨0, by omega⟩
    let b : Fin s := ⟨0, by omega⟩
    simpa [degree_block] using (graph s t).minDegree_le_degree (.inr (.inr (i, b)))
  · exact (graph s t).le_minDegree_of_forall_le_degree s (s_le_degree hs ht)

/-- Every neighbor of an end-clique vertex is either in the same end clique or is its unique
support hub. -/
@[category API, AMS 5]
theorem adj_block_cases {s t : ℕ} {i : Fin t} {d : Fin s} {x : Vertex s t}
    (h : (graph s t).Adj (.inr (.inr (i, d))) x) :
    x = .inr (.inl i.castSucc) ∨ ∃ e : Fin s, x = .inr (.inr (i, e)) := by
  rcases x with c | k | ⟨j, e⟩
  · exact (adj_block_clique i d c h).elim
  · left
    exact congrArg (fun q : Fin (t + 1) => Sum.inr (Sum.inl q))
      (Fin.ext ((adj_block_hub i d k).mp h))
  · right
    obtain ⟨rfl, -⟩ := (adj_block_block i j d e).mp h
    exact ⟨e, rfl⟩

/-- In a Hamiltonian path, every pendant end clique must contain a path endpoint. -/
@[category API, AMS 5]
theorem block_contains_endpoint {s t : ℕ} (hs : 1 ≤ s) (i : Fin t)
    {a z : Vertex s t} (p : (graph s t).Walk a z) (hp : p.IsHamiltonian) :
    ∃ d : Fin s, (.inr (.inr (i, d)) : Vertex s t) = a ∨
      (.inr (.inr (i, d)) : Vertex s t) = z := by
  let e := hp.getVertEquiv
  let pos : Fin s → Fin p.support.length := fun d => e.symm (.inr (.inr (i, d)))
  let positions : Finset (Fin p.support.length) := Finset.univ.image pos
  let d₀ : Fin s := ⟨0, by omega⟩
  have hpositions : positions.Nonempty := by
    exact ⟨pos d₀, by simp [positions]⟩
  let lo := positions.min' hpositions
  let hi := positions.max' hpositions
  have hloMem : lo ∈ positions := positions.min'_mem hpositions
  have hhiMem : hi ∈ positions := positions.max'_mem hpositions
  obtain ⟨dlo, -, hdlo⟩ := Finset.mem_image.mp hloMem
  obtain ⟨dhi, -, hdhi⟩ := Finset.mem_image.mp hhiMem
  have hloVert : p.getVert lo.val = (.inr (.inr (i, dlo)) : Vertex s t) := by
    rw [← hdlo]
    simpa [e, pos] using e.apply_symm_apply (.inr (.inr (i, dlo)) : Vertex s t)
  have hhiVert : p.getVert hi.val = (.inr (.inr (i, dhi)) : Vertex s t) := by
    rw [← hdhi]
    simpa [e, pos] using e.apply_symm_apply (.inr (.inr (i, dhi)) : Vertex s t)
  have hlohi : lo ≤ hi := positions.min'_le_max' hpositions
  by_contra hendpoint
  have hnotEndpoint : ∀ d : Fin s,
      (.inr (.inr (i, d)) : Vertex s t) ≠ a ∧
        (.inr (.inr (i, d)) : Vertex s t) ≠ z := by
    intro d
    constructor
    · intro h
      exact hendpoint ⟨d, Or.inl h⟩
    · intro h
      exact hendpoint ⟨d, Or.inr h⟩
  have hloPos : 0 < lo.val := by
    apply Nat.pos_of_ne_zero
    intro hlo
    apply (hnotEndpoint dlo).1
    rw [← hloVert, hlo, p.getVert_zero]
  have hhiLe : hi.val ≤ p.length := by
    have := hi.isLt
    have hlength := p.length_support
    omega
  have hhiLt : hi.val < p.length := by
    apply lt_of_le_of_ne hhiLe
    intro hhi
    apply (hnotEndpoint dhi).2
    rw [← hhiVert, hhi, p.getVert_length]
  have hprev : (graph s t).Adj (.inr (.inr (i, dlo)))
      (p.getVert (lo.val - 1)) := by
    have hprevLt : lo.val - 1 < p.length := by
      have hlohiVal : lo.val ≤ hi.val := hlohi
      omega
    have h := (p.adj_getVert_succ (i := lo.val - 1) hprevLt).symm
    rw [Nat.sub_add_cancel hloPos] at h
    simpa [hloVert] using h
  have hnext : (graph s t).Adj (.inr (.inr (i, dhi)))
      (p.getVert (hi.val + 1)) := by
    simpa [hhiVert] using p.adj_getVert_succ (i := hi.val) hhiLt
  have hprevHub : p.getVert (lo.val - 1) =
      (.inr (.inl i.castSucc) : Vertex s t) := by
    rcases adj_block_cases hprev with hhub | ⟨d, hd⟩
    · exact hhub
    · exfalso
      have hkLt : lo.val - 1 < p.support.length := by
        have := lo.isLt
        omega
      let k : Fin p.support.length := ⟨lo.val - 1, hkLt⟩
      have hkpos : pos d = k := by
        apply e.injective
        rw [e.apply_symm_apply]
        simpa [e, k] using hd.symm
      have hkMem : k ∈ positions := by
        exact Finset.mem_image.mpr ⟨d, Finset.mem_univ d, hkpos⟩
      have hle := positions.min'_le k hkMem
      have hlt : k < lo := by
        change lo.val - 1 < lo.val
        omega
      exact (not_le_of_gt hlt) hle
  have hnextHub : p.getVert (hi.val + 1) =
      (.inr (.inl i.castSucc) : Vertex s t) := by
    rcases adj_block_cases hnext with hhub | ⟨d, hd⟩
    · exact hhub
    · exfalso
      have hkLt : hi.val + 1 < p.support.length := by
        have hlength := p.length_support
        omega
      let k : Fin p.support.length := ⟨hi.val + 1, hkLt⟩
      have hkpos : pos d = k := by
        apply e.injective
        rw [e.apply_symm_apply]
        simpa [e, k] using hd.symm
      have hkMem : k ∈ positions := by
        exact Finset.mem_image.mpr ⟨d, Finset.mem_univ d, hkpos⟩
      have hle := positions.le_max' k hkMem
      have hlt : hi < k := by
        change hi.val < hi.val + 1
        omega
      exact (not_le_of_gt hlt) hle
  have heq : p.getVert (lo.val - 1) = p.getVert (hi.val + 1) :=
    hprevHub.trans hnextHub.symm
  have hprevLe : lo.val - 1 ≤ p.length := by
    have hlohiVal : lo.val ≤ hi.val := hlohi
    omega
  have hnextLe : hi.val + 1 ≤ p.length := by omega
  have hindices : lo.val - 1 = hi.val + 1 :=
    hp.isPath.getVert_injOn hprevLe hnextLe heq
  have hlohiVal : lo.val ≤ hi.val := hlohi
  omega

/-- No member of the equality family with `t ≥ 3` has a Hamiltonian path. -/
@[category API, AMS 5]
theorem no_hamiltonian_path {s t : ℕ} (hs : 1 ≤ s) (ht : 3 ≤ t) :
    ¬ ∃ a z : Vertex s t, ∃ p : (graph s t).Walk a z, p.IsHamiltonian := by
  rintro ⟨a, z, p, hp⟩
  let i₀ : Fin t := ⟨0, by omega⟩
  let i₁ : Fin t := ⟨1, by omega⟩
  let i₂ : Fin t := ⟨2, by omega⟩
  obtain ⟨d₀, h₀⟩ := block_contains_endpoint hs i₀ p hp
  obtain ⟨d₁, h₁⟩ := block_contains_endpoint hs i₁ p hp
  obtain ⟨d₂, h₂⟩ := block_contains_endpoint hs i₂ p hp
  rcases h₀ with h₀a | h₀z <;>
    rcases h₁ with h₁a | h₁z <;>
    rcases h₂ with h₂a | h₂z
  all_goals first
    | exact (by simpa [i₀, i₁] using h₀a.trans h₁a.symm)
    | exact (by simpa [i₀, i₂] using h₀a.trans h₂a.symm)
    | exact (by simpa [i₁, i₂] using h₁a.trans h₂a.symm)
    | exact (by simpa [i₀, i₁] using h₀z.trans h₁z.symm)
    | exact (by simpa [i₀, i₂] using h₀z.trans h₂z.symm)
    | exact (by simpa [i₁, i₂] using h₁z.trans h₂z.symm)

/-- Every member of the family satisfies the numerical hypothesis of Conjecture 194. -/
@[category API, AMS 5]
theorem satisfies_conjecture_hypothesis {s t : ℕ} (hs : 1 ≤ s) (ht : 3 ≤ t) :
    ((graph s t).indepNum : ℝ) ≤ 1 + averageIndepNeighbors (graph s t) := by
  rw [indepNum_eq, averageIndepNeighbors_eq hs ht]
  norm_num
  linarith

/-- The complete machine-checked certificate for the two-parameter counterexample family. -/
@[category research solved, AMS 5]
theorem family_certificate {s t : ℕ} (hs : 1 ≤ s) (ht : 3 ≤ t) :
    Fintype.card (Vertex s t) = (s + 1) * t ^ 2 ∧
    (graph s t).Connected ∧
    (graph s t).indepNum = t + 1 ∧
    averageIndepNeighbors (graph s t) = t ∧
    (graph s t).minDegree = s ∧
    ((graph s t).indepNum : ℝ) ≤ 1 + averageIndepNeighbors (graph s t) ∧
    ¬ ∃ a z : Vertex s t, ∃ p : (graph s t).Walk a z, p.IsHamiltonian := by
  exact ⟨card_vertex hs ht, connected hs ht, indepNum_eq,
    averageIndepNeighbors_eq hs ht, minDegree_eq hs ht,
    satisfies_conjecture_hypothesis hs ht, no_hamiltonian_path hs ht⟩

end WrittenOnTheWallII.GraphConjecture194.Family
