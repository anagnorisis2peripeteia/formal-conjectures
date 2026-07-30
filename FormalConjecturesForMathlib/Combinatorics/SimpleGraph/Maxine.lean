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
module

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique

namespace SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A list of vertices `L` forms a valid sequence of removals for the maxine greedy algorithm
if each `v ∈ L` has maximum degree in the subgraph induced by `α \ (vertices before v in L)`. -/
def IsMaxineRemovalSequence (G : SimpleGraph α) [DecidableRel G.Adj] (L : List α) : Prop :=
  L.Nodup ∧ 
  (∀ (i : ℕ) (h : i < L.length),
    let v := L.get ⟨i, h⟩
    let prev := L.take i
    let s := (Finset.univ : Finset α) \ prev.toFinset
    ∃ hv : v ∈ s, 
      (G.induce (↑s)).degree ⟨v, hv⟩ > 0 ∧
      ∀ w ∈ s, ∀ hw : w ∈ s,
        (G.induce (↑s)).degree ⟨w, hw⟩ ≤ (G.induce (↑s)).degree ⟨v, hv⟩) ∧
  let s_final := (Finset.univ : Finset α) \ L.toFinset
  ∀ w ∈ s_final, ∀ hw : w ∈ s_final, (G.induce (↑s_final)).degree ⟨w, hw⟩ = 0

/-- Graffiti.pc definition 111: Maxine of G is the order of the largest independent set
that one gets from the greedy algorithm that proceeds by removing a vertex of maximum degree
until the subgraph is discrete. -/
noncomputable def maxine (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  sSup { k | ∃ L : List α, IsMaxineRemovalSequence G L ∧ k = Fintype.card α - L.length }

end SimpleGraph
