/-
Copyright 2025 The Formal Conjectures Authors.

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

import FormalConjecturesUtil

/-!
# Written on the Wall II - Conjecture 194

*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

## Counterexample

The conjecture is false. Take a clique on vertices `0, ..., 10`, four additional vertices
`11, ..., 14` adjacent to every clique vertex, and three leaves attached at `11`, `12`, and `14`.
This connected graph has independence number `4`, while the sum of the independence numbers of its
vertex neighbourhoods is `54`, so their average is `3`. Thus it satisfies the conjecture's
hypothesis with equality. However, its three leaves would all have to be endpoints of a Hamiltonian
path, which is impossible.
-/

namespace WrittenOnTheWallII.GraphConjecture194

open Classical SimpleGraph

/-- The 18-vertex counterexample described in the module docstring. -/
def counterexample : SimpleGraph (Fin 18) :=
  SimpleGraph.fromRel fun i j =>
    (i.val < 11 ∧ j.val < 11) ∨
    (i.val < 11 ∧ 11 ≤ j.val ∧ j.val < 15) ∨
    (i.val = 11 ∧ j.val = 15) ∨
    (i.val = 12 ∧ j.val = 16) ∨
    (i.val = 14 ∧ j.val = 17)

instance : DecidableRel counterexample.Adj := by
  unfold counterexample
  infer_instance

@[category API, AMS 5]
private lemma leaf_is_endpoint {α : Type*} [DecidableEq α] {G : SimpleGraph α}
    {a b leaf neighbour : α} (p : G.Walk a b) (hp : p.IsHamiltonian)
    (hleaf : ∀ v, G.Adj leaf v ↔ v = neighbour) : leaf = a ∨ leaf = b := by
  let i : Fin p.support.length := (hp.getVertEquiv).symm leaf
  have hi : p.getVert i.val = leaf := hp.getVertEquiv.apply_symm_apply leaf
  by_cases hi0 : i.val = 0
  · left
    simpa [hi0] using hi.symm
  by_cases hilast : i.val = p.length
  · right
    simpa [hilast] using hi.symm
  have hile : i.val ≤ p.length := by
    have := i.isLt
    simpa [p.length_support] using this
  have hilt : i.val < p.length := lt_of_le_of_ne hile hilast
  have hipos : 0 < i.val := Nat.pos_of_ne_zero hi0
  have hprev : G.Adj leaf (p.getVert (i.val - 1)) := by
    have h := (p.adj_getVert_succ (i := i.val - 1) (by omega : i.val - 1 < p.length)).symm
    rw [Nat.sub_add_cancel hipos] at h
    simpa [hi] using h
  have hnext : G.Adj leaf (p.getVert (i.val + 1)) := by
    simpa [hi] using p.adj_getVert_succ (i := i.val) hilt
  have heq : p.getVert (i.val - 1) = p.getVert (i.val + 1) :=
    (hleaf _).mp hprev |>.trans ((hleaf _).mp hnext).symm
  have hindices : i.val - 1 = i.val + 1 := hp.isPath.getVert_injOn
    (by simp; omega) (by simp; omega) heq
  omega

@[category test, AMS 5]
theorem counterexample_connected : counterexample.Connected := by
  native_decide

@[category test, AMS 5]
theorem counterexample_indep_num : counterexample.indepNum = 4 := by
  rw [SimpleGraph.indep_num_eq_computable]
  native_decide

@[category test, AMS 5]
theorem counterexample_local_indep_sum :
    (∑ v : Fin 18, (counterexample.induce (counterexample.neighborSet v)).indepNum) = 54 := by
  simp_rw [SimpleGraph.indep_num_eq_computable]
  native_decide

@[category test, AMS 5]
theorem counterexample_average_indep_neighbors : averageIndepNeighbors counterexample = 3 := by
  unfold averageIndepNeighbors indepNeighbors indepNeighborsCard
  rw [show (∑ v : Fin 18,
      ((counterexample.induce (counterexample.neighborSet v)).indepNum : ℝ)) = 54 by
    exact_mod_cast counterexample_local_indep_sum]
  norm_num

@[category test, AMS 5]
theorem counterexample_no_hamiltonian_path :
    ¬ ∃ a b : Fin 18, ∃ p : counterexample.Walk a b, p.IsHamiltonian := by
  rintro ⟨a, b, p, hp⟩
  have h15 : ∀ v, counterexample.Adj 15 v ↔ v = 11 := by native_decide
  have h16 : ∀ v, counterexample.Adj 16 v ↔ v = 12 := by native_decide
  have h17 : ∀ v, counterexample.Adj 17 v ↔ v = 14 := by native_decide
  have e15 := leaf_is_endpoint p hp h15
  have e16 := leaf_is_endpoint p hp h16
  have e17 := leaf_is_endpoint p hp h17
  rcases e15 with h15a | h15b <;>
    rcases e16 with h16a | h16b <;>
    rcases e17 with h17a | h17b <;> omega

/--
WOWII [Conjecture 194](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

For a simple connected graph `G`, if `α(G) ≤ 1 + l_avg(G)`, then `G` has a Hamiltonian path.
Here `α(G) = G.indepNum` is the independence number, and
`l_avg(G) = averageIndepNeighbors G` is the average over all vertices of the independence number
of the neighbourhood.
A Hamiltonian path is a walk visiting every vertex exactly once. The answer is no, as witnessed by
the 18-vertex graph described above.
-/
@[category research solved, AMS 5]
theorem conjecture194 : answer(False) ↔
    ∀ (α : Type) [Fintype α] [DecidableEq α] [Nontrivial α]
      (G : SimpleGraph α) (_h : G.Connected),
      (G.indepNum : ℝ) ≤ 1 + averageIndepNeighbors G →
      ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian := by
  show False ↔ _
  rw [false_iff]
  intro h
  apply counterexample_no_hamiltonian_path
  apply h (Fin 18) counterexample counterexample_connected
  rw [counterexample_indep_num, counterexample_average_indep_neighbors]
  norm_num

end WrittenOnTheWallII.GraphConjecture194
