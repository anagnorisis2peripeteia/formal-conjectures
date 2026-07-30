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

import FormalConjecturesUtil

/-!
# Written on the Wall II - Conjecture 199

*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)
-/

namespace WrittenOnTheWallII.GraphConjecture199

open Classical SimpleGraph

/--
The number of triangles containing a vertex $v$.
-/
noncomputable def numTriangles {α : Type} [Fintype α] (G : SimpleGraph α) (v : α) : ℕ :=
  ((G.neighborSet v).toFinset.filter (fun u => ∃ w, w ∈ G.neighborSet v ∧ G.Adj u w)).card / 2

noncomputable def maxTriangles {α : Type} [Fintype α] [Nontrivial α] (G : SimpleGraph α) : ℕ :=
  ((Finset.univ : Finset α).image (numTriangles G)).max' (by
    have h : (Finset.univ : Finset α).Nonempty := Finset.univ_nonempty
    exact h.image _)

noncomputable def minTriangles {α : Type} [Fintype α] [Nontrivial α] (G : SimpleGraph α) : ℕ :=
  ((Finset.univ : Finset α).image (numTriangles G)).min' (by
    have h : (Finset.univ : Finset α).Nonempty := Finset.univ_nonempty
    exact h.image _)

/--
WOWII [Conjecture 199](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

For a simple connected graph $G$,
$\alpha(G) \le \lceil n / 2 + T_{\max} / (1 + T_{\min}) \rceil$
where $T_{\max}$ and $T_{\min}$ are the maximum and minimum number of triangles incident to a vertex.

This conjecture is false. For $K_{1,3}$, $\alpha = 3$, $T_{\max} = T_{\min} = 0$, and
$n/2 + 0 = 2$, so $3 \le \lceil 2 \rceil = 2$ is false.
-/
@[category research solved, AMS 5]
theorem conjecture199 : answer(False) ↔
    ∀ (α : Type) [Fintype α] [DecidableEq α] [Nontrivial α]
      (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected),
      (G.indepNum : ℝ) ≤ ⌈(Fintype.card α : ℝ) / 2 +
          (maxTriangles G : ℝ) / (1 + (minTriangles G : ℝ))⌉ := by
  sorry

end WrittenOnTheWallII.GraphConjecture199
