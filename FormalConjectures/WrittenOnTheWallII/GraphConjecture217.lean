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
import WOWII217Hamiltonian
import WOWII217Classification

/-!
# Written on the Wall II - Conjecture 217

Per the WOWII definitions popup linked from this conjecture:

- $L(G)$ is the **maximum number of leaves of a spanning tree** of $G$
  — i.e. `Ls G` in our invariant library.
- $\chi_{\mathrm{residue}=2}(G)$ is the **characteristic function** for the
  predicate $\mathrm{residue}\, G = 2$, i.e. $1$ when $\mathrm{residue}\, G = 2$
  and $0$ otherwise.

*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)
-/

namespace WrittenOnTheWallII.GraphConjecture217

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/-- The **characteristic function** for the predicate $\mathrm{residue}\, G = 2$. -/
noncomputable def residueEqTwoIndicator (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  if residue G = 2 then 1 else 0

theorem residueEqTwoIndicator_eq_zero_of_ne
    (G : SimpleGraph α) [DecidableRel G.Adj] (h : residue G ≠ 2) :
    residueEqTwoIndicator G = 0 := by
  simp [residueEqTwoIndicator, h]

theorem residueEqTwoIndicator_eq_one_of_eq
    (G : SimpleGraph α) [DecidableRel G.Adj] (h : residue G = 2) :
    residueEqTwoIndicator G = 1 := by
  simp [residueEqTwoIndicator, h]

theorem Ls_le_two_of_residue_ne_two
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (hRes : residue G ≠ 2)
    (hL : Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2) :
    Ls G ≤ 2 := by
  have hInd : residueEqTwoIndicator G = 0 :=
    residueEqTwoIndicator_eq_zero_of_ne G hRes
  have h0 : Ls G ≤ 4 * (0 : ℝ) + 2 := by
    simpa [hInd] using hL
  have h2 : Ls G ≤ (2 : ℝ) := by
    convert h0 using 1
    norm_num
  exact_mod_cast h2

theorem Ls_le_six_of_residue_eq_two
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (hRes : residue G = 2)
    (hL : Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2) :
    Ls G ≤ 6 := by
  have hInd : residueEqTwoIndicator G = 1 :=
    residueEqTwoIndicator_eq_one_of_eq G hRes
  have h4 : Ls G ≤ 4 * (1 : ℝ) + 2 := by
    simpa [hInd] using hL
  have h6 : Ls G ≤ (6 : ℝ) := by
    convert h4 using 1
    norm_num
  exact_mod_cast h6

/-- Easy half of Conjecture 217: when residue ≠ 2 the hypothesis forces
`Ls ≤ 2`, hence a Hamiltonian path. -/
theorem conjecture217_of_residue_ne_two
    (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected)
    (hRes : residue G ≠ 2)
    (hL : Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2) :
    ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian := by
  exact exists_hamiltonianPath_of_Ls_le_two G h (Ls_le_two_of_residue_ne_two G hRes hL)

/--
WOWII [Conjecture 217](http://cms.uhd.edu/faculty/delavinae/research/wowII/all.html#conj217):

If $G$ is a finite simple connected graph on $n > 1$ vertices and
$L_s(G) \le 4 \cdot \chi_{\mathrm{residue}=2}(G) + 2$,
then $G$ has a Hamiltonian path.
-/
@[category research open, AMS 5]
theorem conjecture217 (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected)
    (hL : Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2) :
    ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian := by
  by_cases hRes : residue G = 2
  · have hL6 : Ls G ≤ 6 := Ls_le_six_of_residue_eq_two G hRes hL
    exact WOWII217Classification.hamiltonian_of_residue_eq_two_and_Ls_le_six G h hRes hL6
  · exact conjecture217_of_residue_ne_two G h hRes hL

-- Sanity checks

@[category test, AMS 5]
example (G : SimpleGraph (Fin 4)) [DecidableRel G.Adj] :
    residueEqTwoIndicator G ≤ 1 := by
  unfold residueEqTwoIndicator; split <;> simp

@[category test, AMS 5]
example (G : SimpleGraph (Fin 4)) [DecidableRel G.Adj] :
    0 ≤ residueEqTwoIndicator G := Nat.zero_le _

end WrittenOnTheWallII.GraphConjecture217
