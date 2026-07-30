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
import FormalConjectures.WrittenOnTheWallII.GraphConjecture101

/-!
# Written on the Wall II - Conjecture 72
-/

namespace WrittenOnTheWallII.GraphConjecture72

open SimpleGraph
open WrittenOnTheWallII.GraphConjecture101

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj]

/--
WOWII [Conjecture 72](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

For a connected graph `G`, the matching number `matchingNumber G` satisfies
`matchingNumber G ≤ maxEvenDistance G + (alphaCore G).card`.

This conjecture is false; for `K_2`, `matchingNumber = 1`, but `maxEvenDistance = 0`
and `alphaCore` size is 0.
-/
@[category research solved, AMS 5]
theorem conjecture72 : answer(False) ↔
    ∀ (α : Type) [Fintype α] [DecidableEq α] [Nontrivial α]
      (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected),
      matchingNumber G ≤ maxEvenDistance G + (alphaCore G).card := by
  sorry

end WrittenOnTheWallII.GraphConjecture72
