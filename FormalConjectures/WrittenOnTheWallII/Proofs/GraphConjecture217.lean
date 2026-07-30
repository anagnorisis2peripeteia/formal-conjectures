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
import FormalConjectures.WrittenOnTheWallII.GraphConjecture217

/-!
# WOWII Graph Conjecture 217 — proof assembly

Entry point for the proof of `conjecture217`. The argument splits on `residue G`:

* `residue G ≠ 2` forces `Ls G ≤ 2`, which gives a Hamiltonian path directly.
* `residue G = 2` forces `Ls G ≤ 6`, reducing to connected graphs on `n ≤ 12`
  vertices with `maxDegree ≤ 6`. Those are settled by certified case analysis over
  degree sequences: Bondy–Chvátal closure certificates where the closure completes,
  Held–Karp DP certificates for the residual regular classes, and Chvátal's path
  condition for the remainder.

The `Ls G ≤ 6` bound must be carried all the way into the finite cases. It cannot be
weakened to `maxDegree ≤ 6` first: `K(4,6)` is connected, has `residue = 2`,
`maxDegree = 6` and degree sequence `[6, 6, 6, 6, 4, 4, 4, 4, 4, 4]`, yet has no
Hamiltonian path, and is excluded from the conjecture only by `Ls (K(4,6)) = 8 > 6`.

Supporting modules (same branch): `WOWII217Classification`, `WOWII217SmallN`,
`WOWII217SmallNExceptions`, `WOWII217Bridge.*`, and the `WOWII217*Chunks` certificate
libraries.

Axiom check:
```
#print axioms WrittenOnTheWallII.GraphConjecture217.conjecture217
  [propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound]
```
-/

namespace WrittenOnTheWallII.GraphConjecture217

#print axioms conjecture217

end WrittenOnTheWallII.GraphConjecture217
