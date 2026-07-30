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

import Mathlib.Combinatorics.SimpleGraph.Hamiltonian

namespace SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Graffiti.pc definition 85: A graph is said to have a Hamiltonian path if there exist
two vertices with a path between them which visits each vertex of the graph exactly once. -/
def hasHamiltonianPath (G : SimpleGraph α) : Prop :=
  ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian

end SimpleGraph
