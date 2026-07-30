import Mathlib
#check SimpleGraph.mem_neighborFinset
#check SimpleGraph.mem_neighborSet
#check SimpleGraph.neighborSet
#check SetLike

#check SimpleGraph.degree_induce_of_neighborSet_subset
example {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    {s : Set V} {v : s} (h : ∀ w ∈ G.neighborSet (v : V), w ∈ s) :
    ((G.induce s).degree v) = G.degree (v : V) := by
  simpa using (SimpleGraph.degree_induce_of_neighborSet_subset (G := G) (s := s) v h)
