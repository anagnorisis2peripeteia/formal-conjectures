import Mathlib
open SimpleGraph
variable {V : Type} [Fintype V] [DecidableEq V] [Nonempty V]
variable (G : SimpleGraph V)
#check (inferInstance : Fintype (G.connectedComponentMk (Classical.choice ‹Nonempty V›)).supp)
#check (inferInstance : Fintype (G.connectedComponentMk (Classical.choice ‹Nonempty V›)))
#check Fintype.card_coe
example (v : V) : Fintype.card (G.connectedComponentMk v) = (G.connectedComponentMk v).supp.toFinset.card := by
  simpa [Set.toFinset_card]
