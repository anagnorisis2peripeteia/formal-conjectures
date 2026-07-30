import Mathlib
open SimpleGraph
variable {V : Type} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V}
#check (show (ConnectedComponent G) from by infer_instance)
#check SimpleGraph.ConnectedComponent.supp
#check SimpleGraph.ConnectedComponent.eq
#check SimpleGraph.ConnectedComponent.mem_supp_of_adj_mem_supp
#check SimpleGraph.ConnectedComponent.mem_supp
#check SimpleGraph.connectedComponentMk
#check SimpleGraph.reachable_iff_exists_walk
#check SimpleGraph.Walk.support
#check SimpleGraph.Walk.reachable_iff_exists_walk
#check SimpleGraph.mem_reachable
#check SimpleGraph.connectedComponentMk
#check (show G.Reachable = True from by rfl)
