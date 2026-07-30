import WOWII217Finite13ClosureSharedDeg
import WOWII217Connected12
import WOWII217ClosureCertificateSemantics
import WOWII217FiniteBase

#check SimpleGraph.connected_iff_exists_forall_reachable
#check SimpleGraph.Connected.iff
#check SimpleGraph.ConnectedComponent
#check SimpleGraph.ConnectedComponent.support
#check SimpleGraph.ConnectedComponent.mem_supp_of_adj_mem_supp
#check SimpleGraph.ConnectedComponent.mem_supp_congr_adj
#check SimpleGraph.ConnectedComponent.degree_induce_eq
#check SimpleGraph.Finite.degree_lt_card_verts
#check Fintype.card_subtype_iff
#check SetLike.exists
#check Finset.card_filter
#check Fintype.card_fin

#check WOWII217FiniteBase.degreeUpperNat
#check WOWII217ClosureSemantics.graphOfUpper
#check WOWII217ClosureSemantics.graphOfUpper_eq_addEligibleEdges13_of_rel
#check WOWII217Relabel13.traceable_of_degreeCounts_6666666555555
#check WOWII217ClosureSemantics.traceable_graphOfUpper_rel13_iff

open SimpleGraph WOWII217ClosureSemantics WOWII217FiniteBase
#check (fun (g : BitVec 78) => WOWII217ClosureSemantics.graphOfUpper (n := 13) g)
#check connectedUpper
#check WOWII217ClosureSemantics.degree_graphOfUpper_eq

example (g : BitVec 78) : True := by
  have h := SimpleGraph.ConnectedComponent.eq
  native_decide
