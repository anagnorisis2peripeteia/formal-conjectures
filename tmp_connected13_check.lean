import WOWII217ClosureSemantics
import WOWII217Closure13Fast
import WOWII217Relabel13
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

#check WOWII217ClosureSemantics.graphOfUpper
#check SimpleGraph.Reachable
#check SimpleGraph.connected_iff_exists_forall_reachable
#check SimpleGraph.ConnectedComponent.mem_supp_of_adj_mem_supp
#check SimpleGraph.Finite.degree_lt_card_verts
#check SimpleGraph.ConnectedComponent.mk
#check SimpleGraph.ConnectedComponent.supp

open SimpleGraph WOWII217FiniteBase WOWII217ClosureSemantics

example (g : BitVec 78) (h : fixedDegreeSequenceUpper (n := 13) g
        [6,6,6,6,6,6,6,5,5,5,5,5,5] = true) : True := by
  have hdeg : 0 = 1 := by omega
  trivial
