import WOWII217Bridge
import WOWII217Encoding

/-!
The certified exceptional-class theorem stated for an ordinary simple graph.
-/

namespace WOWII217Canonical

open WOWII217DP

theorem canonicalSixRegular14Graph_hasHamiltonianWalk
    (G : SimpleGraph (Fin 14)) [DecidableRel G.Adj]
    (connected : connectedUpper (n := 14) (WOWII217Encoding.encodeUpper14 G) = true)
    (sixRegular : fixedDegreeSequenceUpper (n := 14)
      (WOWII217Encoding.encodeUpper14 G)
      [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] = true)
    (zeroNeighborhood : canonicalZeroNeighborhood14
      (WOWII217Encoding.encodeUpper14 G) = true)
    (partitionSorted : canonicalPartitionDegreesSorted14
      (WOWII217Encoding.encodeUpper14 G) = true) :
    ∃ a b : Fin 14, ∃ p : G.Walk a b, p.IsHamiltonian := by
  have certified := WOWII217Bridge.canonicalSixRegular14_hasHamiltonianWalk
    (WOWII217Encoding.encodeUpper14 G) connected sixRegular zeroNeighborhood partitionSorted
  rw [WOWII217Encoding.graphOfUpper14_encodeUpper14 G] at certified
  exact certified

end WOWII217Canonical
