import WOWII217FiniteSmallExceptionsChunks.Chunk013
import WOWII217Encoding8
import WOWII217Connected8
import WOWII217Degree8
import WOWII217ClosureSemanticsSmall
import WOWII217ClosureBridge
import WOWII217BondyChvatal

namespace E2E

open SimpleGraph WOWII217FiniteBase WOWII217Closure WOWII217ClosureSemantics
open WOWII217BondyChvatal WOWII217ClosureSemanticsSmall WOWII217ClosureBridge
open WOWII217Encoding8 WOWII217Connected8 WOWII217Degree8
open WOWII217FiniteSmallExceptions

/-- END-TO-END: from an abstract graph on `Fin 8` with a given degree sequence
(in vertex order) to `Traceable`. This is the "certified" hypothesis that
`DegSort.traceable_of_degreeOrder` consumes.

Chain: encode → connectedUpper → fixedDegreeSequenceUpper → chunk theorem →
completeUpper → traceable of closure → BRIDGE → traceable of original. -/
theorem certified_8_66555531 (H : SimpleGraph (Fin 8)) [DecidableRel H.Adj]
    (conn : H.Connected)
    (degs : List.ofFn (fun v : Fin 8 => H.degree v) = [6, 6, 5, 5, 5, 5, 3, 1]) :
    Traceable H := by
  have hconn : connectedUpper (n := 8) (encodeUpper8 H) = true :=
    connectedUpper_of_connected_graphOfUpper8 _ (by rw [graphOfUpper_encodeUpper8]; exact conn)
  have hdeg : fixedDegreeSequenceUpper (n := 8) (encodeUpper8 H) [6, 6, 5, 5, 5, 5, 3, 1] = true :=
    fixedDegreeSequenceUpper_encodeUpper8_of_degreeSequence H _ degs
  have hcomplete := connected_degreeSequence_66555531_closes (encodeUpper8 H) hconn hdeg
  have htrace := traceable_graphOfUpper_of_completeUpper8 _ hcomplete
  have hbridge := Iff.mp
    (traceable_graphOfUpper_pathClosureParallelRounds_iff (by norm_num)) htrace
  rwa [graphOfUpper_encodeUpper8] at hbridge

end E2E

