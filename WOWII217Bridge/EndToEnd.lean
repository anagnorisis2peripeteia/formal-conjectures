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


/-- GENERAL n=8 form: parameterised by the degree list and the chunk theorem, so each
of the 23 W=28 chunks becomes a one-line instantiation instead of a copy of the chain. -/
theorem certified_8 (ds : List Nat) (H : SimpleGraph (Fin 8)) [DecidableRel H.Adj]
    (chunk : ∀ g : BitVec 28, connectedUpper (n := 8) g = true →
        fixedDegreeSequenceUpper (n := 8) g ds = true →
        completeUpper (n := 8) (pathClosureParallelRounds (n := 8) 4 g) = true)
    (conn : H.Connected)
    (degs : List.ofFn (fun v : Fin 8 => H.degree v) = ds) :
    Traceable H := by
  have hconn : connectedUpper (n := 8) (encodeUpper8 H) = true :=
    connectedUpper_of_connected_graphOfUpper8 _ (by rw [graphOfUpper_encodeUpper8]; exact conn)
  have hdeg : fixedDegreeSequenceUpper (n := 8) (encodeUpper8 H) ds = true :=
    fixedDegreeSequenceUpper_encodeUpper8_of_degreeSequence H _ degs
  have hbridge := Iff.mp
    (traceable_graphOfUpper_pathClosureParallelRounds_iff (by norm_num))
    (traceable_graphOfUpper_of_completeUpper8 _ (chunk (encodeUpper8 H) hconn hdeg))
  rwa [graphOfUpper_encodeUpper8] at hbridge

/-- Chunk013 via the general form -- this is what all 23 W=28 chunks will look like. -/
theorem certified_8_66555531' (H : SimpleGraph (Fin 8)) [DecidableRel H.Adj]
    (conn : H.Connected)
    (degs : List.ofFn (fun v : Fin 8 => H.degree v) = [6, 6, 5, 5, 5, 5, 3, 1]) :
    Traceable H :=
  certified_8 _ H connected_degreeSequence_66555531_closes conn degs

end E2E


