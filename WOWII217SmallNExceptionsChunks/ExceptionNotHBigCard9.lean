import WOWII217ClosureSemantics
import WOWII217FiniteSmallExceptions
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Maxine
import WOWII217ClosureSemanticsSmall
import WOWII217ClosureBridge
import WOWII217Encoding4
import WOWII217Connected4
import WOWII217Degree4
import WOWII217Encoding5
import WOWII217Connected5
import WOWII217Degree5
import WOWII217Encoding6
import WOWII217Connected6
import WOWII217Degree6
import WOWII217Encoding7
import WOWII217Connected7
import WOWII217Degree7
import WOWII217Encoding8
import WOWII217Connected8
import WOWII217Degree8
import WOWII217Encoding9
import WOWII217Connected9
import WOWII217Degree9
import WOWII217Encoding10
import WOWII217Connected10
import WOWII217Degree10
import WOWII217Encoding11
import WOWII217Connected11
import WOWII217Degree11
import WOWII217Encoding12
import WOWII217Connected12
import WOWII217Degree12

open SimpleGraph Classical Finset WOWII217ClosureSemantics WOWII217FiniteSmallExceptions WOWII217ClosureBridge
open WOWII217Encoding4 WOWII217Connected4 WOWII217Degree4
open WOWII217Encoding5 WOWII217Connected5 WOWII217Degree5
open WOWII217Encoding6 WOWII217Connected6 WOWII217Degree6
open WOWII217Encoding7 WOWII217Connected7 WOWII217Degree7
open WOWII217Encoding8 WOWII217Connected8 WOWII217Degree8
open WOWII217Encoding9 WOWII217Connected9 WOWII217Degree9
open WOWII217Encoding10 WOWII217Connected10 WOWII217Degree10
open WOWII217Encoding11 WOWII217Connected11 WOWII217Degree11
open WOWII217Encoding12 WOWII217Connected12 WOWII217Degree12

namespace WOWII217SmallNExceptions

theorem exception_not_hBig_card9
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (connected : G.Connected)
    (hCard12 : Fintype.card V ≤ 12)
    (hResidue : residue G = 2)
    (t : ℕ)
    (S : Finset V) (hS : ∀ v, v ∈ S ↔ t ≤ G.degree v)
    (hNotBig : ¬ (Fintype.card V - 1 ≤ 2 * (card S - 1) ∧ 1 ≤ card S))
    (hCard : Fintype.card V = 9) :
  ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  | 9 =>
have hFinTrans : ∃ G_fin : SimpleGraph (Fin 9), [DecidableRel G_fin.Adj] ∧ G_fin.Connected ∧ G_fin.degreeSequence = G.degreeSequence ∧ (Traceable G_fin → Traceable G) := sorry
rcases hFinTrans with ⟨G_fin, _, conn_fin, hSeqEq, hTrans⟩
if hSeq : G_fin.degreeSequence = [6, 6, 6, 6, 6, 6, 6, 3, 1] then
  have hDecide := WOWII217FiniteSmallExceptions.connected_degreeSequence_666666631_closes
    (encodeUpper9 G_fin)
    (connectedUpper_of_connected_graphOfUpper9 _ (by
      rwa [graphOfUpper_encodeUpper9]
    ))
    (by
      rw [← hSeq]
      exact fixedDegreeSequenceUpper_encodeUpper9_of_degreeSequence G_fin
    )
  have traceEncoded := Iff.mp traceable_graphOfUpper_pathClosureParallelRounds_iff (traceable_graphOfUpper_of_completeUpperN (by exact hDecide))
  rwa [graphOfUpper_encodeUpper9] at traceEncoded
  apply hTrans; exact traceEncoded
else if hSeq : G_fin.degreeSequence = [6, 6, 6, 6, 6, 6, 6, 1, 1] then
  have hDecide := WOWII217FiniteSmallExceptions.connected_degreeSequence_666666611_closes
    (encodeUpper9 G_fin)
    (connectedUpper_of_connected_graphOfUpper9 _ (by
      rwa [graphOfUpper_encodeUpper9]
    ))
    (by
      rw [← hSeq]
      exact fixedDegreeSequenceUpper_encodeUpper9_of_degreeSequence G_fin
    )
  have traceEncoded := Iff.mp traceable_graphOfUpper_pathClosureParallelRounds_iff (traceable_graphOfUpper_of_completeUpperN (by exact hDecide))
  rwa [graphOfUpper_encodeUpper9] at traceEncoded
  apply hTrans; exact traceEncoded
else if hSeq : G_fin.degreeSequence = [6, 6, 6, 6, 6, 6, 5, 2, 1] then
  have hDecide := WOWII217FiniteSmallExceptions.connected_degreeSequence_666666521_closes
    (encodeUpper9 G_fin)
    (connectedUpper_of_connected_graphOfUpper9 _ (by
      rwa [graphOfUpper_encodeUpper9]
    ))
    (by
      rw [← hSeq]
      exact fixedDegreeSequenceUpper_encodeUpper9_of_degreeSequence G_fin
    )
  have traceEncoded := Iff.mp traceable_graphOfUpper_pathClosureParallelRounds_iff (traceable_graphOfUpper_of_completeUpperN (by exact hDecide))
  rwa [graphOfUpper_encodeUpper9] at traceEncoded
  apply hTrans; exact traceEncoded
else if hSeq : G_fin.degreeSequence = [6, 6, 6, 6, 6, 6, 4, 3, 1] then
  have hDecide := WOWII217FiniteSmallExceptions.connected_degreeSequence_666666431_closes
    (encodeUpper9 G_fin)
    (connectedUpper_of_connected_graphOfUpper9 _ (by
      rwa [graphOfUpper_encodeUpper9]
    ))
    (by
      rw [← hSeq]
      exact fixedDegreeSequenceUpper_encodeUpper9_of_degreeSequence G_fin
    )
  have traceEncoded := Iff.mp traceable_graphOfUpper_pathClosureParallelRounds_iff (traceable_graphOfUpper_of_completeUpperN (by exact hDecide))
  rwa [graphOfUpper_encodeUpper9] at traceEncoded
  apply hTrans; exact traceEncoded
else if hSeq : G_fin.degreeSequence = [6, 6, 6, 6, 6, 5, 5, 3, 1] then
  have hDecide := WOWII217FiniteSmallExceptions.connected_degreeSequence_666665531_closes
    (encodeUpper9 G_fin)
    (connectedUpper_of_connected_graphOfUpper9 _ (by
      rwa [graphOfUpper_encodeUpper9]
    ))
    (by
      rw [← hSeq]
      exact fixedDegreeSequenceUpper_encodeUpper9_of_degreeSequence G_fin
    )
  have traceEncoded := Iff.mp traceable_graphOfUpper_pathClosureParallelRounds_iff (traceable_graphOfUpper_of_completeUpperN (by exact hDecide))
  rwa [graphOfUpper_encodeUpper9] at traceEncoded
  apply hTrans; exact traceEncoded
else if hSeq : G_fin.degreeSequence = [6, 6, 5, 5, 5, 5, 3, 3, 2] then
  have hDecide := WOWII217FiniteSmallExceptions.connected_degreeSequence_665555332_closes
    (encodeUpper9 G_fin)
    (connectedUpper_of_connected_graphOfUpper9 _ (by
      rwa [graphOfUpper_encodeUpper9]
    ))
    (by
      rw [← hSeq]
      exact fixedDegreeSequenceUpper_encodeUpper9_of_degreeSequence G_fin
    )
  have traceEncoded := Iff.mp traceable_graphOfUpper_pathClosureParallelRounds_iff (traceable_graphOfUpper_of_completeUpperN (by exact hDecide))
  rwa [graphOfUpper_encodeUpper9] at traceEncoded
  apply hTrans; exact traceEncoded
else if hSeq : G_fin.degreeSequence = [6, 5, 5, 5, 5, 5, 3, 2, 2] then
  have hDecide := WOWII217FiniteSmallExceptions.connected_degreeSequence_655555322_closes
    (encodeUpper9 G_fin)
    (connectedUpper_of_connected_graphOfUpper9 _ (by
      rwa [graphOfUpper_encodeUpper9]
    ))
    (by
      rw [← hSeq]
      exact fixedDegreeSequenceUpper_encodeUpper9_of_degreeSequence G_fin
    )
  have traceEncoded := Iff.mp traceable_graphOfUpper_pathClosureParallelRounds_iff (traceable_graphOfUpper_of_completeUpperN (by exact hDecide))
  rwa [graphOfUpper_encodeUpper9] at traceEncoded
  apply hTrans; exact traceEncoded
else if hSeq : G_fin.degreeSequence = [6, 5, 5, 5, 5, 4, 3, 3, 2] then
  have hDecide := WOWII217FiniteSmallExceptions.connected_degreeSequence_655554332_closes
    (encodeUpper9 G_fin)
    (connectedUpper_of_connected_graphOfUpper9 _ (by
      rwa [graphOfUpper_encodeUpper9]
    ))
    (by
      rw [← hSeq]
      exact fixedDegreeSequenceUpper_encodeUpper9_of_degreeSequence G_fin
    )
  have traceEncoded := Iff.mp traceable_graphOfUpper_pathClosureParallelRounds_iff (traceable_graphOfUpper_of_completeUpperN (by exact hDecide))
  rwa [graphOfUpper_encodeUpper9] at traceEncoded
  apply hTrans; exact traceEncoded
else if hSeq : G_fin.degreeSequence = [6, 5, 5, 5, 5, 3, 3, 3, 3] then
  have hDecide := WOWII217FiniteSmallExceptions.connected_degreeSequence_655553333_closes
    (encodeUpper9 G_fin)
    (connectedUpper_of_connected_graphOfUpper9 _ (by
      rwa [graphOfUpper_encodeUpper9]
    ))
    (by
      rw [← hSeq]
      exact fixedDegreeSequenceUpper_encodeUpper9_of_degreeSequence G_fin
    )
  have traceEncoded := Iff.mp traceable_graphOfUpper_pathClosureParallelRounds_iff (traceable_graphOfUpper_of_completeUpperN (by exact hDecide))
  rwa [graphOfUpper_encodeUpper9] at traceEncoded
  apply hTrans; exact traceEncoded
else if hSeq : G_fin.degreeSequence = [5, 5, 5, 5, 5, 5, 3, 3, 2] then
  have hDecide := WOWII217FiniteSmallExceptions.connected_degreeSequence_555555332_closes
    (encodeUpper9 G_fin)
    (connectedUpper_of_connected_graphOfUpper9 _ (by
      rwa [graphOfUpper_encodeUpper9]
    ))
    (by
      rw [← hSeq]
      exact fixedDegreeSequenceUpper_encodeUpper9_of_degreeSequence G_fin
    )
  have traceEncoded := Iff.mp traceable_graphOfUpper_pathClosureParallelRounds_iff (traceable_graphOfUpper_of_completeUpperN (by exact hDecide))
  rwa [graphOfUpper_encodeUpper9] at traceEncoded
  apply hTrans; exact traceEncoded
else if hSeq : G_fin.degreeSequence = [5, 5, 5, 5, 5, 5, 2, 2, 2] then
  have hDecide := WOWII217FiniteSmallExceptions.connected_degreeSequence_555555222_closes
    (encodeUpper9 G_fin)
    (connectedUpper_of_connected_graphOfUpper9 _ (by
      rwa [graphOfUpper_encodeUpper9]
    ))
    (by
      rw [← hSeq]
      exact fixedDegreeSequenceUpper_encodeUpper9_of_degreeSequence G_fin
    )
  have traceEncoded := Iff.mp traceable_graphOfUpper_pathClosureParallelRounds_iff (traceable_graphOfUpper_of_completeUpperN (by exact hDecide))
  rwa [graphOfUpper_encodeUpper9] at traceEncoded
  apply hTrans; exact traceEncoded
else if hSeq : G_fin.degreeSequence = [5, 5, 5, 5, 5, 4, 3, 2, 2] then
  have hDecide := WOWII217FiniteSmallExceptions.connected_degreeSequence_555554322_closes
    (encodeUpper9 G_fin)
    (connectedUpper_of_connected_graphOfUpper9 _ (by
      rwa [graphOfUpper_encodeUpper9]
    ))
    (by
      rw [← hSeq]
      exact fixedDegreeSequenceUpper_encodeUpper9_of_degreeSequence G_fin
    )
  have traceEncoded := Iff.mp traceable_graphOfUpper_pathClosureParallelRounds_iff (traceable_graphOfUpper_of_completeUpperN (by exact hDecide))
  rwa [graphOfUpper_encodeUpper9] at traceEncoded
  apply hTrans; exact traceEncoded
else if hSeq : G_fin.degreeSequence = [5, 5, 5, 5, 5, 3, 3, 3, 2] then
  have hDecide := WOWII217FiniteSmallExceptions.connected_degreeSequence_555553332_closes
    (encodeUpper9 G_fin)
    (connectedUpper_of_connected_graphOfUpper9 _ (by
      rwa [graphOfUpper_encodeUpper9]
    ))
    (by
      rw [← hSeq]
      exact fixedDegreeSequenceUpper_encodeUpper9_of_degreeSequence G_fin
    )
  have traceEncoded := Iff.mp traceable_graphOfUpper_pathClosureParallelRounds_iff (traceable_graphOfUpper_of_completeUpperN (by exact hDecide))
  rwa [graphOfUpper_encodeUpper9] at traceEncoded
  apply hTrans; exact traceEncoded
else if hSeq : G_fin.degreeSequence = [5, 5, 5, 5, 4, 4, 3, 3, 2] then
  have hDecide := WOWII217FiniteSmallExceptions.connected_degreeSequence_555544332_closes
    (encodeUpper9 G_fin)
    (connectedUpper_of_connected_graphOfUpper9 _ (by
      rwa [graphOfUpper_encodeUpper9]
    ))
    (by
      rw [← hSeq]
      exact fixedDegreeSequenceUpper_encodeUpper9_of_degreeSequence G_fin
    )
  have traceEncoded := Iff.mp traceable_graphOfUpper_pathClosureParallelRounds_iff (traceable_graphOfUpper_of_completeUpperN (by exact hDecide))
  rwa [graphOfUpper_encodeUpper9] at traceEncoded
  apply hTrans; exact traceEncoded
else if hSeq : G_fin.degreeSequence = [5, 5, 5, 5, 4, 3, 3, 3, 3] then
  have hDecide := WOWII217FiniteSmallExceptions.connected_degreeSequence_555543333_closes
    (encodeUpper9 G_fin)
    (connectedUpper_of_connected_graphOfUpper9 _ (by
      rwa [graphOfUpper_encodeUpper9]
    ))
    (by
      rw [← hSeq]
      exact fixedDegreeSequenceUpper_encodeUpper9_of_degreeSequence G_fin
    )
  have traceEncoded := Iff.mp traceable_graphOfUpper_pathClosureParallelRounds_iff (traceable_graphOfUpper_of_completeUpperN (by exact hDecide))
  rwa [graphOfUpper_encodeUpper9] at traceEncoded
  apply hTrans; exact traceEncoded
else if hSeq : G_fin.degreeSequence = [4, 4, 4, 4, 4, 3, 3, 3, 3] then
  have hDecide := WOWII217FiniteSmallExceptions.connected_degreeSequence_444443333_closes
    (encodeUpper9 G_fin)
    (connectedUpper_of_connected_graphOfUpper9 _ (by
      rwa [graphOfUpper_encodeUpper9]
    ))
    (by
      rw [← hSeq]
      exact fixedDegreeSequenceUpper_encodeUpper9_of_degreeSequence G_fin
    )
  have traceEncoded := Iff.mp traceable_graphOfUpper_pathClosureParallelRounds_iff (traceable_graphOfUpper_of_completeUpperN (by exact hDecide))
  rwa [graphOfUpper_encodeUpper9] at traceEncoded
  apply hTrans; exact traceEncoded
else
  sorry

end WOWII217SmallNExceptions
