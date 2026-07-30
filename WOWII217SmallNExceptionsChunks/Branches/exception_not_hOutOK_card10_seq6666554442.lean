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
import WOWII217Bridge.SmallNPattern
import WOWII217Bridge.Certified

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

open Classical in
theorem exception_not_hOutOK_card10_seq6666554442
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (connected : G.Connected)
    (hCard12 : Fintype.card V ≤ 12)
    (hResidue : residue G = 2)
    (t : ℕ)
    (S : Finset V) (hS : ∀ v, v ∈ S ↔ t ≤ G.degree v)
    (hBig : Fintype.card V - 1 ≤ 2 * (card S - 1) ∧ 1 ≤ card S)
    (hNotOutOK : ¬ (∀ v : V, ¬ t ≤ G.degree v →
            Fintype.card V - 1 - (card S - 1) ≤ G.degree v))
    (hCard : Fintype.card V = 10)
    (hFinTrans : ∃ e : Fin 10 ≃ V, List.ofFn (fun v : Fin 10 => G.degree (e v)) = [6, 6, 6, 6, 5, 5, 4, 4, 4, 2]) :
  ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian
  := by

  exact WOWII217Bridge.traceable_of_card_eq G [6, 6, 6, 6, 5, 5, 4, 4, 4, 2]
    (fun H _ hconn hds =>
      WOWII217Bridge.certified_10 _ H connected_degreeSequence_6666554442_closes hconn hds)
    connected
    hFinTrans
end WOWII217SmallNExceptions
