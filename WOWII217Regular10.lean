import WOWII217Encoding10
import WOWII217Degree10
import WOWII217Connected10
import WOWII217Finite10Semantics

/-!
End-to-end cubic order-8 residual certificate.

Connected 4-regular graphs on any vertex type of cardinality 10 are traceable
via the Held–Karp bit-vector certificate on a `Fin 10` labeling.
-/

namespace WOWII217Regular10

open Classical SimpleGraph
open WOWII217BondyChvatal
open WOWII217FiniteBase
open WOWII217ClosureSemantics
open WOWII217Encoding10
open WOWII217Degree10
open WOWII217Connected10
open WOWII217Finite10Semantics

/-- Connected 4-regular graphs on `Fin 10` are traceable. -/
theorem fourRegular10_traceable
    (G : SimpleGraph (Fin 10)) [DecidableRel G.Adj]
    (connected : G.Connected)
    (hReg : ∀ v : Fin 10, G.degree v = 4) :
    Traceable G := by
  have degrees :
      fixedDegreeSequenceUpper (n := 10) (encodeUpper10 G)
        [4, 4, 4, 4, 4, 4, 4, 4, 4, 4] = true :=
    fixedDegreeSequenceUpper_encodeUpper10_of_fourRegular G hReg
  have encodedConnected :
      (graphOfUpper (n := 10) (encodeUpper10 G)).Connected := by
    rw [graphOfUpper_encodeUpper10]
    exact connected
  have connUpper :
      connectedUpper (n := 10) (encodeUpper10 G) = true :=
    connectedUpper_of_connected_graphOfUpper10 (encodeUpper10 G) encodedConnected
  have certified :=
    traceable_of_fourRegular10 (encodeUpper10 G) connUpper degrees
  rwa [graphOfUpper_encodeUpper10] at certified

/-- Transport the 4-reg-10 certificate to any vertex type of card 10. -/
theorem hamiltonian_of_order10_four_regular
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : Fintype.card V = 10)
    (connected : G.Connected)
    (hReg : ∀ v : V, G.degree v = 4) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  let e : Fin 10 ≃ V := (Fintype.equivFinOfCardEq hcard).symm
  let G' : SimpleGraph (Fin 10) := G.comap e.toEmbedding
  let iso : G' ≃g G := SimpleGraph.Iso.comap e G
  letI : DecidableRel G'.Adj := fun u v => by
    change Decidable (G.Adj (e u) (e v))
    infer_instance
  have connected' : G'.Connected := iso.connected_iff.mpr connected
  have hReg' : ∀ v : Fin 10, G'.degree v = 4 := by
    intro v
    have hdeq : G'.degree v = G.degree (e v) := (iso.degree_eq v).symm
    rw [hdeq, hReg]
  have hTrace' : Traceable G' := fourRegular10_traceable G' connected' hReg'
  rcases hTrace' with ⟨a, b, p, hp⟩
  exact ⟨e a, e b, p.map iso.toHom, hp.map iso.toHom e.bijective⟩

end WOWII217Regular10
