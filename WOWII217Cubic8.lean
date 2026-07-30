import WOWII217Encoding8
import WOWII217Degree8
import WOWII217Connected8
import WOWII217Finite8Semantics

/-!
End-to-end cubic order-8 residual certificate.

Connected 3-regular graphs on any vertex type of cardinality 8 are traceable
via the Held–Karp bit-vector certificate on a `Fin 8` labeling.
-/

namespace WOWII217Cubic8

open Classical SimpleGraph
open WOWII217BondyChvatal
open WOWII217FiniteBase
open WOWII217ClosureSemantics
open WOWII217Encoding8
open WOWII217Degree8
open WOWII217Connected8
open WOWII217Finite8Semantics

/-- Connected 3-regular graphs on `Fin 8` are traceable. -/
theorem threeRegular8_traceable
    (G : SimpleGraph (Fin 8)) [DecidableRel G.Adj]
    (connected : G.Connected)
    (hReg : ∀ v : Fin 8, G.degree v = 3) :
    Traceable G := by
  have degrees :
      fixedDegreeSequenceUpper (n := 8) (encodeUpper8 G)
        [3, 3, 3, 3, 3, 3, 3, 3] = true :=
    fixedDegreeSequenceUpper_encodeUpper8_of_threeRegular G hReg
  have encodedConnected :
      (graphOfUpper (n := 8) (encodeUpper8 G)).Connected := by
    rw [graphOfUpper_encodeUpper8]
    exact connected
  have connUpper :
      connectedUpper (n := 8) (encodeUpper8 G) = true :=
    connectedUpper_of_connected_graphOfUpper8 (encodeUpper8 G) encodedConnected
  have certified :=
    traceable_of_cubic8 (encodeUpper8 G) connUpper degrees
  rwa [graphOfUpper_encodeUpper8] at certified

/-- Transport the cubic-8 certificate to any vertex type of card 8. -/
theorem hamiltonian_of_order8_three_regular
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : Fintype.card V = 8)
    (connected : G.Connected)
    (hReg : ∀ v : V, G.degree v = 3) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  let e : Fin 8 ≃ V := (Fintype.equivFinOfCardEq hcard).symm
  let G' : SimpleGraph (Fin 8) := G.comap e.toEmbedding
  let iso : G' ≃g G := SimpleGraph.Iso.comap e G
  letI : DecidableRel G'.Adj := fun u v => by
    change Decidable (G.Adj (e u) (e v))
    infer_instance
  have connected' : G'.Connected := iso.connected_iff.mpr connected
  have hReg' : ∀ v : Fin 8, G'.degree v = 3 := by
    intro v
    have hdeq : G'.degree v = G.degree (e v) := (iso.degree_eq v).symm
    rw [hdeq, hReg]
  have hTrace' : Traceable G' := threeRegular8_traceable G' connected' hReg'
  rcases hTrace' with ⟨a, b, p, hp⟩
  exact ⟨e a, e b, p.map iso.toHom, hp.map iso.toHom e.bijective⟩

end WOWII217Cubic8
