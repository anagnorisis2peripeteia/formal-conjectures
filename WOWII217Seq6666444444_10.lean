/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import WOWII217Encoding10
import WOWII217Degree10
import WOWII217Connected10
import WOWII217Finite10Semantics
import WOWII217Finite10Seq6666444444

/-!
# Transport for 10-vertex sequence [6,6,6,6,4,4,4,4,4,4]

Connected graphs on 10 vertices with degree sequence [6,6,6,6,4,4,4,4,4,4]
and not matching K(4,6) are traceable via the Held-Karp certificate.
-/

namespace WOWII217Seq6666444444_10

open Classical SimpleGraph
open WOWII217BondyChvatal
open WOWII217FiniteBase
open WOWII217ClosureSemantics
open WOWII217Encoding10
open WOWII217Degree10
open WOWII217Connected10
open WOWII217Finite10Semantics
open WOWII217Finite10Seq6666444444

/-- Connected graphs on `Fin 10` with degree sequence [6, 6, 6, 6, 4, 4, 4, 4, 4, 4] and not K(4,6) are traceable. -/
theorem seq6666444444_10_traceable
    (G : SimpleGraph (Fin 10)) [DecidableRel G.Adj]
    (connected : G.Connected)
    (hSeq : List.ofFn (fun v : Fin 10 => G.degree v) = [6, 6, 6, 6, 4, 4, 4, 4, 4, 4])
    (hNe : (encodeUpper10 G == 1034850648000#45) = false) :
    Traceable G := by
  have degrees :
      fixedDegreeSequenceUpper (n := 10) (encodeUpper10 G)
        [6, 6, 6, 6, 4, 4, 4, 4, 4, 4] = true :=
    fixedDegreeSequenceUpper_encodeUpper10_of_degreeSequence G [6, 6, 6, 6, 4, 4, 4, 4, 4, 4] hSeq
  have encodedConnected :
      (graphOfUpper (n := 10) (encodeUpper10 G)).Connected := by
    rw [graphOfUpper_encodeUpper10]
    exact connected
  have connUpper :
      connectedUpper (n := 10) (encodeUpper10 G) = true :=
    connectedUpper_of_connected_graphOfUpper10 (encodeUpper10 G) encodedConnected
  
  have consistent : WOWII217Finite10Seq6666444444.hamiltonianDPConsistent10Split (encodeUpper10 G)
    (endpointBlock10 (encodeUpper10 G) 0) (endpointBlock10 (encodeUpper10 G) 1)
    (endpointBlock10 (encodeUpper10 G) 2) (endpointBlock10 (encodeUpper10 G) 3)
    (endpointBlock10 (encodeUpper10 G) 4) (endpointBlock10 (encodeUpper10 G) 5)
    (endpointBlock10 (encodeUpper10 G) 6) (endpointBlock10 (encodeUpper10 G) 7)
    (endpointBlock10 (encodeUpper10 G) 8) (endpointBlock10 (encodeUpper10 G) 9) = true :=
    endpointBlocks10_consistent (encodeUpper10 G)
  have certificate := seq6666444444_10_hasHamiltonianDPState (encodeUpper10 G)
    (endpointBlock10 (encodeUpper10 G) 0) (endpointBlock10 (encodeUpper10 G) 1)
    (endpointBlock10 (encodeUpper10 G) 2) (endpointBlock10 (encodeUpper10 G) 3)
    (endpointBlock10 (encodeUpper10 G) 4) (endpointBlock10 (encodeUpper10 G) 5)
    (endpointBlock10 (encodeUpper10 G) 6) (endpointBlock10 (encodeUpper10 G) 7)
    (endpointBlock10 (encodeUpper10 G) 8) (endpointBlock10 (encodeUpper10 G) 9)
  rw [connUpper, degrees, consistent] at certificate
  simp only [hNe, Bool.not_false, Bool.true_and] at certificate
  have full : WOWII217Finite10Seq6666444444.hamiltonianDPHasFullPath10Split
      (endpointBlock10 (encodeUpper10 G) 0) (endpointBlock10 (encodeUpper10 G) 1)
      (endpointBlock10 (encodeUpper10 G) 2) (endpointBlock10 (encodeUpper10 G) 3)
      (endpointBlock10 (encodeUpper10 G) 4) (endpointBlock10 (encodeUpper10 G) 5)
      (endpointBlock10 (encodeUpper10 G) 6) (endpointBlock10 (encodeUpper10 G) 7)
      (endpointBlock10 (encodeUpper10 G) 8) (endpointBlock10 (encodeUpper10 G) 9) = true := by
    by_contra notFull
    have fullFalse : WOWII217Finite10Seq6666444444.hamiltonianDPHasFullPath10Split
        (endpointBlock10 (encodeUpper10 G) 0) (endpointBlock10 (encodeUpper10 G) 1)
        (endpointBlock10 (encodeUpper10 G) 2) (endpointBlock10 (encodeUpper10 G) 3)
        (endpointBlock10 (encodeUpper10 G) 4) (endpointBlock10 (encodeUpper10 G) 5)
        (endpointBlock10 (encodeUpper10 G) 6) (endpointBlock10 (encodeUpper10 G) 7)
        (endpointBlock10 (encodeUpper10 G) 8) (endpointBlock10 (encodeUpper10 G) 9) = false :=
      Bool.eq_false_of_not_eq_true notFull
    simp [fullFalse] at certificate
  have full_reg : WOWII217Finite10Regular.hamiltonianDPHasFullPath10Split
      (endpointBlock10 (encodeUpper10 G) 0) (endpointBlock10 (encodeUpper10 G) 1)
      (endpointBlock10 (encodeUpper10 G) 2) (endpointBlock10 (encodeUpper10 G) 3)
      (endpointBlock10 (encodeUpper10 G) 4) (endpointBlock10 (encodeUpper10 G) 5)
      (endpointBlock10 (encodeUpper10 G) 6) (endpointBlock10 (encodeUpper10 G) 7)
      (endpointBlock10 (encodeUpper10 G) 8) (endpointBlock10 (encodeUpper10 G) 9) = true := full
  have certified := traceable_of_endpointBlocks10_full (encodeUpper10 G) full_reg
  rwa [graphOfUpper_encodeUpper10] at certified

/-- Transport the certificate to any vertex type of card 10. -/
theorem hamiltonian_of_order10_seq6666444444
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (_hcard : Fintype.card V = 10)
    (connected : G.Connected)
    (hFinTrans : ∃ e : Fin 10 ≃ V, 
        List.ofFn (fun v : Fin 10 => G.degree (e v)) = [6, 6, 6, 6, 4, 4, 4, 4, 4, 4])
    (hNe : ∀ e : Fin 10 ≃ V, encodeUpper10 (G.comap e.toEmbedding) ≠ 1034850648000#45) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  rcases hFinTrans with ⟨e, hSeq⟩
  let G' : SimpleGraph (Fin 10) := G.comap e.toEmbedding
  let iso : G' ≃g G := SimpleGraph.Iso.comap e G
  letI : DecidableRel G'.Adj := fun u v => by
    change Decidable (G.Adj (e u) (e v))
    infer_instance
  have connected' : G'.Connected := iso.connected_iff.mpr connected
  have hSeq' : List.ofFn (fun v : Fin 10 => G'.degree v) = [6, 6, 6, 6, 4, 4, 4, 4, 4, 4] := by
    have h_fun_eq : (fun v : Fin 10 => G'.degree v) = (fun v : Fin 10 => G.degree (e v)) := by
      ext v
      exact (iso.degree_eq v).symm
    rw [h_fun_eq]
    exact hSeq
  have hNe_bool : (encodeUpper10 G' == 1034850648000#45) = false := by
    have hNe' : encodeUpper10 G' ≠ 1034850648000#45 := hNe e
    cases h_eq : (encodeUpper10 G' == 1034850648000#45)
    · rfl
    · exact False.elim (hNe' (beq_iff_eq.mp h_eq))
  have hTrace' : Traceable G' := seq6666444444_10_traceable G' connected' hSeq' hNe_bool
  rcases hTrace' with ⟨a, b, p, hp⟩
  exact ⟨e a, e b, p.map iso.toHom, hp.map iso.toHom e.bijective⟩

end WOWII217Seq6666444444_10
