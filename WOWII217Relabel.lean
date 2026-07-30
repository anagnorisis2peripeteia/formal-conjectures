import WOWII217Relabel14SortedCertificate
import WOWII217Canonical
import WOWII217Connected14
import WOWII217Degree14

/-!
Canonical relabelling for the certified 14-vertex six-regular exceptional class.

The finite certificate fixes vertex `0`, puts its six neighbours in positions
`1, ..., 6`, and sorts the two remaining blocks by explicit adjacency keys.
This file transports the Held–Karp residual certificate along that relabelling
using structural (non-SAT) proofs of the symmetry-breaking predicates.
-/

namespace WOWII217Relabel

open SimpleGraph
open WOWII217DP
open WOWII217Encoding
open WOWII217Semantics (graphOfUpper14)
open WOWII217Connected14
open WOWII217Degree14
open WOWII217Canonical

theorem canonicalEncoding14_finite_properties (g : BitVec 91)
    (sixRegular : fixedDegreeSequenceUpper (n := 14) g
      [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] = true) :
    (canonicalZeroNeighborhood14 (canonicalEncoding14 g) &&
      canonicalPartitionDegreesSorted14 (canonicalEncoding14 g)) = true := by
  rw [← canonicalEncodingFast14_eq]
  simp only [Bool.and_eq_true]
  exact ⟨canonicalEncodingFast14_zeroNeighborhood g sixRegular,
    canonicalEncodingFast14_partitionSorted g sixRegular⟩

theorem canonicalEncoding14_connected (g : BitVec 91)
    (connected : (graphOfUpper14 g).Connected) :
    connectedUpper (n := 14) (canonicalEncoding14 g) = true := by
  have canonicalConnected : (canonicalGraph14 g).Connected :=
    (canonicalIso14 g).connected_iff.mpr connected
  have hgraph : graphOfUpper14 (canonicalEncoding14 g) = canonicalGraph14 g :=
    graphOfUpper14_canonicalEncoding14 g
  have connected' : (graphOfUpper14DP (canonicalEncoding14 g)).Connected := by
    rw [graphOfUpper14DP_eq, hgraph]
    exact canonicalConnected
  exact connectedUpper_of_connected_graphOfUpper14DP _ connected'

set_option maxHeartbeats 800000 in
theorem sixRegular_graphOfUpper14_of_fixed (g : BitVec 91)
    (sixRegular : fixedDegreeSequenceUpper (n := 14) g
      [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] = true) :
    ∀ v : Fin 14, (graphOfUpper14 g).degree v = 6 := by
  intro v
  -- Extract the DP same-bits hypothesis for this vertex, then transport to FiniteBase.
  have sameDP : (degreeBitsUpper (n := 14) g v).same (BoolFour.ofNat 6) = true := by
    fin_cases v <;>
      norm_num [fixedDegreeSequenceUpper, matchesDegreesFromUpper] at sixRegular ⊢ <;>
      aesop
  have same : (WOWII217FiniteBase.degreeBitsUpper (n := 14) g v).same
      (WOWII217FiniteBase.BoolFour.ofNat 6) = true := by
    rwa [← degreeBitsUpper_dp_eq_finiteBase]
  have upperDegree := degreeUpperNat_eq_six_of_same g v same
  rw [degree_graphOfUpper_eq14_current, upperDegree]

theorem sixRegular14Encoding_hasHamiltonianWalk (g : BitVec 91)
    (connected : (graphOfUpper14 g).Connected)
    (sixRegular : fixedDegreeSequenceUpper (n := 14) g
      [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] = true) :
    ∃ a b : Fin 14, ∃ p : (graphOfUpper14 g).Walk a b, p.IsHamiltonian := by
  have properties := canonicalEncoding14_finite_properties g sixRegular
  rcases (Bool.and_eq_true _ _).mp properties with ⟨canonicalZero, canonicalSorted⟩
  letI : DecidableRel (canonicalGraph14 g).Adj := fun u v => by
    change Decidable
      (WOWII217Semantics.adjUpper (n := 14) g
        (canonicalEquiv14 g u) (canonicalEquiv14 g v) = true)
    infer_instance
  have originalSix := sixRegular_graphOfUpper14_of_fixed g sixRegular
  have canonicalGraphSix :
      ∀ v : Fin 14, (canonicalGraph14 g).degree v = 6 := by
    intro v
    calc
      (canonicalGraph14 g).degree v =
          (graphOfUpper14 g).degree (canonicalEquiv14 g v) :=
        (canonicalIso14 g).degree_eq v |>.symm
      _ = 6 := originalSix (canonicalEquiv14 g v)
  have canonicalSixRegular :
      fixedDegreeSequenceUpper (n := 14) (canonicalEncoding14 g)
        [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] = true := by
    simpa only [canonicalEncoding14] using
      fixedDegreeSequenceUpper_encodeUpper14_of_sixRegular
        (canonicalGraph14 g) canonicalGraphSix
  have canonicalConnected := canonicalEncoding14_connected g connected
  have certified :=
    canonicalSixRegular14Graph_hasHamiltonianWalk
      (canonicalGraph14 g) canonicalConnected canonicalSixRegular
      (by simpa [canonicalEncoding14] using canonicalZero)
      (by simpa [canonicalEncoding14] using canonicalSorted)
  rcases certified with ⟨a, b, p, hp⟩
  refine ⟨canonicalEquiv14 g a, canonicalEquiv14 g b,
    p.map (canonicalIso14 g).toHom, ?_⟩
  exact hp.map (canonicalIso14 g).toHom (canonicalEquiv14 g).bijective

theorem sixRegular14Graph_hasHamiltonianWalk
    (G : SimpleGraph (Fin 14)) [DecidableRel G.Adj]
    (connected : G.Connected)
    (sixRegular : ∀ v : Fin 14, G.degree v = 6) :
    ∃ a b : Fin 14, ∃ p : G.Walk a b, p.IsHamiltonian := by
  have encodedConnected :
      (graphOfUpper14 (encodeUpper14 G)).Connected := by
    rw [graphOfUpper14_encodeUpper14]
    exact connected
  have encodedSix :
      fixedDegreeSequenceUpper (n := 14) (encodeUpper14 G)
        [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] = true :=
    fixedDegreeSequenceUpper_encodeUpper14_of_sixRegular G sixRegular
  have certified := sixRegular14Encoding_hasHamiltonianWalk
    (encodeUpper14 G) encodedConnected encodedSix
  rw [graphOfUpper14_encodeUpper14 G] at certified
  exact certified

end WOWII217Relabel
