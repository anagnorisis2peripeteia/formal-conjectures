import WOWII217Finite12Semantics
import WOWII217Connected12
import WOWII217Degree12
import WOWII217Relabel12SortedCertificate

/-!
Canonical relabelling for the certified connected 5-regular order-12 class.

The relabelling fixes vertex `0`, puts its five neighbours in positions
`1, ..., 5`, and sorts each side of the resulting partition by its number of
edges to the other side.  The structural certificates imported above prove
that this relabelling satisfies the exact symmetry-breaking predicates used by
the finite Hamiltonian-path certificate.
-/

namespace WOWII217Relabel12

open SimpleGraph
open WOWII217FiniteBase WOWII217Closure WOWII217Finite12Regular
open WOWII217Finite12Semantics WOWII217ClosureSemantics
open WOWII217Encoding12 WOWII217BondyChvatal
open WOWII217Connected12
open WOWII217Degree12

theorem degreeZeroFive_of_fixed12 (g : BitVec 66)
    (fiveRegular : fixedDegreeSequenceUpper (n := 12) g
      [5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5] = true) :
    (degreeBitsUpper (n := 12) g 0).same (BoolFour.ofNat 5) = true := by
  norm_num [fixedDegreeSequenceUpper, matchesDegreesFromUpper] at fiveRegular ⊢
  exact fiveRegular.1

theorem canonicalEncoding12_finite_properties (g : BitVec 66)
    (fiveRegular : fixedDegreeSequenceUpper (n := 12) g
      [5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5] = true) :
    (canonicalZeroNeighborhood12 (canonicalEncoding12 g) &&
      canonicalPartitionDegreesSorted12 (canonicalEncoding12 g)) = true := by
  have degreeZero := degreeZeroFive_of_fixed12 g fiveRegular
  rw [← canonicalEncodingFast12_eq]
  simp only [Bool.and_eq_true]
  exact ⟨canonicalEncodingFast12_zeroNeighborhood g degreeZero,
    canonicalEncodingFast12_partitionSorted g degreeZero⟩

theorem canonicalEncoding12_connected (g : BitVec 66)
    (connected : (graphOfUpper (n := 12) g).Connected) :
    connectedUpper (n := 12) (canonicalEncoding12 g) = true := by
  have canonicalConnected : (canonicalGraph12 g).Connected :=
    (canonicalIso12 g).connected_iff.mpr connected
  apply connectedUpper_of_connected_graphOfUpper12
  rw [graphOfUpper_canonicalEncoding12]
  exact canonicalConnected

theorem fiveRegular12Encoding_traceable (g : BitVec 66)
    (connected : (graphOfUpper (n := 12) g).Connected)
    (fiveRegular : fixedDegreeSequenceUpper (n := 12) g
      [5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5] = true) :
    Traceable (graphOfUpper (n := 12) g) := by
  have canonicalProperties := canonicalEncoding12_finite_properties g fiveRegular
  have properties :
      canonicalZeroNeighborhood12 (canonicalEncoding12 g) = true ∧
      canonicalPartitionDegreesSorted12 (canonicalEncoding12 g) = true := by
    simpa only [Bool.and_eq_true] using canonicalProperties
  rcases properties with ⟨canonicalZero, canonicalSorted⟩
  letI : DecidableRel (canonicalGraph12 g).Adj := fun u v => by
    change Decidable
      (adjUpper (n := 12) g
        (canonicalEquiv12 g u) (canonicalEquiv12 g v) = true)
    infer_instance
  have originalFiveRegular := fiveRegular_graphOfUpper_of_fixed g fiveRegular
  have canonicalGraphFiveRegular :
      ∀ v : Fin 12, (canonicalGraph12 g).degree v = 5 := by
    intro v
    calc
      (canonicalGraph12 g).degree v =
          (graphOfUpper (n := 12) g).degree (canonicalEquiv12 g v) :=
        (canonicalIso12 g).degree_eq v |>.symm
      _ = 5 := originalFiveRegular (canonicalEquiv12 g v)
  have canonicalFiveRegular :
      fixedDegreeSequenceUpper (n := 12) (canonicalEncoding12 g)
        [5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5] = true := by
    simpa only [canonicalEncoding12] using
      fixedDegreeSequenceUpper_encodeUpper12_of_fiveRegular
        (canonicalGraph12 g) canonicalGraphFiveRegular
  have canonicalConnected := canonicalEncoding12_connected g connected
  have certified := traceable_of_canonicalFiveRegular12
    (canonicalEncoding12 g) canonicalConnected canonicalFiveRegular
    canonicalZero canonicalSorted
  rw [graphOfUpper_canonicalEncoding12] at certified
  rcases certified with ⟨a, b, p, hp⟩
  refine ⟨canonicalEquiv12 g a, canonicalEquiv12 g b,
    p.map (canonicalIso12 g).toHom, ?_⟩
  exact hp.map (canonicalIso12 g).toHom (canonicalEquiv12 g).bijective

theorem fiveRegular12Graph_traceable
    (G : SimpleGraph (Fin 12)) [DecidableRel G.Adj]
    (connected : G.Connected)
    (fiveRegular : fixedDegreeSequenceUpper (n := 12) (encodeUpper12 G)
      [5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5] = true) :
    Traceable G := by
  have encodedConnected :
      (graphOfUpper (n := 12) (encodeUpper12 G)).Connected := by
    rw [graphOfUpper_encodeUpper12]
    exact connected
  have certified := fiveRegular12Encoding_traceable
    (encodeUpper12 G) encodedConnected fiveRegular
  rw [graphOfUpper_encodeUpper12 G] at certified
  exact certified

end WOWII217Relabel12
