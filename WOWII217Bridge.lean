import WOWII217DP

/-!
End-to-end bridge from the finite SAT certificate to an actual Hamiltonian walk.
-/

namespace WOWII217Bridge

open WOWII217DP

theorem canonicalSixRegular14_hasHamiltonianWalk (g : BitVec 91)
    (connected : connectedUpper (n := 14) g = true)
    (sixRegular : fixedDegreeSequenceUpper (n := 14) g
      [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] = true)
    (zeroNeighborhood : canonicalZeroNeighborhood14 g = true)
    (partitionSorted : canonicalPartitionDegreesSorted14 g = true) :
    ∃ a b : Fin 14,
      ∃ p : (WOWII217Semantics.graphOfUpper14 g).Walk a b, p.IsHamiltonian := by
  let d0 := WOWII217Semantics.endpointBlock14 g 0
  let d1 := WOWII217Semantics.endpointBlock14 g 1
  let d2 := WOWII217Semantics.endpointBlock14 g 2
  let d3 := WOWII217Semantics.endpointBlock14 g 3
  let d4 := WOWII217Semantics.endpointBlock14 g 4
  let d5 := WOWII217Semantics.endpointBlock14 g 5
  let d6 := WOWII217Semantics.endpointBlock14 g 6
  let d7 := WOWII217Semantics.endpointBlock14 g 7
  let d8 := WOWII217Semantics.endpointBlock14 g 8
  let d9 := WOWII217Semantics.endpointBlock14 g 9
  let d10 := WOWII217Semantics.endpointBlock14 g 10
  let d11 := WOWII217Semantics.endpointBlock14 g 11
  let d12 := WOWII217Semantics.endpointBlock14 g 12
  let d13 := WOWII217Semantics.endpointBlock14 g 13
  have semanticConsistent :
      WOWII217Semantics.hamiltonianDPConsistent14Split g
        d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 = true := by
    simpa only [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12,
      d13] using WOWII217Semantics.endpointBlocks_consistent g
  have encodedConsistent :
      hamiltonianDPConsistent14Split g
        d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 = true := by
    change WOWII217Semantics.hamiltonianDPConsistent14Split g
      d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 = true
    exact semanticConsistent
  have certificate := canonicalDegreeSequenceSixRegular14_hasHamiltonianDPState g
    d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13
  have encodedFull :
      hamiltonianDPHasFullPath14Split
        d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 = true := by
    apply Bool.eq_true_of_not_eq_false
    intro noFull
    have impossibleState :
        (connectedUpper (n := 14) g &&
          fixedDegreeSequenceUpper (n := 14) g
            [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] &&
          canonicalZeroNeighborhood14 g &&
          canonicalPartitionDegreesSorted14 g &&
          hamiltonianDPConsistent14Split g
            d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 &&
          !hamiltonianDPHasFullPath14Split
            d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13) = true := by
      simp [connected, sixRegular, zeroNeighborhood, partitionSorted,
        encodedConsistent, noFull]
    rw [impossibleState] at certificate
    exact Bool.noConfusion certificate
  have semanticFull :
      WOWII217Semantics.hamiltonianDPHasFullPath14Split
        d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 = true := by
    change hamiltonianDPHasFullPath14Split
      d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 = true
    exact encodedFull
  exact WOWII217Semantics.existsHamiltonianWalkOfDP14 g
    d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13
    semanticConsistent semanticFull

end WOWII217Bridge
