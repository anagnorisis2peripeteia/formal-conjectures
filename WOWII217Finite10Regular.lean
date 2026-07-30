import WOWII217FiniteBase

/-!
Held–Karp DP certificate for connected 4-regular graphs on 10 vertices.

Under residue = 2 and the stuck threshold `2 · maxDegree < n - 1`, the only
connected residual class on 10 vertices is 4-regular.  This module proves that
no consistent Held–Karp table for a connected 4-regular upper-triangular
encoding can omit a full-set Hamiltonian-path state.
-/

namespace WOWII217Finite10Regular

open WOWII217FiniteBase

def dpAt10
    (d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 : BitVec 1024) :
    Nat → BitVec 1024
  | 0 => d0
  | 1 => d1
  | 2 => d2
  | 3 => d3
  | 4 => d4
  | 5 => d5
  | 6 => d6
  | 7 => d7
  | 8 => d8
  | _ => d9

def hamiltonianDPConsistent10Split (g : BitVec 45)
    (d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 : BitVec 1024) : Bool :=
  (List.range 10).all fun v =>
    let extended := (List.range 10).foldl (fun states u =>
      states ||| (bitMask (w := 1024) (adjUpper (n := 10) g u v) &&&
        ((dpAt10 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 u &&&
          absentMask 10 v) <<< (2 ^ v)))) 0#1024
    dpAt10 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 v ==
      (BitVec.twoPow 1024 (2 ^ v) ||| extended)

def hamiltonianDPHasFullPath10Split
    (d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 : BitVec 1024) : Bool :=
  d0.getLsbD 1023 || d1.getLsbD 1023 || d2.getLsbD 1023 ||
  d3.getLsbD 1023 || d4.getLsbD 1023 || d5.getLsbD 1023 ||
  d6.getLsbD 1023 || d7.getLsbD 1023 || d8.getLsbD 1023 ||
  d9.getLsbD 1023

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
/-- Connected 4-regular order-10 encodings always admit a full Held–Karp path
state. -/
theorem fourRegular10_hasHamiltonianDPState :
    ∀ (g : BitVec 45)
      (d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 : BitVec 1024),
      (connectedUpper (n := 10) g &&
        fixedDegreeSequenceUpper (n := 10) g
          [4, 4, 4, 4, 4, 4, 4, 4, 4, 4] &&
        hamiltonianDPConsistent10Split g
          d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 &&
        !hamiltonianDPHasFullPath10Split
          d0 d1 d2 d3 d4 d5 d6 d7 d8 d9) = false := by
  simp (config := { maxSteps := 1000000000 }) only
    [edgeCount, fixedDegreeSequenceUpper, matchesDegreesFromUpper,
      degreeBitsUpper, BoolFour.increment, BoolFour.same, BoolFour.ofNat,
      connectedUpper, reachableFromZeroUpper,
      hamiltonianDPConsistent10Split, hamiltonianDPHasFullPath10Split, dpAt10,
      absentMask, maskHas, adjUpper, setBit, bitMask,
      List.range, List.range.loop, List.foldl, List.all, List.any]
  bv_decide (maxSteps := 1000000000) (timeout := 7200)

end WOWII217Finite10Regular
