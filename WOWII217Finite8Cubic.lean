import WOWII217FiniteBase

/-!
Held–Karp DP certificate for connected 3-regular graphs on 8 vertices.

Under residue = 2 and the stuck threshold `2 · maxDegree < n - 1`, the only
connected residual class on 8 vertices is cubic.  This module proves that no
consistent Held–Karp table for a connected cubic upper-triangular encoding can
omit a full-set Hamiltonian-path state.
-/

namespace WOWII217Finite8Cubic

open WOWII217FiniteBase

/-- Held–Karp block for endpoint `v`: bit `mask` means a path through exactly
the vertices of `mask` ending at `v`.  Width `2^8 = 256`. -/
def dpAt8
    (d0 d1 d2 d3 d4 d5 d6 d7 : BitVec 256) :
    Nat → BitVec 256
  | 0 => d0
  | 1 => d1
  | 2 => d2
  | 3 => d3
  | 4 => d4
  | 5 => d5
  | 6 => d6
  | _ => d7

def hamiltonianDPConsistent8Split (g : BitVec 28)
    (d0 d1 d2 d3 d4 d5 d6 d7 : BitVec 256) : Bool :=
  (List.range 8).all fun v =>
    let extended := (List.range 8).foldl (fun states u =>
      states ||| (bitMask (w := 256) (adjUpper (n := 8) g u v) &&&
        ((dpAt8 d0 d1 d2 d3 d4 d5 d6 d7 u &&&
          absentMask 8 v) <<< (2 ^ v)))) 0#256
    dpAt8 d0 d1 d2 d3 d4 d5 d6 d7 v ==
      (BitVec.twoPow 256 (2 ^ v) ||| extended)

def hamiltonianDPHasFullPath8Split
    (d0 d1 d2 d3 d4 d5 d6 d7 : BitVec 256) : Bool :=
  d0.getLsbD 255 || d1.getLsbD 255 || d2.getLsbD 255 ||
  d3.getLsbD 255 || d4.getLsbD 255 || d5.getLsbD 255 ||
  d6.getLsbD 255 || d7.getLsbD 255

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
/-- Connected 3-regular order-8 encodings always admit a full Held–Karp path
state: there is no consistent DP table that is full-path-free. -/
theorem cubic8_hasHamiltonianDPState :
    ∀ (g : BitVec 28)
      (d0 d1 d2 d3 d4 d5 d6 d7 : BitVec 256),
      (connectedUpper (n := 8) g &&
        fixedDegreeSequenceUpper (n := 8) g
          [3, 3, 3, 3, 3, 3, 3, 3] &&
        hamiltonianDPConsistent8Split g
          d0 d1 d2 d3 d4 d5 d6 d7 &&
        !hamiltonianDPHasFullPath8Split
          d0 d1 d2 d3 d4 d5 d6 d7) = false := by
  simp (config := { maxSteps := 1000000000 }) only
    [edgeCount, fixedDegreeSequenceUpper, matchesDegreesFromUpper,
      degreeBitsUpper, BoolFour.increment, BoolFour.same, BoolFour.ofNat,
      connectedUpper, reachableFromZeroUpper,
      hamiltonianDPConsistent8Split, hamiltonianDPHasFullPath8Split, dpAt8,
      absentMask, maskHas, adjUpper, setBit, bitMask,
      List.range, List.range.loop, List.foldl, List.all, List.any]
  bv_decide (maxSteps := 1000000000) (timeout := 3600)

end WOWII217Finite8Cubic
