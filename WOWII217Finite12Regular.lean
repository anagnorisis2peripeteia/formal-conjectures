import WOWII217FiniteBase

/-!
Trusted Held--Karp certificate for the one order-12 class that is not completed
by path closure: connected 5-regular graphs.
-/

namespace WOWII217Finite12Regular

open WOWII217FiniteBase

def dpAt12
    (d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 : BitVec 4096) :
    Nat → BitVec 4096
  | 0 => d0
  | 1 => d1
  | 2 => d2
  | 3 => d3
  | 4 => d4
  | 5 => d5
  | 6 => d6
  | 7 => d7
  | 8 => d8
  | 9 => d9
  | 10 => d10
  | _ => d11

def hamiltonianDPConsistent12Split (g : BitVec 66)
    (d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 : BitVec 4096) : Bool :=
  (List.range 12).all fun v =>
    let extended := (List.range 12).foldl (fun states u =>
      states ||| (bitMask (w := 4096) (adjUpper (n := 12) g u v) &&&
        ((dpAt12 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 u &&&
          absentMask 12 v) <<< (2 ^ v)))) 0#4096
    dpAt12 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 v ==
      (BitVec.twoPow 4096 (2 ^ v) ||| extended)

def hamiltonianDPHasFullPath12Split
    (d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 : BitVec 4096) : Bool :=
  d0.getLsbD 4095 || d1.getLsbD 4095 || d2.getLsbD 4095 ||
  d3.getLsbD 4095 || d4.getLsbD 4095 || d5.getLsbD 4095 ||
  d6.getLsbD 4095 || d7.getLsbD 4095 || d8.getLsbD 4095 ||
  d9.getLsbD 4095 || d10.getLsbD 4095 || d11.getLsbD 4095

def canonicalZeroNeighborhood12 (g : BitVec 66) : Bool :=
  (List.range 5).all (fun offset => adjUpper (n := 12) g 0 (offset + 1)) &&
  (List.range 6).all (fun offset => !adjUpper (n := 12) g 0 (offset + 6))

def degreeCountRange12 (g : BitVec 66) (u start count : Nat) : Nat :=
  (List.range count).foldl (fun degree offset =>
    degree + if adjUpper (n := 12) g u (start + offset) then 1 else 0) 0

def canonicalPartitionDegreesSorted12 (g : BitVec 66) : Bool :=
  (List.range 4).all (fun offset =>
    decide (degreeCountRange12 g (offset + 1) 6 6 ≤
      degreeCountRange12 g (offset + 2) 6 6)) &&
  (List.range 5).all (fun offset =>
    decide (degreeCountRange12 g (offset + 6) 1 5 ≤
      degreeCountRange12 g (offset + 7) 1 5))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
theorem canonicalFiveRegular12_hasHamiltonianDPState :
    ∀ (g : BitVec 66)
      (d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 : BitVec 4096),
      (connectedUpper (n := 12) g &&
        fixedDegreeSequenceUpper (n := 12) g
          [5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5] &&
        canonicalZeroNeighborhood12 g &&
        canonicalPartitionDegreesSorted12 g &&
        hamiltonianDPConsistent12Split g
          d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 &&
        !hamiltonianDPHasFullPath12Split
          d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11) = false := by
  simp (config := { maxSteps := 1000000000 }) only
    [edgeCount, fixedDegreeSequenceUpper, matchesDegreesFromUpper,
      degreeBitsUpper, BoolFour.increment, BoolFour.same, BoolFour.ofNat,
      connectedUpper, reachableFromZeroUpper,
      canonicalZeroNeighborhood12, canonicalPartitionDegreesSorted12,
      degreeCountRange12,
      hamiltonianDPConsistent12Split, hamiltonianDPHasFullPath12Split, dpAt12,
      absentMask, maskHas, adjUpper, setBit, bitMask,
      List.range, List.range.loop, List.foldl, List.all, List.any]
  bv_decide (maxSteps := 1000000000) (timeout := 1800)
    (embeddedConstraintSubst := false)

end WOWII217Finite12Regular
