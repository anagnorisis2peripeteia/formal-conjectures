import WOWII217FiniteBase
import WOWII217Closure

namespace WOWII217Finite10ExceptionDominating

open WOWII217FiniteBase WOWII217Closure

def isAdj10 (g : BitVec 45) (u v : Nat) : Bool :=
  bif decide (u < v) then adjUpper (n := 10) g u v
  else bif decide (v < u) then adjUpper (n := 10) g v u
  else false

def hasDominatingEdge10 (g : BitVec 45) : Bool :=
  (List.range 10).any fun u =>
    (List.range 10).any fun v =>
      (decide (u < v) && isAdj10 g u v) &&
        (List.range 10).all fun w =>
          w == u || w == v || isAdj10 g u w || isAdj10 g v w

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
      states ||| (bitMask (w := 1024) (isAdj10 g u v) &&&
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
theorem degreeSequence_6666444444_hasHamiltonianDPState :
    ∀ (g : BitVec 45)
      (d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 : BitVec 1024),
      (connectedUpper (n := 10) g &&
        fixedDegreeSequenceUpper (n := 10) g
          [6, 6, 6, 6, 4, 4, 4, 4, 4, 4] &&
        !hasDominatingEdge10 g &&
        hamiltonianDPConsistent10Split g
          d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 &&
        !hamiltonianDPHasFullPath10Split
          d0 d1 d2 d3 d4 d5 d6 d7 d8 d9) = false := by
  simp (config := { maxSteps := 1000000000 }) only
    [hasDominatingEdge10, isAdj10,
      edgeCount, fixedDegreeSequenceUpper, matchesDegreesFromUpper,
      degreeBitsUpper, BoolFour.increment, BoolFour.same, BoolFour.ofNat,
      connectedUpper, reachableFromZeroUpper,
      hamiltonianDPConsistent10Split, hamiltonianDPHasFullPath10Split, dpAt10,
      absentMask, maskHas, adjUpper, setBit, bitMask,
      List.range, List.range.loop, List.foldl, List.all, List.any, beq_iff_eq,
      cond_true, cond_false]
  bv_decide (maxSteps := 1000000000) (timeout := 600)

end WOWII217Finite10ExceptionDominating
