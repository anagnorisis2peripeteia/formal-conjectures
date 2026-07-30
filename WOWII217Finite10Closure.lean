import WOWII217Closure

namespace WOWII217Finite10Closure

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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
theorem connected_degreeSequence_6666444444_closes_or_dominatingEdge :
    ∀ g : BitVec 45,
      connectedUpper (n := 10) g = true →
      fixedDegreeSequenceUpper (n := 10) g
        [6, 6, 6, 6, 4, 4, 4, 4, 4, 4] = true →
      (completeUpper (n := 10) (pathClosureParallelRounds (n := 10) 4 g) ||
       hasDominatingEdge10 g) = true := by
  simp (config := { maxSteps := 1000000000 }) only
    [completeUpper, pathClosureParallelRounds, pathClosureParallelRound,
      pathClosureParallelMask, degreeUpperNat,
      hasDominatingEdge10, isAdj10,
      upperIndex,
      edgeCount, fixedDegreeSequenceUpper, matchesDegreesFromUpper,
      degreeBitsUpper, BoolFour.increment, BoolFour.same, BoolFour.ofNat,
      connectedUpper, reachableFromZeroUpper,
      adjUpper, setBit, bitMask, maskHas,
      List.range, List.range.loop, List.foldl, List.all, List.any,
      List.flatMap, List.flatten, List.map, List.append,
      List.length_cons, List.length_nil, beq_iff_eq, Bool.or_eq_true,
      cond_true, cond_false]
  bv_decide (maxSteps := 1000000000) (timeout := 600)

end WOWII217Finite10Closure
