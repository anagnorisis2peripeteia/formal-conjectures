import WOWII217Closure13Fast
import WOWII217Finite13

open WOWII217Closure13Fast WOWII217Finite13 WOWII217Closure WOWII217FiniteBase

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
theorem test_relational_closure_sym_fast :
    ∀ g g1 g2 g3 g4 : BitVec 78,
      (fun g =>
        (List.range 7).any fun u =>
          (List.range 6).any fun offset => adjUpper (n := 13) g u (offset + 7)) g = true →
      fixedDegreeSequenceUpper (n := 13) g
        [6, 6, 6, 6, 6, 6, 6, 5, 5, 5, 5, 5, 5] = true →
      canonicalPermutationBlocksPattern13 g 0 = true →
      (upperPairs 13).all (fun edge =>
        let u := edge.1; let v := edge.2;
        !(adjUpper (n := 13) g1 u v ^^
          (adjUpper (n := 13) g u v ||
            degreePairAtLeast12Upper13 g u v)) = true →
      (upperPairs 13).all (fun edge =>
        let u := edge.1; let v := edge.2;
        !(adjUpper (n := 13) g2 u v ^^
          (adjUpper (n := 13) g1 u v ||
            degreePairAtLeast12Upper13 g1 u v)) = true →
      (upperPairs 13).all (fun edge =>
        let u := edge.1; let v := edge.2;
        !(adjUpper (n := 13) g3 u v ^^
          (adjUpper (n := 13) g2 u v ||
            degreePairAtLeast12Upper13 g2 u v)) = true →
      (upperPairs 13).all (fun edge =>
        let u := edge.1; let v := edge.2;
        !(adjUpper (n := 13) g4 u v ^^
          (adjUpper (n := 13) g3 u v ||
            degreePairAtLeast12Upper13 g3 u v)) = true →
      completeUpper (n := 13) g4 = true := by
  intro g g1 g2 g3 g4 hHigh hDeg hCanon hRel0 hRel1 hRel2 hRel3
  simp (config := { maxSteps := 1000000000 }) only
    [hasHighLowEdge13, fixedDegreeSequenceUpper, matchesDegreesFromUpper,
      degreePairAtLeast12Upper13, degreePairBits13,
      BoolFive.increment, BoolFive.zero, upperPairs,
      edgeCount,
      connectedUpper, reachableFromZeroUpper,
      canonicalPermutationBlocksPattern13, canonicalPermutationBlock13,
      blockOrderSignature13, blockOrderedVertex13, bitListLexLe13,
      zeroDegreeBlocksPattern13,
      adjUpper, setBit, bitMask, maskHas,
      List.range, List.range.loop, List.foldl, List.all, List.any,
      List.flatMap, List.flatten, List.map, List.append,
      List.length_cons, List.length_nil, List.getD]
  decide
