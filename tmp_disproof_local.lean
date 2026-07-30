import WOWII217FiniteBase
import WOWII217Closure
import WOWII217Closure13Fast
import WOWII217Finite13

open WOWII217FiniteBase WOWII217Closure WOWII217Closure13Fast

namespace Scratch

def degreeTableAt13 (degrees : BitVec 52) (v : Nat) : BoolFour :=
  { b0 := degrees.getLsbD (4 * v)
    , b1 := degrees.getLsbD (4 * v + 1)
    , b2 := degrees.getLsbD (4 * v + 2)
    , b3 := degrees.getLsbD (4 * v + 3) }

def degreeTableConsistent13 (g : BitVec 78) (degrees : BitVec 52) : Bool :=
  (List.range 13).all fun v =>
    (degreeBitsUpper (n := 13) g v).same (degreeTableAt13 degrees v)

def majority (a b c : Bool) : Bool :=
  (a && b) || (a && c) || (b && c)

def boolFourSumAtLeast12 (x y : BoolFour) : Bool :=
  let c1 := x.b0 && y.b0
  let c2 := majority x.b1 y.b1 c1
  let s2 := x.b2 ^^ y.b2 ^^ c2
  let c3 := majority x.b2 y.b2 c2
  let s3 := x.b3 ^^ y.b3 ^^ c3
  let c4 := majority x.b3 y.b3 c3
  c4 || (s3 && s2)

def pathClosureParallelRel13 (g next : BitVec 78) (degrees : BitVec 52) : Bool :=
  (upperPairs 13).all fun edge =>
    let u := edge.1
    let v := edge.2
    !(adjUpper (n := 13) next u v ^^
      (adjUpper (n := 13) g u v ||
        boolFourSumAtLeast12 (degreeTableAt13 degrees u)
          (degreeTableAt13 degrees v)))

def hasHighLowEdge13 (g : BitVec 78) : Bool :=
  (List.range 7).any fun u =>
    (List.range 6).any fun offset => adjUpper (n := 13) g u (offset + 7)

/-- Two-clique base with a degree-preserving 2-cross-edges / 2-removed-edges perturbation. -/
def gCounter : BitVec 78 := by
  let h : BitVec 78 := 0#78
  let h' := (List.range 13).foldl (fun acc u =>
    (List.range 13).foldl (fun acc' v =>
      if hUV : u < v then
        if ((decide (u = 0) && decide (v = 7)) || (decide (u = 1) && decide (v = 8)))
            ||
            ((u ≤ 6 && v ≤ 6 && ¬ (u = 0 && v = 1)) ||
             (u ≥ 7 && v ≥ 7 && ¬ (u = 7 && v = 8))) then
          setBit acc' (upperIndex u v) true
        else
          acc'
      else
        acc') acc) h
  exact h'

def degreeTableFromUpper13 (g : BitVec 78) : BitVec 52 :=
  (List.range 13).foldl (fun acc v =>
    let d := degreeBitsUpper (n := 13) g v
    let b0 := d.b0
    let b1 := d.b1
    let b2 := d.b2
    let b3 := d.b3
    let acc0 := if b0 then setBit acc (4 * v) true else acc
    let acc1 := if b1 then setBit acc0 (4 * v + 1) true else acc0
    let acc2 := if b2 then setBit acc1 (4 * v + 2) true else acc1
    let acc3 := if b3 then setBit acc2 (4 * v + 3) true else acc2
    acc3) (0#52)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
example : hasHighLowEdge13 gCounter = true := by
  native_decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
example :
    fixedDegreeSequenceUpper (n := 13) gCounter
      [6, 6, 6, 6, 6, 6, 6, 5, 5, 5, 5, 5, 5] = true := by
  native_decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
example :
    degreeTableConsistent13 gCounter (degreeTableFromUpper13 gCounter) = true := by
  native_decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
example :
    pathClosureParallelRel13 gCounter gCounter (degreeTableFromUpper13 gCounter) = true := by
  native_decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
example :
    completeUpper (n := 13) gCounter = false := by
  native_decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
theorem disproof_shared_degree_theorem :
    ¬ (∀ (g g1 g2 g3 g4 : BitVec 78) (d d1 d2 d3 : BitVec 52),
      hasHighLowEdge13 g = true →
      fixedDegreeSequenceUpper (n := 13) g
        [6, 6, 6, 6, 6, 6, 6, 5, 5, 5, 5, 5, 5] = true →
      degreeTableConsistent13 g d = true →
      pathClosureParallelRel13 g g1 d = true →
      degreeTableConsistent13 g1 d1 = true →
      pathClosureParallelRel13 g1 g2 d1 = true →
      degreeTableConsistent13 g2 d2 = true →
      pathClosureParallelRel13 g2 g3 d2 = true →
      degreeTableConsistent13 g3 d3 = true →
      pathClosureParallelRel13 g3 g4 d3 = true →
      completeUpper (n := 13) g4 = true) := by
  intro h
  let dg := degreeTableFromUpper13 gCounter
  have hHigh : hasHighLowEdge13 gCounter = true := by
    native_decide
  have hSeq : fixedDegreeSequenceUpper (n := 13) gCounter
      [6, 6, 6, 6, 6, 6, 6, 5, 5, 5, 5, 5, 5] = true := by
    native_decide
  have hCons0 : degreeTableConsistent13 gCounter dg = true := by
    native_decide
  have hRel0 : pathClosureParallelRel13 gCounter gCounter dg = true := by
    native_decide
  have hFinal : completeUpper (n := 13) gCounter = true :=
    h gCounter gCounter gCounter gCounter gCounter dg dg dg dg
      hHigh hSeq hCons0 hRel0 hCons0 hRel0 hCons0 hRel0 hCons0 hRel0
  have hNot : completeUpper (n := 13) gCounter = false := by
    native_decide
  cases hFinal.trans hNot

end Scratch
