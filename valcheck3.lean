import WOWII217FiniteBase
import WOWII217Closure
import WOWII217Finite13ClosureSharedDeg

open WOWII217FiniteBase WOWII217Closure WOWII217Finite13ClosureSharedDeg

/-- local definitions -/
def adj (u v : Nat) : Bool :=
  if h : u = v then false else
    ((u = 0 || u = 1 || u = 2 || u = 3 || u = 4 || u = 5 || u = 7) &&
     (v = 0 || v = 1 || v = 2 || v = 3 || v = 4 || v = 5 || v = 7)) ||
    ((u = 6 || u = 8 || u = 9 || u = 10 || u = 11 || u = 12) &&
     (v = 6 || v = 8 || v = 9 || v = 10 || v = 11 || v = 12))

/-- encode adjacency into upper-triangle bits-/
def g : BitVec 78 :=
  (upperPairs 13).foldl (fun acc e =>
    let u := e.1
    let v := e.2
    if adj u v then setBit acc (upperIndex u v) true else acc)
    (BitVec.zero 78)

#eval (List.range 13).map (fun i => degreeUpperNat (n := 13) g i)
#eval (fixedDegreeSequenceUpper (n := 13) g [6,6,6,6,6,6,6,5,5,5,5,5,5])
#eval (connectedUpper (n := 13) g)
#eval (hasHighLowEdge13 g)
#eval (pathClosureParallelRel13 g g (degreeTableOfUpper13 g))
#eval (completeUpper (n := 13) g)
