import WOWII217Closure
import WOWII217FiniteBase

open WOWII217FiniteBase WOWII217Closure

/-- Local copy of shared-degree machinery. -/
def majority' (a b c : Bool) : Bool :=
  (a && b) || (a && c) || (b && c)

def boolFourSumAtLeast12Upper13' (x y : BoolFour) : Bool :=
  let c1 := x.b0 && y.b0
  let c2 := majority' x.b1 y.b1 c1
  let s2 := x.b2 ^^ y.b2 ^^ c2
  let c3 := majority' x.b2 y.b2 c2
  let s3 := x.b3 ^^ y.b3 ^^ c3
  let c4 := majority' x.b3 y.b3 c3
  c4 || (s3 && s2)

def degreeTableAt13_local (degrees : BitVec 52) (v : Nat) : BoolFour :=
  { b0 := degrees.getLsbD (4 * v),
    b1 := degrees.getLsbD (4 * v + 1),
    b2 := degrees.getLsbD (4 * v + 2),
    b3 := degrees.getLsbD (4 * v + 3) }

def degreeTableConsistent13_local (g : BitVec 78) (degrees : BitVec 52) : Bool :=
  (List.range 13).all fun v =>
    (degreeBitsUpper (n := 13) g v).same (degreeTableAt13_local degrees v)

def pathClosureParallelRel13_local (g next : BitVec 78) (degrees : BitVec 52) : Bool :=
  (upperPairs 13).all fun edge =>
    let u := edge.1
    let v := edge.2
    !(adjUpper (n := 13) next u v ^^
      (adjUpper (n := 13) g u v ||
        boolFourSumAtLeast12Upper13' (degreeTableAt13_local degrees u)
          (degreeTableAt13_local degrees v)))

def hasHighLowEdge13_local (g : BitVec 78) : Bool :=
  (List.range 7).any fun u =>
    (List.range 6).any fun offset => adjUpper (n := 13) g u (offset + 7)

/-- Counterexample adjacency on N = 13, with blocks A={0,1,2,3,4,5,7}, B={6,8,9,10,11,12}. -/
def adjCounter13 (u v : Nat) : Bool :=
  if h : u = v then false else
    ((u = 0 || u = 1 || u = 2 || u = 3 || u = 4 || u = 5 || u = 7) &&
     (v = 0 || v = 1 || v = 2 || v = 3 || v = 4 || v = 5 || v = 7)) ||
    ((u = 6 || u = 8 || u = 9 || u = 10 || u = 11 || u = 12) &&
     (v = 6 || v = 8 || v = 9 || v = 10 || v = 11 || v = 12))

def encUpper13_local (gAdj : Nat → Nat → Bool) : BitVec 78 :=
  (upperPairs 13).foldl (fun acc e =>
    let u := e.1
    let v := e.2
    if gAdj u v then setBit acc (upperIndex u v) true else acc)
    (BitVec.zero 78)

def setDegreeNibble (d : BitVec 52) (v : Nat) (bits : BoolFour) : BitVec 52 :=
  let d0 := setBit d (4 * v) bits.b0
  let d1 := setBit d0 (4 * v + 1) bits.b1
  let d2 := setBit d1 (4 * v + 2) bits.b2
  setBit d2 (4 * v + 3) bits.b3

def degreeTableFromUpper (g : BitVec 78) : BitVec 52 :=
  (List.range 13).foldl (fun acc v =>
    setDegreeNibble acc v (degreeBitsUpper (n := 13) g v)) (BitVec.zero 52)

def gCounter : BitVec 78 := encUpper13_local adjCounter13

def dCounter : BitVec 52 := degreeTableFromUpper gCounter

#eval (fixedDegreeSequenceUpper (n := 13) gCounter [6,6,6,6,6,6,6,5,5,5,5,5,5])
#eval (hasHighLowEdge13_local gCounter)
#eval (connectedUpper (n := 13) gCounter)
#eval (degreeTableConsistent13_local gCounter dCounter)
#eval (pathClosureParallelRel13_local gCounter gCounter dCounter)
#eval (completeUpper (n := 13) gCounter)
#eval (pathClosureParallelRel13_local gCounter gCounter dCounter &&
  pathClosureParallelRel13_local gCounter gCounter dCounter &&
  pathClosureParallelRel13_local gCounter gCounter dCounter)
