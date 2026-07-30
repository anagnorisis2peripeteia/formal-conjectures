import WOWII217Closure

/-!
A Boolean-counter implementation of the order-13 path closure.  At order 13
the edge threshold is 12, and the sum of two degrees is at most 24, so five
bits suffice.  This avoids normalizing bounded natural-number addition inside
every degree test in the finite certificate.
-/

namespace WOWII217Closure13Fast

open WOWII217FiniteBase WOWII217Closure

structure BoolFive where
  b0 : Bool
  b1 : Bool
  b2 : Bool
  b3 : Bool
  b4 : Bool

def BoolFive.zero : BoolFive :=
  { b0 := false, b1 := false, b2 := false, b3 := false, b4 := false }

def BoolFive.increment (x : BoolFive) (b : Bool) : BoolFive :=
  let c1 := x.b0 && b
  let c2 := x.b1 && c1
  let c3 := x.b2 && c2
  let c4 := x.b3 && c3
  { b0 := x.b0 ^^ b, b1 := x.b1 ^^ c1, b2 := x.b2 ^^ c2,
    b3 := x.b3 ^^ c3, b4 := x.b4 ^^ c4 }

def degreePairBits13 (g : BitVec 78) (u v : Nat) : BoolFive :=
  let first := (List.range 13).foldl
    (fun count w => count.increment (adjUpper (n := 13) g u w)) BoolFive.zero
  (List.range 13).foldl
    (fun count w => count.increment (adjUpper (n := 13) g v w)) first

/-- A five-bit number is at least binary `01100` exactly when bit four is set,
or bits three and two are both set.  Degree sums here are at most 24. -/
def degreePairAtLeast12Upper13 (g : BitVec 78) (u v : Nat) : Bool :=
  let count := degreePairBits13 g u v
  count.b4 || (count.b3 && count.b2)

def pathClosureParallelMask13 (g : BitVec 78) : BitVec 78 :=
  (upperPairs 13).foldl (fun added edge =>
    let u := edge.1
    let v := edge.2
    let legal := !adjUpper (n := 13) g u v &&
      degreePairAtLeast12Upper13 g u v
    setBit added (upperIndex u v) legal) (BitVec.zero 78)

def pathClosureParallelRound13 (g : BitVec 78) : BitVec 78 :=
  g ||| pathClosureParallelMask13 g

def pathClosureParallelRounds13 (rounds : Nat) (g : BitVec 78) : BitVec 78 :=
  (List.range rounds).foldl (fun current _ => pathClosureParallelRound13 current) g

end WOWII217Closure13Fast
