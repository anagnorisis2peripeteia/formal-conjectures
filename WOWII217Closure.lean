import WOWII217FiniteBase

/-!
Boolean Bondy--Chvatal path-closure computations used by the finite part of
WOWII 217.  The semantic theorem that each admitted edge preserves
traceability is deliberately kept separate from these computations.
-/

namespace WOWII217Closure

open WOWII217FiniteBase

def upperPairs (n : Nat) : List (Nat × Nat) :=
  (List.range n).flatMap fun v =>
    (List.range v).map fun u => (u, v)

def upperIndex (u v : Nat) : Nat :=
  v * (v - 1) / 2 + u

def degreeUpperNat {n : Nat} (g : BitVec (edgeCount n)) (u : Nat) : Nat :=
  (List.range n).foldl (fun degree v =>
    degree + if adjUpper g u v then 1 else 0) 0

/-- One ordered scan of all absent edges, adding an edge as soon as its
current endpoint-degree sum is at least `n - 1`. -/
def pathClosureScan {n : Nat} (g : BitVec (edgeCount n)) :
    BitVec (edgeCount n) :=
  (upperPairs n).foldl (fun current edge =>
    let u := edge.1
    let v := edge.2
    if adjUpper current u v then current
    else if decide (n - 1 ≤ degreeUpperNat current u + degreeUpperNat current v) then
      setBit current (upperIndex u v) true
    else current) g

/-- Iterating for the number of possible edges is enough to reach every edge
that this monotone closure procedure can add. -/
def pathClosure {n : Nat} (g : BitVec (edgeCount n)) :
    BitVec (edgeCount n) :=
  (List.range (edgeCount n)).foldl (fun current _ => pathClosureScan current) g

def pathClosureRounds {n : Nat} (rounds : Nat) (g : BitVec (edgeCount n)) :
    BitVec (edgeCount n) :=
  (List.range rounds).foldl (fun current _ => pathClosureScan current) g

def degreeUpperBv5 {n : Nat} (g : BitVec (edgeCount n)) (u : Nat) : BitVec 5 :=
  (List.range n).foldl (fun sum v =>
    sum + bif adjUpper g u v then 1#5 else 0#5) 0#5

/-- The mask of all edges that meet the path-closure degree threshold in the
same input graph.  Keeping the degree tests tied to `g` gives the bitblaster a
shared expression for a whole closure round. -/
def pathClosureParallelMask {n : Nat} (g : BitVec (edgeCount n)) :
    BitVec (edgeCount n) :=
  (upperPairs n).foldl (fun added edge =>
    let u := edge.1
    let v := edge.2
    let legal := !adjUpper g u v &&
      (BitVec.ofNat 5 (n - 1) ≤ degreeUpperBv5 g u + degreeUpperBv5 g v)
    setBit added (upperIndex u v) legal) (BitVec.zero (edgeCount n))

/-- One parallel Bondy--Chvatal path-closure round. -/
def pathClosureParallelRound {n : Nat} (g : BitVec (edgeCount n)) :
    BitVec (edgeCount n) :=
  g ||| pathClosureParallelMask g

def pathClosureParallelRounds {n : Nat} (rounds : Nat)
    (g : BitVec (edgeCount n)) : BitVec (edgeCount n) :=
  (List.range rounds).foldl (fun current _ => pathClosureParallelRound current) g

def completeUpper {n : Nat} (g : BitVec (edgeCount n)) : Bool :=
  (upperPairs n).all fun edge => adjUpper g edge.1 edge.2

end WOWII217Closure
