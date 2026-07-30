import FormalConjecturesUtil
import Std.Tactic.BVDecide

/-! A scalable SAT certificate experiment for the n = 8 WOWII 217 shards. -/

namespace WOWII217N8Closure

def natBit (x i : Nat) : Bool := decide (x / 2 ^ i % 2 = 1)

def bitMask {w : Nat} (b : Bool) : BitVec w :=
  BitVec.cast (by simp) (BitVec.replicate w (BitVec.ofBool b))

def setBit {w : Nat} (x : BitVec w) (i : Nat) (b : Bool) : BitVec w :=
  x ||| (bitMask (w := w) b &&& BitVec.twoPow w i)

structure BoolFour where
  b0 : Bool
  b1 : Bool
  b2 : Bool
  b3 : Bool

def BoolFour.ofNat (x : Nat) : BoolFour :=
  { b0 := natBit x 0, b1 := natBit x 1, b2 := natBit x 2, b3 := natBit x 3 }

def BoolFour.same (x y : BoolFour) : Bool :=
  !(x.b0 ^^ y.b0) && !(x.b1 ^^ y.b1) && !(x.b2 ^^ y.b2) && !(x.b3 ^^ y.b3)

def BoolFour.increment (x : BoolFour) (b : Bool) : BoolFour :=
  let c1 := x.b0 && b
  let c2 := x.b1 && c1
  let c3 := x.b2 && c2
  { b0 := x.b0 ^^ b, b1 := x.b1 ^^ c1, b2 := x.b2 ^^ c2, b3 := x.b3 ^^ c3 }

def edgeCount (n : Nat) : Nat := n * (n - 1) / 2

def adjUpper {n : Nat} (g : BitVec (edgeCount n)) (u v : Nat) : Bool :=
  if u < v then g.getLsbD (v * (v - 1) / 2 + u)
  else if v < u then g.getLsbD (u * (u - 1) / 2 + v)
  else false

def degreeBitsUpper {n : Nat} (g : BitVec (edgeCount n)) (u : Nat) : BoolFour :=
  (List.range n).foldl (fun bits v => bits.increment (adjUpper g u v))
    { b0 := false, b1 := false, b2 := false, b3 := false }

def reachableFromZeroUpper {n : Nat} (g : BitVec (edgeCount n)) : BitVec n :=
  (List.range n).foldl (fun seen _ =>
    (List.range n).foldl (fun next v =>
      let discovered := (List.range n).any fun u =>
        seen.getLsbD u && adjUpper g u v
      setBit next v discovered) seen) (BitVec.twoPow n 0)

def connectedUpper {n : Nat} (g : BitVec (edgeCount n)) : Bool :=
  let seen := reachableFromZeroUpper g
  (List.range n).all fun v => seen.getLsbD v

def matchesDegreesFromUpper {n : Nat} (g : BitVec (edgeCount n)) :
    Nat → List Nat → Bool
  | _, [] => true
  | i, d :: ds =>
      (degreeBitsUpper g i).same (.ofNat d) && matchesDegreesFromUpper g (i + 1) ds

def fixedDegreeSequenceUpper {n : Nat} (g : BitVec (edgeCount n))
    (ds : List Nat) : Bool :=
  decide (ds.length = n) && matchesDegreesFromUpper g 0 ds

def hamiltonianBit {n : Nat} (table : BitVec ((2 ^ n) * n))
    (mask vertex : Nat) : Bool :=
  table.getLsbD (mask * n + vertex)

/-- A one-sided reachability table: singleton paths are present, legal extensions are closed,
and no full-set endpoint is present.  Such a table exists exactly when no Hamiltonian path does. -/
def certifiesNoHamiltonianPathClosureUpper {n : Nat}
    (g : BitVec (edgeCount n)) (table : BitVec ((2 ^ n) * n)) : Bool :=
  (List.range n).all (fun v => hamiltonianBit table (2 ^ v) v) &&
    (List.range (2 ^ n)).all (fun mask =>
      (List.range n).all (fun u =>
        (List.range n).all (fun v =>
          !hamiltonianBit table mask u || natBit mask v || !adjUpper g u v ||
            hamiltonianBit table (mask + 2 ^ v) v))) &&
    (List.range n).all fun v => !hamiltonianBit table ((2 ^ n) - 1) v

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
example : ∀ (g : BitVec (edgeCount 8)) (ham : BitVec ((2 ^ 8) * 8)),
    (connectedUpper (n := 8) g &&
      fixedDegreeSequenceUpper (n := 8) g [4, 4, 4, 4, 4, 2, 2, 2] &&
      certifiesNoHamiltonianPathClosureUpper (n := 8) g ham) = false := by
  simp (config := { maxSteps := 100000000 }) only
    [edgeCount, connectedUpper, reachableFromZeroUpper,
    fixedDegreeSequenceUpper, matchesDegreesFromUpper, degreeBitsUpper,
    BoolFour.increment, BoolFour.same, BoolFour.ofNat,
    certifiesNoHamiltonianPathClosureUpper, hamiltonianBit,
    adjUpper, setBit, bitMask, natBit,
    List.range, List.range.loop, List.foldl, List.length, List.all, List.any]
  bv_decide (maxSteps := 100000000) (timeout := 600)

end WOWII217N8Closure
