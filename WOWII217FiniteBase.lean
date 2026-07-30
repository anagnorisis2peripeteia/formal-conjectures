import FormalConjecturesUtil
import Std.Tactic.BVDecide

/-!
Shared Boolean and bit-vector primitives for the finite WOWII 217
certificates. This module deliberately contains no large certificate theorem.
-/

namespace WOWII217FiniteBase

def bitMask {w : Nat} (b : Bool) : BitVec w :=
  BitVec.cast (by simp) (BitVec.replicate w (BitVec.ofBool b))

def setBit {w : Nat} (x : BitVec w) (i : Nat) (b : Bool) : BitVec w :=
  x ||| (bitMask (w := w) b &&& BitVec.twoPow w i)

def edgeCount (n : Nat) : Nat := n * (n - 1) / 2

def adjUpper {n : Nat} (g : BitVec (edgeCount n)) (u v : Nat) : Bool :=
  if u < v then g.getLsbD (v * (v - 1) / 2 + u)
  else if v < u then g.getLsbD (u * (u - 1) / 2 + v)
  else false

def maskHas (mask v : Nat) : Bool :=
  decide (mask / 2 ^ v % 2 = 1)

structure BoolFour where
  b0 : Bool
  b1 : Bool
  b2 : Bool
  b3 : Bool

def BoolFour.ofNat (x : Nat) : BoolFour :=
  { b0 := maskHas x 0, b1 := maskHas x 1,
    b2 := maskHas x 2, b3 := maskHas x 3 }

def BoolFour.same (x y : BoolFour) : Bool :=
  !(x.b0 ^^ y.b0) && !(x.b1 ^^ y.b1) &&
    !(x.b2 ^^ y.b2) && !(x.b3 ^^ y.b3)

def BoolFour.increment (x : BoolFour) (b : Bool) : BoolFour :=
  let c1 := x.b0 && b
  let c2 := x.b1 && c1
  let c3 := x.b2 && c2
  { b0 := x.b0 ^^ b, b1 := x.b1 ^^ c1,
    b2 := x.b2 ^^ c2, b3 := x.b3 ^^ c3 }

def degreeBitsUpper {n : Nat} (g : BitVec (edgeCount n)) (u : Nat) : BoolFour :=
  (List.range n).foldl (fun bits v => bits.increment (adjUpper g u v))
    { b0 := false, b1 := false, b2 := false, b3 := false }

def matchesDegreesFromUpper {n : Nat} (g : BitVec (edgeCount n)) :
    Nat → List Nat → Bool
  | _, [] => true
  | i, d :: ds =>
      (degreeBitsUpper g i).same (.ofNat d) &&
        matchesDegreesFromUpper g (i + 1) ds

def fixedDegreeSequenceUpper {n : Nat} (g : BitVec (edgeCount n))
    (ds : List Nat) : Bool :=
  decide (ds.length = n) && matchesDegreesFromUpper g 0 ds

def reachableFromZeroUpper {n : Nat} (g : BitVec (edgeCount n)) : BitVec n :=
  (List.range n).foldl (fun seen _ =>
    (List.range n).foldl (fun next v =>
      let discovered := (List.range n).any fun u =>
        seen.getLsbD u && adjUpper g u v
      setBit next v discovered) seen) (BitVec.twoPow n 0)

def connectedUpper {n : Nat} (g : BitVec (edgeCount n)) : Bool :=
  let seen := reachableFromZeroUpper g
  (List.range n).all fun v => seen.getLsbD v

/-- Bit `mask` is set exactly when vertex `v` is absent from `mask`. -/
def absentMask : (n v : Nat) → BitVec (2 ^ n)
  | 0, _ => 1#1
  | n + 1, v =>
      if v = n then
        BitVec.cast (by simp [pow_succ, Nat.mul_two])
          (BitVec.append (BitVec.zero (2 ^ n)) (BitVec.allOnes (2 ^ n)))
      else
        BitVec.cast (by simp [pow_succ, Nat.mul_two])
          (BitVec.append (absentMask n v) (absentMask n v))

end WOWII217FiniteBase
