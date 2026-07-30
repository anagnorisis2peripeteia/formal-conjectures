import FormalConjecturesUtil
import Std.Tactic.BVDecide
import WOWII217Semantics

/-!
Finite SAT certificate for the exceptional 14-vertex regular class arising in
WOWII Graph Conjecture 217.
-/

namespace WOWII217DP

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

/-- For each subset mask, store the bitset of possible endpoints of a path whose
vertex set is exactly that mask. Subsets are processed in increasing numeric order. -/
def hamiltonianEndpointTable {n : Nat} (g : BitVec (edgeCount n)) : Array (BitVec n) :=
  (List.range (2 ^ n)).foldl (fun table mask =>
    let ends := (List.range n).foldl (fun ends v =>
      let singleton := decide (mask = 2 ^ v)
      let previous := table.getD (mask - 2 ^ v) (BitVec.zero n)
      let canExtend := (List.range n).any fun u =>
        previous.getLsbD u && adjUpper g u v
      setBit ends v (maskHas mask v && (singleton || canExtend))) (BitVec.zero n)
    table.push ends) #[]

def hasHamiltonianPathDP {n : Nat} (g : BitVec (edgeCount n)) : Bool :=
  let table := hamiltonianEndpointTable g
  let ends := table.getD (2 ^ n - 1) (BitVec.zero n)
  (List.range n).any fun v => ends.getLsbD v

structure BoolFour where
  b0 : Bool
  b1 : Bool
  b2 : Bool
  b3 : Bool

def BoolFour.ofNat (x : Nat) : BoolFour :=
  { b0 := maskHas x 0, b1 := maskHas x 1, b2 := maskHas x 2, b3 := maskHas x 3 }

def BoolFour.same (x y : BoolFour) : Bool :=
  !(x.b0 ^^ y.b0) && !(x.b1 ^^ y.b1) && !(x.b2 ^^ y.b2) && !(x.b3 ^^ y.b3)

def BoolFour.increment (x : BoolFour) (b : Bool) : BoolFour :=
  let c1 := x.b0 && b
  let c2 := x.b1 && c1
  let c3 := x.b2 && c2
  { b0 := x.b0 ^^ b, b1 := x.b1 ^^ c1, b2 := x.b2 ^^ c2, b3 := x.b3 ^^ c3 }

/-- Unsigned comparison of the four stored bits, most significant first. -/
def BoolFour.le (x y : BoolFour) : Bool :=
  if x.b3 ^^ y.b3 then !x.b3 && y.b3
  else if x.b2 ^^ y.b2 then !x.b2 && y.b2
  else if x.b1 ^^ y.b1 then !x.b1 && y.b1
  else !x.b0 || y.b0

def degreeBitsUpper {n : Nat} (g : BitVec (edgeCount n)) (u : Nat) : BoolFour :=
  (List.range n).foldl (fun bits v => bits.increment (adjUpper g u v))
    { b0 := false, b1 := false, b2 := false, b3 := false }

def matchesDegreesFromUpper {n : Nat} (g : BitVec (edgeCount n)) :
    Nat → List Nat → Bool
  | _, [] => true
  | i, d :: ds =>
      (degreeBitsUpper g i).same (.ofNat d) && matchesDegreesFromUpper g (i + 1) ds

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

def dpWidth (n : Nat) : Nat := 2 ^ n * n

def dpBit {n : Nat} (dp : BitVec (dpWidth n)) (mask v : Nat) : Bool :=
  dp.getLsbD (mask * n + v)

/-- The characteristic table for Held--Karp endpoint reachability. This is a
relation on an auxiliary bitvector, rather than an in-expression mutable array,
so the SAT checker sees a compact Tseitin-style certificate. -/
def hamiltonianDPConsistent {n : Nat} (g : BitVec (edgeCount n))
    (dp : BitVec (dpWidth n)) : Bool :=
  (List.range (2 ^ n)).all fun mask =>
    (List.range n).all fun v =>
      let singleton := decide (mask = 2 ^ v)
      let canExtend := (List.range n).any fun u =>
        dpBit dp (mask - 2 ^ v) u && adjUpper g u v
      !(dpBit dp mask v ^^ (maskHas mask v && (singleton || canExtend)))

def hamiltonianDPHasFullPath {n : Nat} (dp : BitVec (dpWidth n)) : Bool :=
  (List.range n).any fun v => dpBit dp (2 ^ n - 1) v

/-- Bit `mask` is set exactly when vertex `v` is absent from `mask`. The recursive
construction doubles the previous pattern, except at the newly introduced vertex,
where the lower half is one and the upper half is zero. -/
def absentMask : (n v : Nat) → BitVec (2 ^ n)
  | 0, _ => 1#1
  | n + 1, v =>
      if v = n then
        BitVec.cast (by simp [pow_succ, Nat.mul_two])
          (BitVec.append (BitVec.zero (2 ^ n)) (BitVec.allOnes (2 ^ n)))
      else
        BitVec.cast (by simp [pow_succ, Nat.mul_two])
          (BitVec.append (absentMask n v) (absentMask n v))

def absentMask8 : Nat → BitVec 256
  | 0 => 0x5555555555555555555555555555555555555555555555555555555555555555#256
  | 1 => 0x3333333333333333333333333333333333333333333333333333333333333333#256
  | 2 => 0x0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f#256
  | 3 => 0x00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff#256
  | 4 => 0x0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff#256
  | 5 => 0x00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff#256
  | 6 => 0x0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff#256
  | 7 => 0x00000000000000000000000000000000ffffffffffffffffffffffffffffffff#256
  | _ => 0#256

def dpBlock8 (dp : BitVec 2048) (v : Nat) : BitVec 256 :=
  dp.extractLsb' (v * 256) 256

def hamiltonianDPConsistent8 (g : BitVec 28) (dp : BitVec 2048) : Bool :=
  (List.range 8).all fun v =>
    let extended := (List.range 8).foldl (fun states u =>
      states ||| (bitMask (w := 256) (adjUpper (n := 8) g u v) &&&
        ((dpBlock8 dp u &&& absentMask 8 v) <<< (2 ^ v)))) 0#256
    dpBlock8 dp v == (BitVec.twoPow 256 (2 ^ v) ||| extended)

def hamiltonianDPHasFullPath8 (dp : BitVec 2048) : Bool :=
  (List.range 8).any fun v => (dpBlock8 dp v).getLsbD 255

-- The DP finds a Hamiltonian path in the complete graph on eight vertices.
example : hasHamiltonianPathDP (n := 8) (0xfffffff#28) = true := by
  native_decide

example : fixedDegreeSequenceUpper (n := 8) (0xc1003ff#28)
    [4, 4, 4, 4, 4, 2, 2, 2] = true := by
  decide

example : hasHamiltonianPathDP (n := 8) (0xc1003ff#28) = false := by
  native_decide

-- Scaling probe: every connected graph in the exceptional
-- (4,4,4,4,4,2,2,2) class has a full Held--Karp state.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem degreeSequence44444222_hasHamiltonianDPState :
    ∀ (g : BitVec 28) (dp : BitVec 2048),
      (connectedUpper (n := 8) g &&
        fixedDegreeSequenceUpper (n := 8) g [4, 4, 4, 4, 4, 2, 2, 2] &&
        hamiltonianDPConsistent8 g dp &&
        !hamiltonianDPHasFullPath8 dp) = false := by
  simp (config := { maxSteps := 100000000 }) only
    [edgeCount, fixedDegreeSequenceUpper, matchesDegreesFromUpper, degreeBitsUpper,
      BoolFour.increment, BoolFour.same, BoolFour.ofNat,
      connectedUpper, reachableFromZeroUpper,
      hamiltonianDPConsistent8, hamiltonianDPHasFullPath8, dpBlock8, absentMask,
      maskHas, adjUpper, setBit, bitMask,
      List.range, List.range.loop, List.foldl, List.all, List.any]
  bv_decide (maxSteps := 100000000) (timeout := 600)

def dpBlock14 (dp : BitVec 229376) (v : Nat) : BitVec 16384 :=
  dp.extractLsb' (v * 16384) 16384

def hamiltonianDPConsistent14 (g : BitVec 91) (dp : BitVec 229376) : Bool :=
  (List.range 14).all fun v =>
    let extended := (List.range 14).foldl (fun states u =>
      states ||| (bitMask (w := 16384) (adjUpper (n := 14) g u v) &&&
        ((dpBlock14 dp u &&& absentMask 14 v) <<< (2 ^ v)))) 0#16384
    dpBlock14 dp v == (BitVec.twoPow 16384 (2 ^ v) ||| extended)

def hamiltonianDPHasFullPath14 (dp : BitVec 229376) : Bool :=
  (List.range 14).any fun v => (dpBlock14 dp v).getLsbD 16383

/-- The same endpoint table represented by fourteen separate blocks. Keeping
each endpoint block at width `2^14` avoids normalising extracts from one
229376-bit vector. -/
def dpAt14
    (d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 : BitVec 16384) :
    Nat → BitVec 16384
  | 0 => d0
  | 1 => d1
  | 2 => d2
  | 3 => d3
  | 4 => d4
  | 5 => d5
  | 6 => d6
  | 7 => d7
  | 8 => d8
  | 9 => d9
  | 10 => d10
  | 11 => d11
  | 12 => d12
  | _ => d13

def hamiltonianDPConsistent14Split (g : BitVec 91)
    (d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 : BitVec 16384) : Bool :=
  (List.range 14).all fun v =>
    let extended := (List.range 14).foldl (fun states u =>
      states ||| (bitMask (w := 16384) (adjUpper (n := 14) g u v) &&&
        ((dpAt14 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 u &&&
          absentMask 14 v) <<< (2 ^ v)))) 0#16384
    dpAt14 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 v ==
      (BitVec.twoPow 16384 (2 ^ v) ||| extended)

def hamiltonianDPHasFullPath14Split
    (d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 : BitVec 16384) : Bool :=
  d0.getLsbD 16383 || d1.getLsbD 16383 || d2.getLsbD 16383 ||
  d3.getLsbD 16383 || d4.getLsbD 16383 || d5.getLsbD 16383 ||
  d6.getLsbD 16383 || d7.getLsbD 16383 || d8.getLsbD 16383 ||
  d9.getLsbD 16383 || d10.getLsbD 16383 || d11.getLsbD 16383 ||
  d12.getLsbD 16383 || d13.getLsbD 16383

-- Up to relabelling, any 6-regular graph has this neighbourhood at vertex 0.
-- This removes the 14! labelling symmetry from the SAT certificate.
def canonicalZeroNeighborhood14 (g : BitVec 91) : Bool :=
  adjUpper (n := 14) g 0 1 &&
  adjUpper (n := 14) g 0 2 &&
  adjUpper (n := 14) g 0 3 &&
  adjUpper (n := 14) g 0 4 &&
  adjUpper (n := 14) g 0 5 &&
  adjUpper (n := 14) g 0 6 &&
  !adjUpper (n := 14) g 0 7 &&
  !adjUpper (n := 14) g 0 8 &&
  !adjUpper (n := 14) g 0 9 &&
  !adjUpper (n := 14) g 0 10 &&
  !adjUpper (n := 14) g 0 11 &&
  !adjUpper (n := 14) g 0 12 &&
  !adjUpper (n := 14) g 0 13

def degreeBitsRangeUpper (g : BitVec 91) (u start count : Nat) : BoolFour :=
  (List.range count).foldl (fun bits offset =>
    bits.increment (adjUpper (n := 14) g u (start + offset)))
    { b0 := false, b1 := false, b2 := false, b3 := false }

def bitListLexLe : List Bool → List Bool → Bool
  | [], [] => true
  | x :: xs, y :: ys => if x ^^ y then !x && y else bitListLexLe xs ys
  | _, _ => false

def adjacencyRowToZeroNeighbors14 (g : BitVec 91) (u : Nat) : List Bool :=
  [adjUpper (n := 14) g u 6, adjUpper (n := 14) g u 5,
    adjUpper (n := 14) g u 4, adjUpper (n := 14) g u 3,
    adjUpper (n := 14) g u 2, adjUpper (n := 14) g u 1]

def nonneighborKeyLe14 (g : BitVec 91) (u v : Nat) : Bool :=
  let du := degreeBitsRangeUpper g u 1 6
  let dv := degreeBitsRangeUpper g v 1 6
  du.le dv &&
    (!du.same dv || bitListLexLe
      (adjacencyRowToZeroNeighbors14 g u) (adjacencyRowToZeroNeighbors14 g v))

/-- After fixing the neighbourhood of vertex 0, vertices remain freely
permutable inside `{1, ..., 6}` and `{7, ..., 13}`. Sort both blocks by their
number of cross-block neighbours to remove that residual symmetry. -/
def canonicalPartitionDegreesSorted14 (g : BitVec 91) : Bool :=
  (degreeBitsRangeUpper g 1 7 7).le (degreeBitsRangeUpper g 2 7 7) &&
  (degreeBitsRangeUpper g 2 7 7).le (degreeBitsRangeUpper g 3 7 7) &&
  (degreeBitsRangeUpper g 3 7 7).le (degreeBitsRangeUpper g 4 7 7) &&
  (degreeBitsRangeUpper g 4 7 7).le (degreeBitsRangeUpper g 5 7 7) &&
  (degreeBitsRangeUpper g 5 7 7).le (degreeBitsRangeUpper g 6 7 7) &&
  nonneighborKeyLe14 g 7 8 &&
  nonneighborKeyLe14 g 8 9 &&
  nonneighborKeyLe14 g 9 10 &&
  nonneighborKeyLe14 g 10 11 &&
  nonneighborKeyLe14 g 11 12 &&
  nonneighborKeyLe14 g 12 13

example : (List.range 15).all (fun x =>
    (List.range 15).all (fun y =>
      !((BoolFour.ofNat x).le (BoolFour.ofNat y) ^^ decide (x ≤ y)))) = true := by
  native_decide

def bitRowSix (x : Nat) : List Bool :=
  [maskHas x 5, maskHas x 4, maskHas x 3, maskHas x 2, maskHas x 1, maskHas x 0]

example : (List.range 64).all (fun x =>
    (List.range 64).all (fun y =>
      !(bitListLexLe (bitRowSix x) (bitRowSix y) ^^ decide (x ≤ y)))) = true := by
  native_decide

-- The canonical labelling of the largest exceptional degree class has a full
-- Held--Karp state. A separate graph-isomorphism lemma transports the result
-- back to arbitrary labels.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
theorem canonicalDegreeSequenceSixRegular14_hasHamiltonianDPState :
    ∀ (g : BitVec 91)
      (d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 : BitVec 16384),
      (connectedUpper (n := 14) g &&
        fixedDegreeSequenceUpper (n := 14) g
          [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] &&
        canonicalZeroNeighborhood14 g &&
        canonicalPartitionDegreesSorted14 g &&
        hamiltonianDPConsistent14Split g
          d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 &&
        !hamiltonianDPHasFullPath14Split
          d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13) = false := by
  simp (config := { maxSteps := 1000000000 }) only
    [edgeCount, fixedDegreeSequenceUpper, matchesDegreesFromUpper, degreeBitsUpper,
      BoolFour.increment, BoolFour.same, BoolFour.ofNat,
      connectedUpper, reachableFromZeroUpper,
      canonicalZeroNeighborhood14, canonicalPartitionDegreesSorted14,
      nonneighborKeyLe14, adjacencyRowToZeroNeighbors14, bitListLexLe,
      degreeBitsRangeUpper, BoolFour.le,
      hamiltonianDPConsistent14Split, hamiltonianDPHasFullPath14Split, dpAt14,
      absentMask,
      maskHas, adjUpper, setBit, bitMask,
      List.range, List.range.loop, List.foldl, List.all, List.any]
  bv_decide (maxSteps := 1000000000) (timeout := 1800)
    (embeddedConstraintSubst := false)

end WOWII217DP
