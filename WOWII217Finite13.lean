import WOWII217FiniteBase

/-!
SAT certificate probe for the sole order-13 degree sequence not discharged by
the external Chvatal reduction.
-/

namespace WOWII217Finite13

open WOWII217FiniteBase

def dpAt13
    (d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 : BitVec 8192) :
    Nat → BitVec 8192
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
  | _ => d12

def hamiltonianDPConsistent13Split (g : BitVec 78)
    (d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 : BitVec 8192) : Bool :=
  (List.range 13).all fun v =>
    let extended := (List.range 13).foldl (fun states u =>
      states ||| (bitMask (w := 8192) (adjUpper (n := 13) g u v) &&&
        ((dpAt13 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 u &&&
          absentMask 13 v) <<< (2 ^ v)))) 0#8192
    dpAt13 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 v ==
      (BitVec.twoPow 8192 (2 ^ v) ||| extended)

def hamiltonianDPHasFullPath13Split
    (d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 : BitVec 8192) : Bool :=
  d0.getLsbD 8191 || d1.getLsbD 8191 || d2.getLsbD 8191 ||
  d3.getLsbD 8191 || d4.getLsbD 8191 || d5.getLsbD 8191 ||
  d6.getLsbD 8191 || d7.getLsbD 8191 || d8.getLsbD 8191 ||
  d9.getLsbD 8191 || d10.getLsbD 8191 || d11.getLsbD 8191 ||
  d12.getLsbD 8191

/-- Vertex `0` has `r` degree-six neighbours and `6-r` degree-five
neighbours, packed into prefixes of their degree blocks. -/
def zeroDegreeBlocksPattern13 (g : BitVec 78) (r : Nat) : Bool :=
  (List.range 6).all (fun offset =>
      !(adjUpper (n := 13) g 0 (offset + 1) ^^ decide (offset < r))) &&
  (List.range 6).all (fun offset =>
    !(adjUpper (n := 13) g 0 (offset + 7) ^^ decide (offset < 6 - r)))

/-- Symmetry-breaking normal form for a degree-preserving relabelling. -/
def canonicalZeroDegreeBlocks13 (g : BitVec 78) : Bool :=
  (List.range 7).any fun r => zeroDegreeBlocksPattern13 g r

def adjacencyCountRange13 (g : BitVec 78) (u start count : Nat) : Nat :=
  (List.range count).foldl (fun total offset =>
    total + if adjUpper (n := 13) g u (start + offset) then 1 else 0) 0

/-- An invariant key under permutations inside each of the four blocks cut out
by degree and adjacency to vertex `0`. Base eight is larger than every block
count, so comparison is lexicographic on the four counts. -/
def degreeBlockKey13 (g : BitVec 78) (r u : Nat) : Nat :=
  adjacencyCountRange13 g u 1 r +
    8 * adjacencyCountRange13 g u (r + 1) (6 - r) +
    64 * adjacencyCountRange13 g u 7 (6 - r) +
    512 * adjacencyCountRange13 g u (13 - r) r

def degreeBlockSorted13 (g : BitVec 78) (r start count : Nat) : Bool :=
  (List.range (count - 1)).all fun offset =>
    decide (degreeBlockKey13 g r (start + offset) ≤
      degreeBlockKey13 g r (start + offset + 1))

/-- The strengthened normal form also sorts each freely permutable block by an
adjacency-count vector whose value is invariant under those permutations. -/
def canonicalSortedDegreeBlocks13 (g : BitVec 78) : Bool :=
  (List.range 7).any fun r =>
    zeroDegreeBlocksPattern13 g r &&
      degreeBlockSorted13 g r 1 r &&
      degreeBlockSorted13 g r (r + 1) (6 - r) &&
      degreeBlockSorted13 g r 7 (6 - r) &&
      degreeBlockSorted13 g r (13 - r) r

def adjacencyRowCodeRange13 (g : BitVec 78) (u start count : Nat) : Nat :=
  (List.range count).foldl (fun code offset =>
    code + if adjUpper (n := 13) g u (start + offset) then 2 ^ offset else 0) 0

/-- Sequential key: stage zero uses only invariant block counts. Each later
stage also records adjacency rows to all earlier, already-sorted blocks. Later
block permutations therefore cannot disturb an earlier stage's order. -/
def sequentialDegreeBlockKey13 (g : BitVec 78) (r stage u : Nat) : Nat :=
  let base := degreeBlockKey13 g r u
  let rowA := adjacencyRowCodeRange13 g u 1 r
  let rowB := adjacencyRowCodeRange13 g u (r + 1) (6 - r)
  let rowC := adjacencyRowCodeRange13 g u 7 (6 - r)
  match stage with
  | 0 => base
  | 1 => base + 4096 * rowA
  | 2 => base + 4096 * (rowA + 128 * rowB)
  | _ => base + 4096 * (rowA + 128 * rowB + 16384 * rowC)

def sequentialDegreeBlockSorted13 (g : BitVec 78)
    (r stage start count : Nat) : Bool :=
  (List.range (count - 1)).all fun offset =>
    decide (sequentialDegreeBlockKey13 g r stage (start + offset) ≤
      sequentialDegreeBlockKey13 g r stage (start + offset + 1))

def sequentialDegreeBlocksPattern13 (g : BitVec 78) (r : Nat) : Bool :=
  zeroDegreeBlocksPattern13 g r &&
    sequentialDegreeBlockSorted13 g r 0 1 r &&
    sequentialDegreeBlockSorted13 g r 1 (r + 1) (6 - r) &&
    sequentialDegreeBlockSorted13 g r 2 7 (6 - r) &&
    sequentialDegreeBlockSorted13 g r 3 (13 - r) r

/-- A stronger canonical form obtained by sorting the four blocks in order.
The key for each block uses only invariants and adjacency rows to blocks whose
order has already been fixed. -/
def canonicalSequentialDegreeBlocks13 (g : BitVec 78) : Bool :=
  (List.range 7).any fun r => sequentialDegreeBlocksPattern13 g r

def bitListLexLe13 : List Bool → List Bool → Bool
  | [], [] => true
  | x :: xs, y :: ys => if x ^^ y then !x && y else bitListLexLe13 xs ys
  | _, _ => false

def blockOrderedVertex13 (start : Nat) (order : List Nat) (i : Nat) : Nat :=
  start + order.getD i i

/-- Signature of an ordering of one contiguous block. It records, in order,
the rows to all earlier blocks and then the induced upper triangle. -/
def blockOrderSignature13 (g : BitVec 78) (start count : Nat)
    (order : List Nat) : List Bool :=
  ((List.range count).flatMap fun i =>
      (List.range (start - 1)).map fun offset =>
        adjUpper (n := 13) g (blockOrderedVertex13 start order i) (offset + 1)) ++
    ((List.range count).flatMap fun j =>
      (List.range j).map fun i =>
        adjUpper (n := 13) g (blockOrderedVertex13 start order i)
          (blockOrderedVertex13 start order j))

/-- The current block order is lexicographically least among all permutations
of that block, using only its internal graph and rows to already-fixed blocks. -/
def canonicalPermutationBlock13 (g : BitVec 78) (start count : Nat) : Bool :=
  let identity := List.range count
  identity.permutations.all fun order =>
    bitListLexLe13 (blockOrderSignature13 g start count identity)
      (blockOrderSignature13 g start count order)

/-- Full sequential block canonization. A later block's signature may use all
earlier blocks, but no earlier signature depends on a later block, so the four
minimum choices can be made in order. -/
def canonicalPermutationBlocksPattern13 (g : BitVec 78) (r : Nat) : Bool :=
  zeroDegreeBlocksPattern13 g r &&
    canonicalPermutationBlock13 g 1 r &&
    canonicalPermutationBlock13 g (r + 1) (6 - r) &&
    canonicalPermutationBlock13 g 7 (6 - r) &&
    canonicalPermutationBlock13 g (13 - r) r

end WOWII217Finite13
