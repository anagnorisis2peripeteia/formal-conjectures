import FormalConjecturesUtil
import Std.Tactic.BVDecide

example : ∀ x : BitVec 8, x &&& x = x := by
  bv_decide

example : ∀ x : BitVec 8, x.getLsbD 3 = x.getLsbD 3 := by
  bv_decide

namespace WOWII217Cert

set_option maxRecDepth 100000

def adj {n : Nat} (g : BitVec (n * n)) (u v : Nat) : Bool :=
  g.getLsbD (u * n + v)

def bitMask {w : Nat} (b : Bool) : BitVec w :=
  BitVec.cast (by simp) (BitVec.replicate w (BitVec.ofBool b))

def selectBitVec {w : Nat} (b : Bool) (x y : BitVec w) : BitVec w :=
  let mask := bitMask (w := w) b
  (mask &&& x) ||| (~~~mask &&& y)

def setBit {w : Nat} (x : BitVec w) (i : Nat) (b : Bool) : BitVec w :=
  x ||| (bitMask (w := w) b &&& BitVec.twoPow w i)

def natBit (x i : Nat) : Bool :=
  decide (x / 2 ^ i % 2 = 1)

def simpleSymmetric {n : Nat} (g : BitVec (n * n)) : Bool :=
  (List.range n).all fun u =>
    !adj g u u && (List.range n).all fun v => adj g u v == adj g v u

def reachability {n : Nat} (g : BitVec (n * n)) : BitVec (n * n) :=
  let initial := (List.range n).foldl (fun r u =>
    (List.range n).foldl (fun r v => setBit r (u * n + v) (u == v || adj g u v)) r) 0
  (List.range n).foldl (fun r k =>
    (List.range n).foldl (fun r i =>
      (List.range n).foldl (fun r j =>
        let reachable := r.getLsbD (i * n + j) ||
          (r.getLsbD (i * n + k) && r.getLsbD (k * n + j))
        setBit r (i * n + j) reachable) r) r) initial

def connected {n : Nat} (g : BitVec (n * n)) : Bool :=
  let r := reachability g
  (List.range n).all fun u => (List.range n).all fun v => r.getLsbD (u * n + v)

def hamiltonianTable {n : Nat} (g : BitVec (n * n)) : BitVec ((2 ^ n) * n) :=
  (List.range (2 ^ n)).foldl (fun table mask =>
    (List.range n).foldl (fun table v =>
      let present := natBit mask v
      let singleton := mask == 2 ^ v
      let previous := mask - 2 ^ v
      let extendable := (List.range n).any fun u =>
        natBit previous u && table.getLsbD (previous * n + u) && adj g u v
      setBit table (mask * n + v) (present && (singleton || extendable))) table) 0

def hasHamiltonianPath {n : Nat} (g : BitVec (n * n)) : Bool :=
  let table := hamiltonianTable g
  (List.range n).any fun v => table.getLsbD (((2 ^ n) - 1) * n + v)

/-- Exhaustive Hamiltonian-path search with a compile-time visited mask.

For small fixed orders this reflects to a Boolean formula over edge bits without materialising the
wide dynamic-programming table used by `hamiltonianTable`. -/
def hasHamiltonianPathFrom {n : Nat} (g : BitVec (n * n))
    (visited : BitVec n) (u : Nat) : Nat → Bool
  | 0 => true
  | fuel + 1 => (List.range n).any fun v =>
      !visited.getLsbD v && adj g u v &&
        hasHamiltonianPathFrom g (setBit visited v true) v fuel

def hasHamiltonianPathDFS {n : Nat} (g : BitVec (n * n)) : Bool :=
  (List.range n).any fun start =>
    hasHamiltonianPathFrom g (setBit (0 : BitVec n) start true) start (n - 1)

abbrev Degree := BitVec 4

def degree {n : Nat} (g : BitVec (n * n)) (u : Nat) : Degree :=
  (List.range n).foldl (fun d v => selectBitVec (adj g u v) (d + 1) d) 0

def maxDegreeAtMostSix {n : Nat} (g : BitVec (n * n)) : Bool :=
  (List.range n).all fun u => (degree g u).ule (BitVec.ofNat 4 6)

def insertDegreeDesc (x : Degree) : List Degree → List Degree
  | [] => [x]
  | y :: ys =>
      let xFirst := y.ule x
      (bif xFirst then x else y) :: insertDegreeDesc (bif xFirst then y else x) ys

def sortDegreesDesc (xs : List Degree) : List Degree :=
  xs.foldr insertDegreeDesc []

def decrementFirst (d : Degree) : Nat → List Degree → List Degree
  | _, [] => []
  | i, x :: xs =>
      (bif (BitVec.ofNat 4 i).ult d then x - 1 else x) :: decrementFirst d (i + 1) xs

def residueDegrees : Nat → List Degree → Degree
  | 0, _ => 0
  | _ + 1, [] => 0
  | fuel + 1, d :: rest =>
      bif d == 0 then BitVec.ofNat 4 (rest.length + 1)
      else residueDegrees fuel (sortDegreesDesc (decrementFirst d 0 rest))

def residueFour {n : Nat} (g : BitVec (n * n)) : Degree :=
  residueDegrees (n + 1) (sortDegreesDesc ((List.range n).map fun u => degree g u))

def residueEqTwo {n : Nat} (g : BitVec (n * n)) : Bool :=
  residueFour g == BitVec.ofNat 4 2

def packedDegree (n : Nat) (ds : BitVec (n * 4)) (u : Nat) : Degree :=
  BitVec.extractLsb' (u * 4) 4 ds

def degreesMatch {n : Nat} (g : BitVec (n * n)) (ds : BitVec (n * 4)) : Bool :=
  (List.range n).all fun u => packedDegree n ds u == degree g u

def packedResidue (n : Nat) (ds : BitVec (n * 4)) : Degree :=
  residueDegrees (n + 1)
    (sortDegreesDesc ((List.range n).map fun u => packedDegree n ds u))

def packedResidueEqTwo (n : Nat) (ds : BitVec (n * 4)) : Bool :=
  packedResidue n ds == BitVec.ofNat 4 2

def traceDegree (n : Nat) (trace : BitVec ((n + 1) * n * 4))
    (stage index : Nat) : Degree :=
  BitVec.extractLsb' ((stage * n + index) * 4) 4 trace

def countPackedDegree (n : Nat) (ds : BitVec (n * 4))
    (active value : Nat) : Degree :=
  (List.range active).foldl (fun count i =>
    bif packedDegree n ds i == BitVec.ofNat 4 value then count + 1 else count) 0

def countTraceDegree (n : Nat) (trace : BitVec ((n + 1) * n * 4))
    (stage active value : Nat) : Degree :=
  (List.range active).foldl (fun count i =>
    bif traceDegree n trace stage i == BitVec.ofNat 4 value then count + 1 else count) 0

def rawHavelDegree (n : Nat) (trace : BitVec ((n + 1) * n * 4))
    (stage index : Nat) : Degree :=
  let d := traceDegree n trace stage 0
  let x := traceDegree n trace stage (index + 1)
  selectBitVec ((BitVec.ofNat 4 index).ult d) (x - 1) x

def countRawHavelDegree (n : Nat) (trace : BitVec ((n + 1) * n * 4))
    (stage active value : Nat) : Degree :=
  (List.range (active - 1)).foldl (fun count i =>
    bif rawHavelDegree n trace stage i == BitVec.ofNat 4 value then count + 1 else count) 0

def traceRowSorted (n : Nat) (trace : BitVec ((n + 1) * n * 4))
    (stage active : Nat) : Bool :=
  (List.range (active - 1)).all fun i =>
    (traceDegree n trace stage (i + 1)).ule (traceDegree n trace stage i)

def sameInitialMultiset (n : Nat) (ds : BitVec (n * 4))
    (trace : BitVec ((n + 1) * n * 4)) : Bool :=
  (List.range 16).all fun value =>
    countTraceDegree n trace 0 n value == countPackedDegree n ds n value

def validHavelTransition (n : Nat) (trace : BitVec ((n + 1) * n * 4))
    (stage active : Nat) : Bool :=
  traceDegree n trace stage 0 != 0 &&
    traceRowSorted n trace (stage + 1) (active - 1) &&
    (List.range 16).all fun value =>
      countTraceDegree n trace (stage + 1) (active - 1) value ==
        countRawHavelDegree n trace stage active value

def validResidueTwoTrace (n : Nat) (ds : BitVec (n * 4))
    (trace : BitVec ((n + 1) * n * 4)) : Bool :=
  sameInitialMultiset n ds trace && traceRowSorted n trace 0 n &&
    (List.range (n - 2)).all (fun stage =>
      validHavelTransition n trace stage (n - stage)) &&
    traceDegree n trace (n - 2) 0 == 0 &&
    traceDegree n trace (n - 2) 1 == 0

def permutationIndex (n : Nat) (permutation : BitVec ((n + 1) * n * 4))
    (stage index : Nat) : Degree :=
  BitVec.extractLsb' ((stage * n + index) * 4) 4 permutation

def validPermutationRow (n : Nat) (permutation : BitVec ((n + 1) * n * 4))
    (stage active : Nat) : Bool :=
  (List.range active).all fun i =>
    (permutationIndex n permutation stage i).ult (BitVec.ofNat 4 active) &&
      (List.range i).all fun j =>
        permutationIndex n permutation stage i != permutationIndex n permutation stage j

def selectPackedDegree (n : Nat) (ds : BitVec (n * 4))
    (active : Nat) (index : Degree) : Degree :=
  (List.range active).foldl (fun selected i =>
    selectBitVec (index == BitVec.ofNat 4 i) (packedDegree n ds i) selected) 0

def selectRawHavelDegree (n : Nat) (trace : BitVec ((n + 1) * n * 4))
    (stage active : Nat) (index : Degree) : Degree :=
  (List.range (active - 1)).foldl (fun selected i =>
    selectBitVec (index == BitVec.ofNat 4 i) (rawHavelDegree n trace stage i) selected) 0

def validInitialPermutation (n : Nat) (ds : BitVec (n * 4))
    (trace permutation : BitVec ((n + 1) * n * 4)) : Bool :=
  validPermutationRow n permutation 0 n &&
    (List.range n).all fun i =>
      traceDegree n trace 0 i ==
        selectPackedDegree n ds n (permutationIndex n permutation 0 i)

def validPermutedHavelTransition (n : Nat)
    (trace permutation : BitVec ((n + 1) * n * 4))
    (stage active : Nat) : Bool :=
  traceDegree n trace stage 0 != 0 &&
    traceRowSorted n trace (stage + 1) (active - 1) &&
    validPermutationRow n permutation (stage + 1) (active - 1) &&
    (List.range (active - 1)).all fun i =>
      traceDegree n trace (stage + 1) i ==
        selectRawHavelDegree n trace stage active
          (permutationIndex n permutation (stage + 1) i)

def validResidueTwoPermutationTrace (n : Nat) (ds : BitVec (n * 4))
    (trace permutation : BitVec ((n + 1) * n * 4)) : Bool :=
  validInitialPermutation n ds trace permutation && traceRowSorted n trace 0 n &&
    (List.range (n - 2)).all (fun stage =>
      validPermutedHavelTransition n trace permutation stage (n - stage)) &&
    traceDegree n trace (n - 2) 0 == 0 &&
    traceDegree n trace (n - 2) 1 == 0

structure BoolFour where
  b0 : Bool
  b1 : Bool
  b2 : Bool
  b3 : Bool

def BoolFour.ofNat (x : Nat) : BoolFour :=
  { b0 := natBit x 0, b1 := natBit x 1, b2 := natBit x 2, b3 := natBit x 3 }

def BoolFour.same (x y : BoolFour) : Bool :=
  !(x.b0 ^^ y.b0) && !(x.b1 ^^ y.b1) && !(x.b2 ^^ y.b2) && !(x.b3 ^^ y.b3)

def BoolFour.lt (x y : BoolFour) : Bool :=
  (!x.b3 && y.b3) || (!(x.b3 ^^ y.b3) &&
    ((!x.b2 && y.b2) || (!(x.b2 ^^ y.b2) &&
      ((!x.b1 && y.b1) || (!(x.b1 ^^ y.b1) && (!x.b0 && y.b0))))))

def BoolFour.le (x y : BoolFour) : Bool := x.same y || x.lt y

def BoolFour.decrement (x : BoolFour) : BoolFour :=
  let borrow1 := !x.b0
  let borrow2 := !x.b1 && borrow1
  let borrow3 := !x.b2 && borrow2
  { b0 := !x.b0, b1 := x.b1 ^^ borrow1,
    b2 := x.b2 ^^ borrow2, b3 := x.b3 ^^ borrow3 }

def BoolFour.choose (c : Bool) (x y : BoolFour) : BoolFour :=
  { b0 := (c && x.b0) || (!c && y.b0),
    b1 := (c && x.b1) || (!c && y.b1),
    b2 := (c && x.b2) || (!c && y.b2),
    b3 := (c && x.b3) || (!c && y.b3) }

def BoolFour.decrementSat (x : BoolFour) : BoolFour :=
  let nonzero := !x.same (.ofNat 0)
  .choose nonzero x.decrement (.ofNat 0)

def BoolFour.maximum (x y : BoolFour) : BoolFour := .choose (y.le x) x y

def BoolFour.minimum (x y : BoolFour) : BoolFour := .choose (y.le x) y x

def insertFourDesc (x : BoolFour) : List BoolFour → List BoolFour
  | [] => [x]
  | y :: ys => x.maximum y :: insertFourDesc (x.minimum y) ys

def sortFourDesc (xs : List BoolFour) : List BoolFour := xs.foldr insertFourDesc []

def decrementFirstFour (d : BoolFour) : Nat → List BoolFour → List BoolFour
  | _, [] => []
  | i, x :: xs =>
      BoolFour.choose ((BoolFour.ofNat i).lt d) x.decrementSat x ::
        decrementFirstFour d (i + 1) xs

def havelStepFour : List BoolFour → List BoolFour
  | [] => []
  | d :: rest => sortFourDesc (decrementFirstFour d 0 rest)

def residueEqTwoFour : Nat → List BoolFour → Bool
  | 0, _ => false
  | _ + 1, [] => false
  | fuel + 1, d :: rest =>
      let zero := d.same (.ofNat 0)
      (zero && decide (rest.length = 1)) ||
        (!zero && residueEqTwoFour fuel (havelStepFour (d :: rest)))

def fourBits {w : Nat} (x : BitVec w) (start : Nat) : BoolFour :=
  { b0 := x.getLsbD start, b1 := x.getLsbD (start + 1),
    b2 := x.getLsbD (start + 2), b3 := x.getLsbD (start + 3) }

def packedBits (n : Nat) (xs : BitVec (n * 4)) (index : Nat) : BoolFour :=
  fourBits xs (index * 4)

def traceBits (n : Nat) (trace : BitVec ((n + 1) * n * 4))
    (stage index : Nat) : BoolFour :=
  fourBits trace ((stage * n + index) * 4)

def permutationBits (n : Nat) (permutation : BitVec ((n + 1) * n * 4))
    (stage index : Nat) : BoolFour :=
  fourBits permutation ((stage * n + index) * 4)

def BoolFour.increment (x : BoolFour) (b : Bool) : BoolFour :=
  let c1 := x.b0 && b
  let c2 := x.b1 && c1
  let c3 := x.b2 && c2
  { b0 := x.b0 ^^ b, b1 := x.b1 ^^ c1, b2 := x.b2 ^^ c2, b3 := x.b3 ^^ c3 }

def degreeBits {n : Nat} (g : BitVec (n * n)) (u : Nat) : BoolFour :=
  (List.range n).foldl (fun bits v => bits.increment (adj g u v))
    { b0 := false, b1 := false, b2 := false, b3 := false }

def graphResidueEqTwoPure {n : Nat} (g : BitVec (n * n)) : Bool :=
  residueEqTwoFour (n + 1) (sortFourDesc ((List.range n).map fun u => degreeBits g u))

def matchesDegreesFrom {n : Nat} (g : BitVec (n * n)) : Nat → List Nat → Bool
  | _, [] => true
  | i, d :: ds =>
      (degreeBits g i).same (.ofNat d) && matchesDegreesFrom g (i + 1) ds

def fixedDegreeSequence {n : Nat} (g : BitVec (n * n)) (ds : List Nat) : Bool :=
  decide (ds.length = n) && matchesDegreesFrom g 0 ds

def degreesMatchBits {n : Nat} (g : BitVec (n * n)) (ds : BitVec (n * 4)) : Bool :=
  (List.range n).all fun u =>
    (packedBits n ds u).same (degreeBits g u)

def validPermutationRowPure (n : Nat)
    (permutation : BitVec ((n + 1) * n * 4)) (stage active : Nat) : Bool :=
  (List.range active).all fun i =>
    (permutationBits n permutation stage i).lt (.ofNat active) &&
      (List.range i).all fun j =>
        !(permutationBits n permutation stage i).same
          (permutationBits n permutation stage j)

def traceRowSortedPure (n : Nat) (trace : BitVec ((n + 1) * n * 4))
    (stage active : Nat) : Bool :=
  (List.range (active - 1)).all fun i =>
    (traceBits n trace stage (i + 1)).le (traceBits n trace stage i)

def validInitialPermutationPure (n : Nat) (ds : BitVec (n * 4))
    (trace permutation : BitVec ((n + 1) * n * 4)) : Bool :=
  validPermutationRowPure n permutation 0 n &&
    (List.range n).all fun i =>
      (List.range n).all fun j =>
        !(permutationBits n permutation 0 i).same (.ofNat j) ||
          (traceBits n trace 0 i).same (packedBits n ds j)

def validPermutedHavelTransitionPure (n : Nat)
    (trace permutation : BitVec ((n + 1) * n * 4))
    (stage active : Nat) : Bool :=
  !(traceBits n trace stage 0).same (.ofNat 0) &&
    traceRowSortedPure n trace (stage + 1) (active - 1) &&
    validPermutationRowPure n permutation (stage + 1) (active - 1) &&
    (List.range (active - 1)).all fun i =>
      (List.range (active - 1)).all fun j =>
        let chosen := (permutationBits n permutation (stage + 1) i).same (.ofNat j)
        let decrement := (BoolFour.ofNat j).lt (traceBits n trace stage 0)
        let next := traceBits n trace (stage + 1) i
        let previous := traceBits n trace stage (j + 1)
        !chosen || ((!decrement || next.same previous.decrement) &&
          (decrement || next.same previous))

def validResidueTwoTracePure (n : Nat) (ds : BitVec (n * 4))
    (trace permutation : BitVec ((n + 1) * n * 4)) : Bool :=
  validInitialPermutationPure n ds trace permutation && traceRowSortedPure n trace 0 n &&
    (List.range (n - 2)).all (fun stage =>
      validPermutedHavelTransitionPure n trace permutation stage (n - stage)) &&
    (traceBits n trace (n - 2) 0).same (.ofNat 0) &&
    (traceBits n trace (n - 2) 1).same (.ofNat 0)

def validPackedPermutation (n : Nat) (xs : BitVec (n * 4)) : Bool :=
  (List.range n).all fun i =>
    (packedBits n xs i).lt (.ofNat n) &&
      (List.range i).all fun j => !(packedBits n xs i).same (packedBits n xs j)

def connectedCertificate {n : Nat} (g : BitVec (n * n)) (ranks : BitVec (n * 4)) : Bool :=
  validPackedPermutation n ranks &&
    (List.range n).all fun v =>
      (packedBits n ranks v).same (.ofNat 0) || (List.range n).any fun u =>
        adj g v u && (packedBits n ranks u).lt (packedBits n ranks v)

def connectedCertificateRooted {n : Nat} (g : BitVec (n * n))
    (ranks : BitVec (n * 4)) : Bool :=
  validPackedPermutation n ranks && (packedBits n ranks 0).same (.ofNat 0) &&
    (List.range n).all fun v =>
      decide (v = 0) || (List.range n).any fun u =>
        adj g v u && (packedBits n ranks u).lt (packedBits n ranks v)

/-- Vertices reachable from vertex `0`, computed by `n` rounds of edge relaxation. -/
def reachableFromZero {n : Nat} (g : BitVec (n * n)) : BitVec n :=
  (List.range n).foldl (fun seen _ =>
    (List.range n).foldl (fun next v =>
      let discovered := (List.range n).any fun u =>
        seen.getLsbD u && adj g u v
      setBit next v discovered) seen) (BitVec.twoPow n 0)

/-- Functional connectivity check for a symmetric graph. -/
def connectedFromZero {n : Nat} (g : BitVec (n * n)) : Bool :=
  let seen := reachableFromZero g
  (List.range n).all fun v => seen.getLsbD v

def validInitialDegreesPure {n : Nat} (g : BitVec (n * n))
    (trace : BitVec ((n + 1) * n * 4)) : Bool :=
  (List.range n).all fun i => (traceBits n trace 0 i).same (degreeBits g i)

def validResidueTwoTraceSortedGraph {n : Nat} (g : BitVec (n * n))
    (trace permutation : BitVec ((n + 1) * n * 4)) : Bool :=
  validInitialDegreesPure g trace && traceRowSortedPure n trace 0 n &&
    (List.range (n - 2)).all (fun stage =>
      validPermutedHavelTransitionPure n trace permutation stage (n - stage)) &&
    (traceBits n trace (n - 2) 0).same (.ofNat 0) &&
    (traceBits n trace (n - 2) 1).same (.ofNat 0)

def hamiltonianBit {n : Nat} (table : BitVec ((2 ^ n) * n))
    (mask vertex : Nat) : Bool :=
  table.getLsbD (mask * n + vertex)

def validHamiltonianTable {n : Nat} (g : BitVec (n * n))
    (table : BitVec ((2 ^ n) * n)) : Bool :=
  (List.range (2 ^ n)).all fun mask =>
    (List.range n).all fun v =>
      let present := natBit mask v
      let singleton := mask == 2 ^ v
      let previous := mask - 2 ^ v
      let extendable := (List.range n).any fun u =>
        natBit previous u && hamiltonianBit table previous u && adj g u v
      hamiltonianBit table mask v == (present && (singleton || extendable))

def certifiesNoHamiltonianPath {n : Nat} (g : BitVec (n * n))
    (table : BitVec ((2 ^ n) * n)) : Bool :=
  validHamiltonianTable g table &&
    (List.range n).all fun v => !hamiltonianBit table ((2 ^ n) - 1) v

/-- A compact, one-sided certificate of nontraceability.

Singleton paths must be marked reachable, and every marked path endpoint must remain marked after
every legal one-vertex extension.  Thus a Hamiltonian path would force a marked full-set state,
contradicting the final clause.  Unlike `validHamiltonianTable`, unreachable states need not be
defined exactly, which gives the SAT solver a substantially smaller Horn-style obligation. -/
def certifiesNoHamiltonianPathClosure {n : Nat} (g : BitVec (n * n))
    (table : BitVec ((2 ^ n) * n)) : Bool :=
  (List.range n).all (fun v => hamiltonianBit table (2 ^ v) v) &&
    (List.range (2 ^ n)).all (fun mask =>
      (List.range n).all (fun u =>
        (List.range n).all (fun v =>
          !hamiltonianBit table mask u || natBit mask v || !adj g u v ||
            hamiltonianBit table (mask + 2 ^ v) v))) &&
    (List.range n).all fun v => !hamiltonianBit table ((2 ^ n) - 1) v

def packedMaxDegreeAtMostSix (n : Nat) (ds : BitVec (n * 4)) : Bool :=
  (List.range n).all fun v => (packedBits n ds v).le (.ofNat 6)

example : residueEqTwo (n := 3) (BitVec.ofNat 9 170) := by
  native_decide

example : ∀ g : BitVec (3 * 3),
    simpleSymmetric g && connected g → hasHamiltonianPath g := by
  simp only [simpleSymmetric, connected, reachability, hasHamiltonianPath,
    hamiltonianTable, adj, setBit, bitMask, natBit, List.range, List.range.loop, List.foldl,
    List.all, List.any]
  bv_decide

/- The n = 4 and n = 5 certificates were checked successfully before isolating n = 6.
/- The relational n = 6 certificate passed with `lean -s 65536`.
/- The symmetry-reduced relational n = 6 certificate passed.
set_option maxRecDepth 100000 in
example : ∀ a b : Degree,
    a.ule 1 && b.ule 1 → (residueDegrees 2 [a, b]).ule 2 := by
  simp only [residueDegrees, sortDegreesDesc, insertDegreeDesc, decrementFirst,
    List.foldr, List.length]
  bv_decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
example : ∀ (g : BitVec 16) (ds : BitVec 16)
    (trace permutation : BitVec 80)
    (ranks : BitVec 16) (ham : BitVec 64),
    (simpleSymmetric (n := 4) g && connectedCertificate (n := 4) g ranks &&
      degreesMatchBits (n := 4) g ds &&
      validResidueTwoTracePure 4 ds trace permutation &&
      certifiesNoHamiltonianPath (n := 4) g ham) = false := by
  simp only [simpleSymmetric, connectedCertificate, validPackedPermutation,
    degreesMatchBits, degreeBits, BoolFour.increment, BoolFour.decrement,
    BoolFour.same, BoolFour.lt, BoolFour.le, BoolFour.ofNat,
    packedBits, traceBits, permutationBits, fourBits,
    validResidueTwoTracePure, validInitialPermutationPure,
    validPermutedHavelTransitionPure, validPermutationRowPure,
    traceRowSortedPure, certifiesNoHamiltonianPath,
    validHamiltonianTable, hamiltonianBit, adj, natBit,
    List.range, List.range.loop, List.foldl, List.all, List.any]
  bv_decide (maxSteps := 10000000) (timeout := 60)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
example : ∀ (g : BitVec 25) (ds : BitVec 20)
    (trace permutation : BitVec 120)
    (ranks : BitVec 20) (ham : BitVec 160),
    (simpleSymmetric (n := 5) g && connectedCertificate (n := 5) g ranks &&
      degreesMatchBits (n := 5) g ds &&
      validResidueTwoTracePure 5 ds trace permutation &&
      certifiesNoHamiltonianPath (n := 5) g ham) = false := by
  simp only [simpleSymmetric, connectedCertificate, validPackedPermutation,
    degreesMatchBits, degreeBits, BoolFour.increment, BoolFour.decrement,
    BoolFour.same, BoolFour.lt, BoolFour.le, BoolFour.ofNat,
    packedBits, traceBits, permutationBits, fourBits,
    validResidueTwoTracePure, validInitialPermutationPure,
    validPermutedHavelTransitionPure, validPermutationRowPure,
    traceRowSortedPure, certifiesNoHamiltonianPath,
    validHamiltonianTable, hamiltonianBit, adj, natBit,
    List.range, List.range.loop, List.foldl, List.all, List.any]
  bv_decide (maxSteps := 20000000) (timeout := 120)
-/

set_option maxRecDepth 100000 in
set_option maxHeartbeats 30000000 in
example : ∀ (g : BitVec 36) (ds : BitVec 24)
    (trace permutation : BitVec 168)
    (ranks : BitVec 24) (ham : BitVec 384),
    (simpleSymmetric (n := 6) g && connectedCertificate (n := 6) g ranks &&
      degreesMatchBits (n := 6) g ds &&
      validResidueTwoTracePure 6 ds trace permutation &&
      certifiesNoHamiltonianPath (n := 6) g ham) = false := by
  simp (config := { maxSteps := 50000000 }) only
    [simpleSymmetric, connectedCertificate, validPackedPermutation,
    degreesMatchBits, degreeBits, BoolFour.increment, BoolFour.decrement,
    BoolFour.same, BoolFour.lt, BoolFour.le, BoolFour.ofNat,
    packedBits, traceBits, permutationBits, fourBits,
    validResidueTwoTracePure, validInitialPermutationPure,
    validPermutedHavelTransitionPure, validPermutationRowPure,
    traceRowSortedPure, certifiesNoHamiltonianPath,
    validHamiltonianTable, hamiltonianBit, adj, natBit,
    List.range, List.range.loop, List.foldl, List.all, List.any]
  bv_decide (maxSteps := 40000000) (timeout := 300)
-/

/- The direct sorting-network experiment is sound but slower than relational certificates.
example : graphResidueEqTwoPure (n := 3) (BitVec.ofNat 9 170) := by
  native_decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
example : ∀ (g : BitVec 16) (ranks : BitVec 16) (ham : BitVec 64),
    (simpleSymmetric (n := 4) g && connectedCertificate (n := 4) g ranks &&
      graphResidueEqTwoPure (n := 4) g &&
      certifiesNoHamiltonianPath (n := 4) g ham) = false := by
  simp (config := { maxSteps := 10000000 }) only
    [simpleSymmetric, connectedCertificate, validPackedPermutation,
    graphResidueEqTwoPure, residueEqTwoFour, havelStepFour,
    decrementFirstFour, sortFourDesc, insertFourDesc,
    degreeBits, BoolFour.increment, BoolFour.decrement, BoolFour.decrementSat,
    BoolFour.choose, BoolFour.maximum, BoolFour.minimum,
    BoolFour.same, BoolFour.lt, BoolFour.le, BoolFour.ofNat,
    packedBits, fourBits, certifiesNoHamiltonianPath,
    validHamiltonianTable, hamiltonianBit, adj, natBit,
    List.range, List.range.loop, List.map, List.foldr, List.foldl,
    List.length, List.all, List.any]
  bv_decide (maxSteps := 20000000) (timeout := 60)
-/

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
example : ∀ (g : BitVec 36) (trace permutation : BitVec 168)
    (ranks : BitVec 24) (ham : BitVec 384),
    (simpleSymmetric (n := 6) g && connectedCertificateRooted (n := 6) g ranks &&
      validResidueTwoTraceSortedGraph (n := 6) g trace permutation &&
      certifiesNoHamiltonianPath (n := 6) g ham) = false := by
  simp (config := { maxSteps := 50000000 }) only
    [simpleSymmetric, connectedCertificateRooted, validPackedPermutation,
    validResidueTwoTraceSortedGraph, validInitialDegreesPure,
    validPermutedHavelTransitionPure, validPermutationRowPure,
    traceRowSortedPure, degreeBits, BoolFour.increment, BoolFour.decrement,
    BoolFour.same, BoolFour.lt, BoolFour.le, BoolFour.ofNat,
    packedBits, traceBits, permutationBits, fourBits,
    certifiesNoHamiltonianPath, validHamiltonianTable, hamiltonianBit,
    adj, natBit, List.range, List.range.loop, List.foldl,
    List.all, List.any]
  bv_decide (maxSteps := 50000000) (timeout := 300)
-/

structure BoolOrdering where
  less : Bool
  equal : Bool

/-- Numeric comparison of an adjacency matrix with the matrix obtained by relabelling its
vertices according to `permutation`.  Bits are visited from most to least significant. -/
def matrixULEUnderPermutation {n : Nat} (g : BitVec (n * n))
    (permutation : List Nat) : Bool :=
  let result : BoolOrdering := (List.range (n * n)).foldl (fun (state : BoolOrdering) offset =>
    let index := n * n - 1 - offset
    let u := index / n
    let v := index % n
    let pu := permutation.getD u u
    let pv := permutation.getD v v
    let lhs := adj g u v
    let rhs := adj g pu pv
    { less := state.less || (state.equal && !lhs && rhs),
      equal := state.equal && !(lhs ^^ rhs) })
    ({ less := false, equal := true } : BoolOrdering)
  result.less || result.equal

def shiftedRange (start count : Nat) : List Nat :=
  (List.range count).map (start + ·)

/-- All permutations that preserve two consecutive degree blocks. -/
def degreeBlockPermutations (first second : Nat) : List (List Nat) :=
  (List.range first).permutations.flatMap fun p =>
    (shiftedRange first second).permutations.map fun q => p ++ q

/-- Canonical representative: the packed adjacency matrix is minimal under every relabelling
that preserves the two degree blocks.  Every orbit has such a representative. -/
def canonicalUnderDegreeBlocks {n : Nat} (g : BitVec (n * n))
    (first second : Nat) : Bool :=
  (degreeBlockPermutations first second).all fun permutation =>
    matrixULEUnderPermutation g permutation

def canonicalUnderPermutations {n : Nat} (g : BitVec (n * n))
    (permutations : List (List Nat)) : Bool :=
  permutations.all fun permutation => matrixULEUnderPermutation g permutation

def degreePermutations52 : List (List Nat) :=
  [[0,1,2,3,4,5,6],[0,1,2,3,4,6,5],[0,1,2,4,3,5,6],[0,1,2,4,3,6,5],[0,1,3,2,4,5,6],[0,1,3,2,4,6,5],[0,1,3,4,2,5,6],[0,1,3,4,2,6,5],[0,1,4,2,3,5,6],[0,1,4,2,3,6,5],[0,1,4,3,2,5,6],[0,1,4,3,2,6,5],[0,2,1,3,4,5,6],[0,2,1,3,4,6,5],[0,2,1,4,3,5,6],[0,2,1,4,3,6,5],[0,2,3,1,4,5,6],[0,2,3,1,4,6,5],[0,2,3,4,1,5,6],[0,2,3,4,1,6,5],[0,2,4,1,3,5,6],[0,2,4,1,3,6,5],[0,2,4,3,1,5,6],[0,2,4,3,1,6,5],[0,3,1,2,4,5,6],[0,3,1,2,4,6,5],[0,3,1,4,2,5,6],[0,3,1,4,2,6,5],[0,3,2,1,4,5,6],[0,3,2,1,4,6,5],[0,3,2,4,1,5,6],[0,3,2,4,1,6,5],[0,3,4,1,2,5,6],[0,3,4,1,2,6,5],[0,3,4,2,1,5,6],[0,3,4,2,1,6,5],[0,4,1,2,3,5,6],[0,4,1,2,3,6,5],[0,4,1,3,2,5,6],[0,4,1,3,2,6,5],[0,4,2,1,3,5,6],[0,4,2,1,3,6,5],[0,4,2,3,1,5,6],[0,4,2,3,1,6,5],[0,4,3,1,2,5,6],[0,4,3,1,2,6,5],[0,4,3,2,1,5,6],[0,4,3,2,1,6,5],[1,0,2,3,4,5,6],[1,0,2,3,4,6,5],[1,0,2,4,3,5,6],[1,0,2,4,3,6,5],[1,0,3,2,4,5,6],[1,0,3,2,4,6,5],[1,0,3,4,2,5,6],[1,0,3,4,2,6,5],[1,0,4,2,3,5,6],[1,0,4,2,3,6,5],[1,0,4,3,2,5,6],[1,0,4,3,2,6,5],[1,2,0,3,4,5,6],[1,2,0,3,4,6,5],[1,2,0,4,3,5,6],[1,2,0,4,3,6,5],[1,2,3,0,4,5,6],[1,2,3,0,4,6,5],[1,2,3,4,0,5,6],[1,2,3,4,0,6,5],[1,2,4,0,3,5,6],[1,2,4,0,3,6,5],[1,2,4,3,0,5,6],[1,2,4,3,0,6,5],[1,3,0,2,4,5,6],[1,3,0,2,4,6,5],[1,3,0,4,2,5,6],[1,3,0,4,2,6,5],[1,3,2,0,4,5,6],[1,3,2,0,4,6,5],[1,3,2,4,0,5,6],[1,3,2,4,0,6,5],[1,3,4,0,2,5,6],[1,3,4,0,2,6,5],[1,3,4,2,0,5,6],[1,3,4,2,0,6,5],[1,4,0,2,3,5,6],[1,4,0,2,3,6,5],[1,4,0,3,2,5,6],[1,4,0,3,2,6,5],[1,4,2,0,3,5,6],[1,4,2,0,3,6,5],[1,4,2,3,0,5,6],[1,4,2,3,0,6,5],[1,4,3,0,2,5,6],[1,4,3,0,2,6,5],[1,4,3,2,0,5,6],[1,4,3,2,0,6,5],[2,0,1,3,4,5,6],[2,0,1,3,4,6,5],[2,0,1,4,3,5,6],[2,0,1,4,3,6,5],[2,0,3,1,4,5,6],[2,0,3,1,4,6,5],[2,0,3,4,1,5,6],[2,0,3,4,1,6,5],[2,0,4,1,3,5,6],[2,0,4,1,3,6,5],[2,0,4,3,1,5,6],[2,0,4,3,1,6,5],[2,1,0,3,4,5,6],[2,1,0,3,4,6,5],[2,1,0,4,3,5,6],[2,1,0,4,3,6,5],[2,1,3,0,4,5,6],[2,1,3,0,4,6,5],[2,1,3,4,0,5,6],[2,1,3,4,0,6,5],[2,1,4,0,3,5,6],[2,1,4,0,3,6,5],[2,1,4,3,0,5,6],[2,1,4,3,0,6,5],[2,3,0,1,4,5,6],[2,3,0,1,4,6,5],[2,3,0,4,1,5,6],[2,3,0,4,1,6,5],[2,3,1,0,4,5,6],[2,3,1,0,4,6,5],[2,3,1,4,0,5,6],[2,3,1,4,0,6,5],[2,3,4,0,1,5,6],[2,3,4,0,1,6,5],[2,3,4,1,0,5,6],[2,3,4,1,0,6,5],[2,4,0,1,3,5,6],[2,4,0,1,3,6,5],[2,4,0,3,1,5,6],[2,4,0,3,1,6,5],[2,4,1,0,3,5,6],[2,4,1,0,3,6,5],[2,4,1,3,0,5,6],[2,4,1,3,0,6,5],[2,4,3,0,1,5,6],[2,4,3,0,1,6,5],[2,4,3,1,0,5,6],[2,4,3,1,0,6,5],[3,0,1,2,4,5,6],[3,0,1,2,4,6,5],[3,0,1,4,2,5,6],[3,0,1,4,2,6,5],[3,0,2,1,4,5,6],[3,0,2,1,4,6,5],[3,0,2,4,1,5,6],[3,0,2,4,1,6,5],[3,0,4,1,2,5,6],[3,0,4,1,2,6,5],[3,0,4,2,1,5,6],[3,0,4,2,1,6,5],[3,1,0,2,4,5,6],[3,1,0,2,4,6,5],[3,1,0,4,2,5,6],[3,1,0,4,2,6,5],[3,1,2,0,4,5,6],[3,1,2,0,4,6,5],[3,1,2,4,0,5,6],[3,1,2,4,0,6,5],[3,1,4,0,2,5,6],[3,1,4,0,2,6,5],[3,1,4,2,0,5,6],[3,1,4,2,0,6,5],[3,2,0,1,4,5,6],[3,2,0,1,4,6,5],[3,2,0,4,1,5,6],[3,2,0,4,1,6,5],[3,2,1,0,4,5,6],[3,2,1,0,4,6,5],[3,2,1,4,0,5,6],[3,2,1,4,0,6,5],[3,2,4,0,1,5,6],[3,2,4,0,1,6,5],[3,2,4,1,0,5,6],[3,2,4,1,0,6,5],[3,4,0,1,2,5,6],[3,4,0,1,2,6,5],[3,4,0,2,1,5,6],[3,4,0,2,1,6,5],[3,4,1,0,2,5,6],[3,4,1,0,2,6,5],[3,4,1,2,0,5,6],[3,4,1,2,0,6,5],[3,4,2,0,1,5,6],[3,4,2,0,1,6,5],[3,4,2,1,0,5,6],[3,4,2,1,0,6,5],[4,0,1,2,3,5,6],[4,0,1,2,3,6,5],[4,0,1,3,2,5,6],[4,0,1,3,2,6,5],[4,0,2,1,3,5,6],[4,0,2,1,3,6,5],[4,0,2,3,1,5,6],[4,0,2,3,1,6,5],[4,0,3,1,2,5,6],[4,0,3,1,2,6,5],[4,0,3,2,1,5,6],[4,0,3,2,1,6,5],[4,1,0,2,3,5,6],[4,1,0,2,3,6,5],[4,1,0,3,2,5,6],[4,1,0,3,2,6,5],[4,1,2,0,3,5,6],[4,1,2,0,3,6,5],[4,1,2,3,0,5,6],[4,1,2,3,0,6,5],[4,1,3,0,2,5,6],[4,1,3,0,2,6,5],[4,1,3,2,0,5,6],[4,1,3,2,0,6,5],[4,2,0,1,3,5,6],[4,2,0,1,3,6,5],[4,2,0,3,1,5,6],[4,2,0,3,1,6,5],[4,2,1,0,3,5,6],[4,2,1,0,3,6,5],[4,2,1,3,0,5,6],[4,2,1,3,0,6,5],[4,2,3,0,1,5,6],[4,2,3,0,1,6,5],[4,2,3,1,0,5,6],[4,2,3,1,0,6,5],[4,3,0,1,2,5,6],[4,3,0,1,2,6,5],[4,3,0,2,1,5,6],[4,3,0,2,1,6,5],[4,3,1,0,2,5,6],[4,3,1,0,2,6,5],[4,3,1,2,0,5,6],[4,3,1,2,0,6,5],[4,3,2,0,1,5,6],[4,3,2,0,1,6,5],[4,3,2,1,0,5,6],[4,3,2,1,0,6,5]]

def degreePermutations43 : List (List Nat) :=
  [[0,1,2,3,4,5,6],[0,1,2,3,4,6,5],[0,1,2,3,5,4,6],[0,1,2,3,5,6,4],[0,1,2,3,6,4,5],[0,1,2,3,6,5,4],[0,1,3,2,4,5,6],[0,1,3,2,4,6,5],[0,1,3,2,5,4,6],[0,1,3,2,5,6,4],[0,1,3,2,6,4,5],[0,1,3,2,6,5,4],[0,2,1,3,4,5,6],[0,2,1,3,4,6,5],[0,2,1,3,5,4,6],[0,2,1,3,5,6,4],[0,2,1,3,6,4,5],[0,2,1,3,6,5,4],[0,2,3,1,4,5,6],[0,2,3,1,4,6,5],[0,2,3,1,5,4,6],[0,2,3,1,5,6,4],[0,2,3,1,6,4,5],[0,2,3,1,6,5,4],[0,3,1,2,4,5,6],[0,3,1,2,4,6,5],[0,3,1,2,5,4,6],[0,3,1,2,5,6,4],[0,3,1,2,6,4,5],[0,3,1,2,6,5,4],[0,3,2,1,4,5,6],[0,3,2,1,4,6,5],[0,3,2,1,5,4,6],[0,3,2,1,5,6,4],[0,3,2,1,6,4,5],[0,3,2,1,6,5,4],[1,0,2,3,4,5,6],[1,0,2,3,4,6,5],[1,0,2,3,5,4,6],[1,0,2,3,5,6,4],[1,0,2,3,6,4,5],[1,0,2,3,6,5,4],[1,0,3,2,4,5,6],[1,0,3,2,4,6,5],[1,0,3,2,5,4,6],[1,0,3,2,5,6,4],[1,0,3,2,6,4,5],[1,0,3,2,6,5,4],[1,2,0,3,4,5,6],[1,2,0,3,4,6,5],[1,2,0,3,5,4,6],[1,2,0,3,5,6,4],[1,2,0,3,6,4,5],[1,2,0,3,6,5,4],[1,2,3,0,4,5,6],[1,2,3,0,4,6,5],[1,2,3,0,5,4,6],[1,2,3,0,5,6,4],[1,2,3,0,6,4,5],[1,2,3,0,6,5,4],[1,3,0,2,4,5,6],[1,3,0,2,4,6,5],[1,3,0,2,5,4,6],[1,3,0,2,5,6,4],[1,3,0,2,6,4,5],[1,3,0,2,6,5,4],[1,3,2,0,4,5,6],[1,3,2,0,4,6,5],[1,3,2,0,5,4,6],[1,3,2,0,5,6,4],[1,3,2,0,6,4,5],[1,3,2,0,6,5,4],[2,0,1,3,4,5,6],[2,0,1,3,4,6,5],[2,0,1,3,5,4,6],[2,0,1,3,5,6,4],[2,0,1,3,6,4,5],[2,0,1,3,6,5,4],[2,0,3,1,4,5,6],[2,0,3,1,4,6,5],[2,0,3,1,5,4,6],[2,0,3,1,5,6,4],[2,0,3,1,6,4,5],[2,0,3,1,6,5,4],[2,1,0,3,4,5,6],[2,1,0,3,4,6,5],[2,1,0,3,5,4,6],[2,1,0,3,5,6,4],[2,1,0,3,6,4,5],[2,1,0,3,6,5,4],[2,1,3,0,4,5,6],[2,1,3,0,4,6,5],[2,1,3,0,5,4,6],[2,1,3,0,5,6,4],[2,1,3,0,6,4,5],[2,1,3,0,6,5,4],[2,3,0,1,4,5,6],[2,3,0,1,4,6,5],[2,3,0,1,5,4,6],[2,3,0,1,5,6,4],[2,3,0,1,6,4,5],[2,3,0,1,6,5,4],[2,3,1,0,4,5,6],[2,3,1,0,4,6,5],[2,3,1,0,5,4,6],[2,3,1,0,5,6,4],[2,3,1,0,6,4,5],[2,3,1,0,6,5,4],[3,0,1,2,4,5,6],[3,0,1,2,4,6,5],[3,0,1,2,5,4,6],[3,0,1,2,5,6,4],[3,0,1,2,6,4,5],[3,0,1,2,6,5,4],[3,0,2,1,4,5,6],[3,0,2,1,4,6,5],[3,0,2,1,5,4,6],[3,0,2,1,5,6,4],[3,0,2,1,6,4,5],[3,0,2,1,6,5,4],[3,1,0,2,4,5,6],[3,1,0,2,4,6,5],[3,1,0,2,5,4,6],[3,1,0,2,5,6,4],[3,1,0,2,6,4,5],[3,1,0,2,6,5,4],[3,1,2,0,4,5,6],[3,1,2,0,4,6,5],[3,1,2,0,5,4,6],[3,1,2,0,5,6,4],[3,1,2,0,6,4,5],[3,1,2,0,6,5,4],[3,2,0,1,4,5,6],[3,2,0,1,4,6,5],[3,2,0,1,5,4,6],[3,2,0,1,5,6,4],[3,2,0,1,6,4,5],[3,2,0,1,6,5,4],[3,2,1,0,4,5,6],[3,2,1,0,4,6,5],[3,2,1,0,5,4,6],[3,2,1,0,5,6,4],[3,2,1,0,6,4,5],[3,2,1,0,6,5,4]]

example :
    (degreeBlockPermutations 5 2).all (fun p => degreePermutations52.contains p) &&
      degreePermutations52.all (fun p => (degreeBlockPermutations 5 2).contains p) := by
  native_decide

example :
    (degreeBlockPermutations 4 3).all (fun p => degreePermutations43.contains p) &&
      degreePermutations43.all (fun p => (degreeBlockPermutations 4 3).contains p) := by
  native_decide

def sameGraphCode {n : Nat} (g : BitVec (n * n)) (code : Nat) : Bool :=
  (List.range (n * n)).all fun i => !(g.getLsbD i ^^ natBit code i)

def oneOfGraphCodes {n : Nat} (g : BitVec (n * n)) (codes : List Nat) : Bool :=
  codes.any fun code => sameGraphCode g code

def edgeCount (n : Nat) : Nat := n * (n - 1) / 2

def upperEdgeIndex (u v : Nat) : Nat :=
  let lo := min u v
  let hi := max u v
  hi * (hi - 1) / 2 + lo

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

def sameEdgeCode {n : Nat} (g : BitVec (edgeCount n)) (code : Nat) : Bool :=
  (List.range (edgeCount n)).all fun i => !(g.getLsbD i ^^ natBit code i)

def oneOfEdgeCodes {n : Nat} (g : BitVec (edgeCount n)) (codes : List Nat) : Bool :=
  codes.any fun code => sameEdgeCode g code

def degreeEdgeCodes5211 : List Nat := [35838,37885,41975,50111,67582,70651,74735,82815,133117,134139,140255,148223,264183,265199,267231,279039,526271,527231,529151,532991]

def degreeEdgeCodes4333222 : List Nat := [102188,102194,103864,104052,104108,104114,104220,104241,104824,105068,105074,105130,105242,105257,107892,107948,107954,108198,108310,108325,108908,108914,108970,109158,109326,109347,110828,110834,110940,110961,111002,111017,111190,111205,111246,111267,111373,111379,116028,116278,117050,117294,118908,118970,119097,119326,119341,119347,122998,123054,123166,123181,123187,123431,167352,167540,167596,167602,167708,167729,169628,169649,170232,170588,170609,170650,170665,170777,173300,173468,173489,173718,173733,173845,174316,174322,174428,174449,174490,174505,174678,174693,174734,174755,174861,174867,176348,176369,176537,176725,176781,176787,181436,181813,182396,182458,182585,182814,182829,182835,184505,184861,188533,188574,188589,188595,188701,188951,200056,200300,200306,200362,200474,200489,201976,202332,202353,202394,202409,202521,203354,203369,206060,206066,206172,206193,206234,206249,206422,206437,206478,206499,206605,206611,207082,207194,207209,207438,207459,207627,209114,209129,209241,209485,209491,209547,214140,214202,214329,214558,214573,214579,215162,215595,217209,217627,221278,221293,221299,221355,221467,221711,298356,298412,298418,298662,298774,298789,300276,300444,300465,300694,300709,300821,301292,301298,301404,301425,301466,301481,301654,301669,301710,301731,301837,301843,304534,304549,305382,305494,305509,305550,305571,305927,307414,307429,307541,307597,307603,307847,312502,312629,313462,313518,313630,313645,313651,313895,315509,315550,315565,315571,315677,315927,319655,319767,331116,331122,331178,331366,331534,331555,333036,333042,333148,333169,333210,333225,333398,333413,333454,333475,333581,333587,334058,334170,334185,334414,334435,334603,337126,337238,337253,337294,337315,337671,338254,338275,340174,340195,340301,340307,340363,340551,345206,345262,345374,345389,345395,345639,346222,346411,348254,348269,348275,348331,348443,348687,352359,352527,396524,396530,396636,396657,396698,396713,396886,396901,396942,396963,397069,397075,398556,398577,398745,398933,398989,398995,399578,399593,399705,399949,399955,400011,402646,402661,402773,402829,402835,403079,403662,403683,403789,403795,403851,404039,405709,405715,410741,410782,410797,410803,410909,411159,411742,411757,411763,411819,411931,412175,413789,413851,417879,417935,560444,560694,562364,562741,563324,563386,563513,563742,563757,563763,566454,566581,567414,567470,567582,567597,567603,567847,569461,569502,569517,569523,569629,569879,575550,577597,581687,593210,593454,595068,595130,595257,595486,595501,595507,596090,596523,599158,599214,599326,599341,599347,599591,600174,600363,602206,602221,602227,602283,602395,602639,607294,610363,614447,658556,658618,658745,658974,658989,658995,660665,661021,661625,662043,664693,664734,664749,664755,664861,665111,665694,665709,665715,665771,665883,666127,667741,667803,672829,673851,679967,789622,789678,789790,789805,789811,790055,791669,791710,791725,791731,791837,792087,792670,792685,792691,792747,792859,793103,795815,795927,796775,796943,798807,798863,803895,804911,806943,1082812,1083062,1083189,1083772,1083834,1084022,1084078,1084190,1084205,1084211,1085692,1085881,1086069,1086110,1086125,1086131,1086237,1089782,1089909,1089950,1089965,1089971,1090215,1090327,1097918,1098045,1098295,1115516,1115578,1115766,1115822,1115934,1115949,1115955,1116538,1116782,1116971,1118458,1118585,1118814,1118829,1118835,1118891,1119003,1122542,1122654,1122669,1122675,1122731,1122919,1123087,1130622,1130811,1131055,1180924,1181113,1181301,1181342,1181357,1181363,1181469,1181946,1182073,1182302,1182317,1182323,1182379,1182491,1183993,1184349,1184411,1188062,1188077,1188083,1188189,1188251,1188439,1188495,1196157,1196219,1196575,1311990,1312117,1312158,1312173,1312179,1312423,1312535,1313006,1313118,1313133,1313139,1313195,1313383,1313551,1315038,1315053,1315059,1315165,1315227,1315415,1315471,1319143,1319255,1319311,1327223,1327279,1327391,1574078,1574205,1574455,1575038,1575227,1575471,1577085,1577147,1577503,1581175,1581231,1581343]

def consecutiveAdjacentUpper {n : Nat} (g : BitVec (edgeCount n)) :
    List Nat → Bool
  | [] => true
  | [_] => true
  | u :: v :: rest => adjUpper g u v && consecutiveAdjacentUpper g (v :: rest)

def validHamiltonianOrderUpper {n : Nat} (g : BitVec (edgeCount n))
    (order : List Nat) : Bool :=
  decide (order.length = n) && decide order.Nodup &&
    order.all (· < n) && consecutiveAdjacentUpper g order

def degreeWitnesses5211 : List (Nat × List Nat) := [(35838, [5,1,2,3,4,0,6]),(37885, [5,2,1,3,4,0,6]),(41975, [5,3,1,2,4,0,6]),(50111, [5,4,1,2,3,0,6]),(67582, [5,0,2,3,4,1,6]),(70651, [5,2,0,3,4,1,6]),(74735, [5,3,0,2,4,1,6]),(82815, [5,4,0,2,3,1,6]),(133117, [5,0,1,3,4,2,6]),(134139, [5,1,0,3,4,2,6]),(140255, [5,3,0,1,4,2,6]),(148223, [5,4,0,1,3,2,6]),(264183, [5,0,1,2,4,3,6]),(265199, [5,1,0,2,4,3,6]),(267231, [5,2,0,1,4,3,6]),(279039, [5,4,0,1,2,3,6]),(526271, [5,0,1,2,3,4,6]),(527231, [5,1,0,2,3,4,6]),(529151, [5,2,0,1,3,4,6]),(532991, [5,3,0,1,2,4,6])]

def degreeWitnesses4333222 : List (Nat × List Nat) := [(102188, [2,4,3,0,5,1,6]),(102194, [2,4,3,1,5,0,6]),(103864, [3,0,5,2,4,1,6]),(104052, [1,6,0,4,3,2,5]),(104108, [0,5,2,3,4,1,6]),(104114, [0,5,2,3,4,1,6]),(104220, [0,5,2,4,3,1,6]),(104241, [0,5,2,4,3,1,6]),(104824, [3,0,4,2,5,1,6]),(105068, [0,4,3,2,5,1,6]),(105074, [0,4,3,2,5,1,6]),(105130, [0,6,1,4,3,2,5]),(105242, [0,3,4,2,5,1,6]),(105257, [0,3,4,2,5,1,6]),(107892, [1,6,0,4,2,3,5]),(107948, [0,5,3,2,4,1,6]),(107954, [0,5,3,2,4,1,6]),(108198, [2,0,5,3,4,1,6]),(108310, [0,5,3,4,2,1,6]),(108325, [0,5,3,4,2,1,6]),(108908, [0,4,2,3,5,1,6]),(108914, [0,4,2,3,5,1,6]),(108970, [0,6,1,4,2,3,5]),(109158, [2,0,4,3,5,1,6]),(109326, [0,2,4,3,5,1,6]),(109347, [0,2,4,3,5,1,6]),(110828, [2,5,3,0,4,1,6]),(110834, [2,5,3,1,4,0,6]),(110940, [0,4,2,5,3,1,6]),(110961, [0,4,2,5,3,1,6]),(111002, [0,3,5,2,4,1,6]),(111017, [0,3,5,2,4,1,6]),(111190, [0,4,3,5,2,1,6]),(111205, [0,4,3,5,2,1,6]),(111246, [0,2,5,3,4,1,6]),(111267, [0,2,5,3,4,1,6]),(111373, [0,6,1,2,4,3,5]),(111379, [0,6,1,3,4,2,5]),(116028, [0,5,4,2,3,1,6]),(116278, [0,5,4,3,2,1,6]),(117050, [0,3,2,4,5,1,6]),(117294, [0,2,3,4,5,1,6]),(118908, [0,4,5,2,3,1,6]),(118970, [0,3,2,5,4,1,6]),(119097, [0,6,1,3,2,4,5]),(119326, [0,2,5,4,3,1,6]),(119341, [0,3,4,5,2,1,6]),(119347, [0,2,5,4,3,1,6]),(122998, [0,4,5,3,2,1,6]),(123054, [0,2,3,5,4,1,6]),(123166, [0,2,4,5,3,1,6]),(123181, [0,3,5,4,2,1,6]),(123187, [0,2,4,5,3,1,6]),(123431, [0,6,1,2,3,4,5]),(167352, [3,0,5,1,4,2,6]),(167540, [1,5,0,4,3,2,6]),(167596, [0,5,1,4,3,2,6]),(167602, [0,5,1,4,3,2,6]),(167708, [0,5,1,3,4,2,6]),(167729, [0,5,1,3,4,2,6]),(169628, [1,4,3,0,5,2,6]),(169649, [1,4,3,2,5,0,6]),(170232, [3,0,4,1,5,2,6]),(170588, [0,4,3,1,5,2,6]),(170609, [0,4,3,1,5,2,6]),(170650, [0,3,4,1,5,2,6]),(170665, [0,3,4,1,5,2,6]),(170777, [0,6,2,4,3,1,5]),(173300, [1,4,0,5,3,2,6]),(173468, [0,5,3,1,4,2,6]),(173489, [0,5,3,1,4,2,6]),(173718, [0,5,3,4,1,2,6]),(173733, [0,5,3,4,1,2,6]),(173845, [1,0,5,3,4,2,6]),(174316, [0,4,1,5,3,2,6]),(174322, [0,4,1,5,3,2,6]),(174428, [1,5,3,0,4,2,6]),(174449, [1,5,3,2,4,0,6]),(174490, [0,3,5,1,4,2,6]),(174505, [0,3,5,1,4,2,6]),(174678, [0,4,3,5,1,2,6]),(174693, [0,4,3,5,1,2,6]),(174734, [0,6,2,1,4,3,5]),(174755, [0,6,2,3,4,1,5]),(174861, [0,1,5,3,4,2,6]),(174867, [0,1,5,3,4,2,6]),(176348, [0,4,1,3,5,2,6]),(176369, [0,4,1,3,5,2,6]),(176537, [0,6,2,4,1,3,5]),(176725, [1,0,4,3,5,2,6]),(176781, [0,1,4,3,5,2,6]),(176787, [0,1,4,3,5,2,6]),(181436, [0,5,4,1,3,2,6]),(181813, [0,5,4,3,1,2,6]),(182396, [0,4,5,1,3,2,6]),(182458, [0,6,2,3,1,4,5]),(182585, [0,3,1,5,4,2,6]),(182814, [0,3,4,5,1,2,6]),(182829, [0,1,5,4,3,2,6]),(182835, [0,1,5,4,3,2,6]),(184505, [0,3,1,4,5,2,6]),(184861, [0,1,3,4,5,2,6]),(188533, [0,4,5,3,1,2,6]),(188574, [0,3,5,4,1,2,6]),(188589, [0,1,4,5,3,2,6]),(188595, [0,1,4,5,3,2,6]),(188701, [0,1,3,5,4,2,6]),(188951, [0,6,2,1,3,4,5]),(200056, [3,0,4,2,6,1,5]),(200300, [0,4,3,2,6,1,5]),(200306, [0,4,3,2,6,1,5]),(200362, [0,5,1,4,3,2,6]),(200474, [0,3,4,2,6,1,5]),(200489, [0,3,4,2,6,1,5]),(201976, [3,0,4,1,6,2,5]),(202332, [0,4,3,1,6,2,5]),(202353, [0,4,3,1,6,2,5]),(202394, [0,3,4,1,6,2,5]),(202409, [0,3,4,1,6,2,5]),(202521, [0,5,2,4,3,1,6]),(203354, [0,4,3,1,5,2,6]),(203369, [0,4,3,2,5,1,6]),(206060, [0,4,1,6,2,3,5]),(206066, [0,4,1,6,2,3,5]),(206172, [0,4,2,6,1,3,5]),(206193, [0,4,2,6,1,3,5]),(206234, [0,5,3,1,4,2,6]),(206249, [0,5,3,2,4,1,6]),(206422, [1,6,2,0,4,3,5]),(206437, [1,6,2,3,4,0,5]),(206478, [0,2,6,1,4,3,5]),(206499, [0,2,6,1,4,3,5]),(206605, [0,1,6,2,4,3,5]),(206611, [0,1,6,2,4,3,5]),(207082, [0,4,1,5,3,2,6]),(207194, [0,3,5,1,6,2,4]),(207209, [0,3,5,1,6,2,4]),(207438, [0,2,6,1,5,3,4]),(207459, [0,2,6,1,5,3,4]),(207627, [0,1,5,3,4,2,6]),(209114, [0,3,5,2,6,1,4]),(209129, [0,3,5,2,6,1,4]),(209241, [0,4,2,5,3,1,6]),(209485, [0,1,6,2,5,3,4]),(209491, [0,1,6,2,5,3,4]),(209547, [0,1,4,3,5,2,6]),(214140, [1,6,2,3,0,4,5]),(214202, [0,3,2,6,1,4,5]),(214329, [0,3,1,6,2,4,5]),(214558, [0,2,6,1,3,4,5]),(214573, [0,1,6,2,3,4,5]),(214579, [0,1,6,2,3,4,5]),(215162, [0,3,2,6,1,5,4]),(215595, [0,1,5,4,3,2,6]),(217209, [0,3,1,6,2,5,4]),(217627, [0,1,3,4,5,2,6]),(221278, [0,2,6,1,3,5,4]),(221293, [0,1,6,2,3,5,4]),(221299, [0,1,6,2,3,5,4]),(221355, [0,1,4,5,3,2,6]),(221467, [0,1,3,5,4,2,6]),(221711, [1,6,2,0,3,4,5]),(298356, [1,5,0,4,2,3,6]),(298412, [0,5,1,4,2,3,6]),(298418, [0,5,1,4,2,3,6]),(298662, [2,0,5,1,4,3,6]),(298774, [0,5,1,2,4,3,6]),(298789, [0,5,1,2,4,3,6]),(300276, [1,4,0,5,2,3,6]),(300444, [0,5,2,4,1,3,6]),(300465, [0,5,2,4,1,3,6]),(300694, [0,5,2,1,4,3,6]),(300709, [0,5,2,1,4,3,6]),(300821, [1,0,5,2,4,3,6]),(301292, [0,4,1,5,2,3,6]),(301298, [0,4,1,5,2,3,6]),(301404, [0,4,2,5,1,3,6]),(301425, [0,4,2,5,1,3,6]),(301466, [0,6,3,1,4,2,5]),(301481, [0,6,3,2,4,1,5]),(301654, [1,5,2,0,4,3,6]),(301669, [1,5,2,3,4,0,6]),(301710, [0,2,5,1,4,3,6]),(301731, [0,2,5,1,4,3,6]),(301837, [0,1,5,2,4,3,6]),(301843, [0,1,5,2,4,3,6]),(304534, [1,4,2,0,5,3,6]),(304549, [1,4,2,3,5,0,6]),(305382, [2,0,4,1,5,3,6]),(305494, [0,4,2,1,5,3,6]),(305509, [0,4,2,1,5,3,6]),(305550, [0,2,4,1,5,3,6]),(305571, [0,2,4,1,5,3,6]),(305927, [0,6,3,4,2,1,5]),(307414, [0,4,1,2,5,3,6]),(307429, [0,4,1,2,5,3,6]),(307541, [1,0,4,2,5,3,6]),(307597, [0,1,4,2,5,3,6]),(307603, [0,1,4,2,5,3,6]),(307847, [0,6,3,4,1,2,5]),(312502, [0,5,4,1,2,3,6]),(312629, [0,5,4,2,1,3,6]),(313462, [0,4,5,1,2,3,6]),(313518, [0,6,3,2,1,4,5]),(313630, [0,2,4,5,1,3,6]),(313645, [0,1,5,4,2,3,6]),(313651, [0,1,5,4,2,3,6]),(313895, [0,2,1,5,4,3,6]),(315509, [0,4,5,2,1,3,6]),(315550, [0,2,5,4,1,3,6]),(315565, [0,1,4,5,2,3,6]),(315571, [0,1,4,5,2,3,6]),(315677, [0,6,3,1,2,4,5]),(315927, [0,1,2,5,4,3,6]),(319655, [0,2,1,4,5,3,6]),(319767, [0,1,2,4,5,3,6]),(331116, [0,4,2,3,6,1,5]),(331122, [0,4,2,3,6,1,5]),(331178, [0,5,1,4,2,3,6]),(331366, [2,0,4,3,6,1,5]),(331534, [0,2,4,3,6,1,5]),(331555, [0,2,4,3,6,1,5]),(333036, [0,4,1,6,3,2,5]),(333042, [0,4,1,6,3,2,5]),(333148, [1,6,3,0,4,2,5]),(333169, [1,6,3,2,4,0,5]),(333210, [0,3,6,1,4,2,5]),(333225, [0,3,6,1,4,2,5]),(333398, [0,4,3,6,1,2,5]),(333413, [0,4,3,6,1,2,5]),(333454, [0,5,2,1,4,3,6]),(333475, [0,5,2,3,4,1,6]),(333581, [0,1,6,3,4,2,5]),(333587, [0,1,6,3,4,2,5]),(334058, [0,4,1,5,2,3,6]),(334170, [0,3,6,1,5,2,4]),(334185, [0,3,6,1,5,2,4]),(334414, [0,2,5,1,6,3,4]),(334435, [0,2,5,1,6,3,4]),(334603, [0,1,5,2,4,3,6]),(337126, [2,0,4,1,6,3,5]),(337238, [0,4,2,1,6,3,5]),(337253, [0,4,2,1,6,3,5]),(337294, [0,2,4,1,6,3,5]),(337315, [0,2,4,1,6,3,5]),(337671, [0,5,3,4,2,1,6]),(338254, [0,4,2,1,5,3,6]),(338275, [0,4,2,3,5,1,6]),(340174, [0,2,5,3,6,1,4]),(340195, [0,2,5,3,6,1,4]),(340301, [0,1,6,3,5,2,4]),(340307, [0,1,6,3,5,2,4]),(340363, [0,1,4,2,5,3,6]),(340551, [0,4,3,5,2,1,6]),(345206, [1,6,3,2,0,4,5]),(345262, [0,2,3,6,1,4,5]),(345374, [0,3,6,1,2,4,5]),(345389, [0,1,6,3,2,4,5]),(345395, [0,1,6,3,2,4,5]),(345639, [0,2,1,6,3,4,5]),(346222, [0,2,3,6,1,5,4]),(346411, [0,1,5,4,2,3,6]),(348254, [0,3,6,1,2,5,4]),(348269, [0,1,6,3,2,5,4]),(348275, [0,1,6,3,2,5,4]),(348331, [0,1,4,5,2,3,6]),(348443, [1,6,3,0,2,4,5]),(348687, [0,1,2,5,4,3,6]),(352359, [0,2,1,6,3,5,4]),(352527, [0,1,2,4,5,3,6]),(396524, [2,6,3,0,4,1,5]),(396530, [2,6,3,1,4,0,5]),(396636, [0,4,2,6,3,1,5]),(396657, [0,4,2,6,3,1,5]),(396698, [0,3,6,2,4,1,5]),(396713, [0,3,6,2,4,1,5]),(396886, [0,4,3,6,2,1,5]),(396901, [0,4,3,6,2,1,5]),(396942, [0,2,6,3,4,1,5]),(396963, [0,2,6,3,4,1,5]),(397069, [0,5,1,2,4,3,6]),(397075, [0,5,1,3,4,2,6]),(398556, [0,4,1,3,6,2,5]),(398577, [0,4,1,3,6,2,5]),(398745, [0,5,2,4,1,3,6]),(398933, [1,0,4,3,6,2,5]),(398989, [0,1,4,3,6,2,5]),(398995, [0,1,4,3,6,2,5]),(399578, [0,3,6,2,5,1,4]),(399593, [0,3,6,2,5,1,4]),(399705, [0,4,2,5,1,3,6]),(399949, [0,1,5,2,6,3,4]),(399955, [0,1,5,2,6,3,4]),(400011, [0,1,4,3,6,2,5]),(402646, [0,4,1,2,6,3,5]),(402661, [0,4,1,2,6,3,5]),(402773, [1,0,4,2,6,3,5]),(402829, [0,1,4,2,6,3,5]),(402835, [0,1,4,2,6,3,5]),(403079, [0,5,3,4,1,2,6]),(403662, [0,2,6,3,5,1,4]),(403683, [0,2,6,3,5,1,4]),(403789, [0,1,5,3,6,2,4]),(403795, [0,1,5,3,6,2,4]),(403851, [0,1,4,2,6,3,5]),(404039, [0,4,3,5,1,2,6]),(405709, [0,4,1,2,5,3,6]),(405715, [0,4,1,3,5,2,6]),(410741, [2,6,3,1,0,4,5]),(410782, [0,2,6,3,1,4,5]),(410797, [0,3,6,2,1,4,5]),(410803, [0,2,6,3,1,4,5]),(410909, [0,1,3,6,2,4,5]),(411159, [0,1,2,6,3,4,5]),(411742, [0,2,6,3,1,5,4]),(411757, [0,3,6,2,1,5,4]),(411763, [0,2,6,3,1,5,4]),(411819, [2,6,3,0,1,4,5]),(411931, [0,1,3,6,2,4,5]),(412175, [0,1,2,6,3,4,5]),(413789, [0,1,3,6,2,5,4]),(413851, [0,1,3,6,2,5,4]),(417879, [0,1,2,6,3,5,4]),(417935, [0,1,2,6,3,5,4]),(560444, [0,5,1,3,2,4,6]),(560694, [0,5,1,2,3,4,6]),(562364, [0,5,2,3,1,4,6]),(562741, [0,5,2,1,3,4,6]),(563324, [1,5,2,3,0,4,6]),(563386, [0,3,2,5,1,4,6]),(563513, [0,3,1,5,2,4,6]),(563742, [0,2,5,1,3,4,6]),(563757, [0,1,5,2,3,4,6]),(563763, [0,1,5,2,3,4,6]),(566454, [0,5,3,2,1,4,6]),(566581, [0,5,3,1,2,4,6]),(567414, [1,5,3,2,0,4,6]),(567470, [0,2,3,5,1,4,6]),(567582, [0,3,5,1,2,4,6]),(567597, [0,1,5,3,2,4,6]),(567603, [0,1,5,3,2,4,6]),(567847, [0,2,1,5,3,4,6]),(569461, [2,5,3,1,0,4,6]),(569502, [0,2,5,3,1,4,6]),(569517, [0,3,5,2,1,4,6]),(569523, [0,2,5,3,1,4,6]),(569629, [0,1,3,5,2,4,6]),(569879, [0,1,2,5,3,4,6]),(575550, [0,2,3,1,5,4,6]),(577597, [0,1,3,2,5,4,6]),(581687, [0,1,2,3,5,4,6]),(593210, [0,3,2,4,6,1,5]),(593454, [0,2,3,4,6,1,5]),(595068, [0,4,6,1,3,2,5]),(595130, [0,5,2,3,1,4,6]),(595257, [0,3,1,6,4,2,5]),(595486, [0,3,4,6,1,2,5]),(595501, [0,1,6,4,3,2,5]),(595507, [0,1,6,4,3,2,5]),(596090, [0,3,2,5,1,6,4]),(596523, [0,1,5,2,3,4,6]),(599158, [0,4,6,1,2,3,5]),(599214, [0,5,3,2,1,4,6]),(599326, [0,2,4,6,1,3,5]),(599341, [0,1,6,4,2,3,5]),(599347, [0,1,6,4,2,3,5]),(599591, [0,2,1,6,4,3,5]),(600174, [0,2,3,5,1,6,4]),(600363, [0,1,5,3,2,4,6]),(602206, [0,2,5,3,1,6,4]),(602221, [0,3,5,2,1,6,4]),(602227, [0,2,5,3,1,6,4]),(602283, [2,5,3,0,1,4,6]),(602395, [0,1,3,5,2,4,6]),(602639, [0,1,2,5,3,4,6]),(607294, [0,2,3,1,6,4,5]),(610363, [0,1,3,2,5,4,6]),(614447, [0,1,2,3,5,4,6]),(658556, [0,4,6,2,3,1,5]),(658618, [0,3,2,6,4,1,5]),(658745, [0,5,1,3,2,4,6]),(658974, [0,2,6,4,3,1,5]),(658989, [0,3,4,6,2,1,5]),(658995, [0,2,6,4,3,1,5]),(660665, [0,3,1,4,6,2,5]),(661021, [0,1,3,4,6,2,5]),(661625, [0,3,1,5,2,6,4]),(662043, [0,1,3,4,6,2,5]),(664693, [0,4,6,2,1,3,5]),(664734, [0,2,6,4,1,3,5]),(664749, [0,1,4,6,2,3,5]),(664755, [0,1,4,6,2,3,5]),(664861, [0,5,3,1,2,4,6]),(665111, [0,1,2,6,4,3,5]),(665694, [0,3,5,1,2,6,4]),(665709, [0,1,5,3,2,6,4]),(665715, [0,1,5,3,2,6,4]),(665771, [0,1,4,6,2,3,5]),(665883, [1,5,3,0,2,4,6]),(666127, [0,1,2,6,4,3,5]),(667741, [0,1,3,5,2,6,4]),(667803, [0,1,3,5,2,6,4]),(672829, [0,1,3,2,6,4,5]),(673851, [0,1,3,2,6,4,5]),(679967, [0,1,2,6,4,5,3]),(789622, [0,4,6,3,2,1,5]),(789678, [0,2,3,6,4,1,5]),(789790, [0,2,4,6,3,1,5]),(789805, [0,3,6,4,2,1,5]),(789811, [0,2,4,6,3,1,5]),(790055, [0,5,1,2,3,4,6]),(791669, [0,4,6,3,1,2,5]),(791710, [0,3,6,4,1,2,5]),(791725, [0,1,4,6,3,2,5]),(791731, [0,1,4,6,3,2,5]),(791837, [0,1,3,6,4,2,5]),(792087, [0,5,2,1,3,4,6]),(792670, [0,2,5,1,3,6,4]),(792685, [0,1,5,2,3,6,4]),(792691, [0,1,5,2,3,6,4]),(792747, [0,1,4,6,3,2,5]),(792859, [0,1,3,6,4,2,5]),(793103, [1,5,2,0,3,4,6]),(795815, [0,2,1,4,6,3,5]),(795927, [0,1,2,4,6,3,5]),(796775, [0,2,1,5,3,6,4]),(796943, [0,1,2,4,6,3,5]),(798807, [0,1,2,5,3,6,4]),(798863, [0,1,2,5,3,6,4]),(803895, [0,1,2,3,6,4,5]),(804911, [0,1,2,3,6,4,5]),(806943, [0,1,2,5,4,6,3]),(1082812, [1,4,2,3,0,5,6]),(1083062, [1,4,3,2,0,5,6]),(1083189, [2,4,3,1,0,5,6]),(1083772, [0,4,2,3,1,5,6]),(1083834, [0,3,2,4,1,5,6]),(1084022, [0,4,3,2,1,5,6]),(1084078, [0,2,3,4,1,5,6]),(1084190, [0,2,4,3,1,5,6]),(1084205, [0,3,4,2,1,5,6]),(1084211, [0,2,4,3,1,5,6]),(1085692, [0,4,1,3,2,5,6]),(1085881, [0,3,1,4,2,5,6]),(1086069, [0,4,3,1,2,5,6]),(1086110, [0,3,4,1,2,5,6]),(1086125, [0,1,4,3,2,5,6]),(1086131, [0,1,4,3,2,5,6]),(1086237, [0,1,3,4,2,5,6]),(1089782, [0,4,1,2,3,5,6]),(1089909, [0,4,2,1,3,5,6]),(1089950, [0,2,4,1,3,5,6]),(1089965, [0,1,4,2,3,5,6]),(1089971, [0,1,4,2,3,5,6]),(1090215, [0,2,1,4,3,5,6]),(1090327, [0,1,2,4,3,5,6]),(1097918, [0,2,3,1,4,5,6]),(1098045, [0,1,3,2,4,5,6]),(1098295, [0,1,2,3,4,5,6]),(1115516, [0,4,2,3,1,6,5]),(1115578, [0,3,2,4,1,6,5]),(1115766, [0,4,3,2,1,6,5]),(1115822, [0,2,3,4,1,6,5]),(1115934, [0,2,4,3,1,6,5]),(1115949, [0,3,4,2,1,6,5]),(1115955, [0,2,4,3,1,6,5]),(1116538, [0,4,2,3,1,5,6]),(1116782, [0,4,3,2,1,5,6]),(1116971, [2,4,3,0,1,5,6]),(1118458, [0,3,2,5,6,1,4]),(1118585, [0,3,1,6,5,2,4]),(1118814, [0,2,5,6,1,3,4]),(1118829, [0,1,6,5,2,3,4]),(1118835, [0,1,6,5,2,3,4]),(1118891, [0,1,4,3,2,5,6]),(1119003, [0,1,3,4,2,5,6]),(1122542, [0,2,3,5,6,1,4]),(1122654, [0,3,5,6,1,2,4]),(1122669, [0,1,6,5,3,2,4]),(1122675, [0,1,6,5,3,2,4]),(1122731, [0,1,4,2,3,5,6]),(1122919, [0,2,1,6,5,3,4]),(1123087, [0,1,2,4,3,5,6]),(1130622, [0,2,3,1,6,5,4]),(1130811, [0,1,3,2,4,5,6]),(1131055, [0,1,2,3,4,5,6]),(1180924, [0,4,1,3,2,6,5]),(1181113, [0,3,1,4,2,6,5]),(1181301, [0,4,3,1,2,6,5]),(1181342, [0,3,4,1,2,6,5]),(1181357, [0,1,4,3,2,6,5]),(1181363, [0,1,4,3,2,6,5]),(1181469, [0,1,3,4,2,6,5]),(1181946, [0,3,2,6,5,1,4]),(1182073, [0,3,1,5,6,2,4]),(1182302, [0,2,6,5,1,3,4]),(1182317, [0,1,5,6,2,3,4]),(1182323, [0,1,5,6,2,3,4]),(1182379, [0,1,4,3,2,6,5]),(1182491, [0,1,3,4,2,6,5]),(1183993, [0,4,1,3,2,5,6]),(1184349, [0,4,3,1,2,5,6]),(1184411, [1,4,3,0,2,5,6]),(1188062, [0,2,6,5,3,1,4]),(1188077, [0,3,5,6,2,1,4]),(1188083, [0,2,6,5,3,1,4]),(1188189, [0,1,3,5,6,2,4]),(1188251, [0,1,3,5,6,2,4]),(1188439, [0,1,2,6,5,3,4]),(1188495, [0,1,2,6,5,3,4]),(1196157, [0,1,3,2,6,5,4]),(1196219, [0,1,3,2,6,5,4]),(1196575, [0,1,2,6,5,4,3]),(1311990, [0,4,1,2,3,6,5]),(1312117, [0,4,2,1,3,6,5]),(1312158, [0,2,4,1,3,6,5]),(1312173, [0,1,4,2,3,6,5]),(1312179, [0,1,4,2,3,6,5]),(1312423, [0,2,1,4,3,6,5]),(1312535, [0,1,2,4,3,6,5]),(1313006, [0,2,3,6,5,1,4]),(1313118, [0,3,6,5,1,2,4]),(1313133, [0,1,5,6,3,2,4]),(1313139, [0,1,5,6,3,2,4]),(1313195, [0,1,4,2,3,6,5]),(1313383, [0,2,1,5,6,3,4]),(1313551, [0,1,2,4,3,6,5]),(1315038, [0,2,5,6,3,1,4]),(1315053, [0,3,6,5,2,1,4]),(1315059, [0,2,5,6,3,1,4]),(1315165, [0,1,3,6,5,2,4]),(1315227, [0,1,3,6,5,2,4]),(1315415, [0,1,2,5,6,3,4]),(1315471, [0,1,2,5,6,3,4]),(1319143, [0,4,1,2,3,5,6]),(1319255, [0,4,2,1,3,5,6]),(1319311, [1,4,2,0,3,5,6]),(1327223, [0,1,2,3,6,5,4]),(1327279, [0,1,2,3,6,5,4]),(1327391, [0,1,2,4,5,6,3]),(1574078, [0,2,3,1,4,6,5]),(1574205, [0,1,3,2,4,6,5]),(1574455, [0,1,2,3,4,6,5]),(1575038, [0,2,3,1,5,6,4]),(1575227, [0,1,3,2,4,6,5]),(1575471, [0,1,2,3,4,6,5]),(1577085, [0,1,3,2,5,6,4]),(1577147, [0,1,3,2,5,6,4]),(1577503, [0,1,2,5,6,4,3]),(1581175, [0,1,2,3,5,6,4]),(1581231, [0,1,2,3,5,6,4]),(1581343, [0,1,2,4,6,5,3])]

example : degreeEdgeCodes5211 = degreeWitnesses5211.map Prod.fst := by native_decide
example : degreeEdgeCodes4333222 = degreeWitnesses4333222.map Prod.fst := by native_decide

example : degreeWitnesses5211.all (fun witness =>
    validHamiltonianOrderUpper
      (BitVec.ofNat (edgeCount 7) witness.1) witness.2) := by
  native_decide

example : degreeWitnesses4333222.all (fun witness =>
    validHamiltonianOrderUpper
      (BitVec.ofNat (edgeCount 7) witness.1) witness.2) := by
  native_decide

/- Every labelled connected graph of degree sequence `4^5, 1^2` belongs to the unique
isomorphism class, represented by its twenty degree-preserving labellings. -/
set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
example : ∀ (g : BitVec (edgeCount 7)),
    (connectedUpper (n := 7) g &&
      fixedDegreeSequenceUpper (n := 7) g [4, 4, 4, 4, 4, 1, 1] &&
      !oneOfEdgeCodes (n := 7) g degreeEdgeCodes5211) = false := by
  simp (config := { maxSteps := 100000000 }) only
    [edgeCount, connectedUpper, reachableFromZeroUpper,
    fixedDegreeSequenceUpper, matchesDegreesFromUpper, degreeBitsUpper,
    BoolFour.increment, BoolFour.same, BoolFour.ofNat,
    oneOfEdgeCodes, sameEdgeCode, degreeEdgeCodes5211,
    adjUpper, setBit, bitMask, natBit,
    List.range, List.range.loop, List.foldl, List.length, List.all, List.any]
  bv_decide (maxSteps := 100000000) (timeout := 600)

/- Every labelled connected graph of degree sequence `3^4, 2^3` belongs to one of the ten
isomorphism classes, represented by all 552 distinct degree-preserving labellings. -/
set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
example : ∀ (g : BitVec (edgeCount 7)),
    (connectedUpper (n := 7) g &&
      fixedDegreeSequenceUpper (n := 7) g [3, 3, 3, 3, 2, 2, 2] &&
      !oneOfEdgeCodes (n := 7) g degreeEdgeCodes4333222) = false := by
  simp (config := { maxSteps := 100000000 }) only
    [edgeCount, connectedUpper, reachableFromZeroUpper,
    fixedDegreeSequenceUpper, matchesDegreesFromUpper, degreeBitsUpper,
    BoolFour.increment, BoolFour.same, BoolFour.ofNat,
    oneOfEdgeCodes, sameEdgeCode, degreeEdgeCodes4333222,
    adjUpper, setBit, bitMask, natBit,
    List.range, List.range.loop, List.foldl, List.length, List.all, List.any]
  bv_decide (maxSteps := 100000000) (timeout := 600)

def degreeEdgeCodes55555511 : List Nat := [2195454,2260989,2392055,2654143,3177471,4259838,4358139,4489199,4751231,5273599,8454141,8486907,8683487,8945407,9465855,16842743,16875503,16941023,17333759,17850367,33619903,33652607,33718015,33848831,34619391,67173375,67205119,67268607,67395583,67649535]

def degreeWitnesses55555511 : List (Nat × List Nat) := [(2195454, [6,1,2,3,4,5,0,7]),(2260989, [6,2,1,3,4,5,0,7]),(2392055, [6,3,1,2,4,5,0,7]),(2654143, [6,4,1,2,3,5,0,7]),(3177471, [6,5,1,2,3,4,0,7]),(4259838, [6,0,2,3,4,5,1,7]),(4358139, [6,2,0,3,4,5,1,7]),(4489199, [6,3,0,2,4,5,1,7]),(4751231, [6,4,0,2,3,5,1,7]),(5273599, [6,5,0,2,3,4,1,7]),(8454141, [6,0,1,3,4,5,2,7]),(8486907, [6,1,0,3,4,5,2,7]),(8683487, [6,3,0,1,4,5,2,7]),(8945407, [6,4,0,1,3,5,2,7]),(9465855, [6,5,0,1,3,4,2,7]),(16842743, [6,0,1,2,4,5,3,7]),(16875503, [6,1,0,2,4,5,3,7]),(16941023, [6,2,0,1,4,5,3,7]),(17333759, [6,4,0,1,2,5,3,7]),(17850367, [6,5,0,1,2,4,3,7]),(33619903, [6,0,1,2,3,5,4,7]),(33652607, [6,1,0,2,3,5,4,7]),(33718015, [6,2,0,1,3,5,4,7]),(33848831, [6,3,0,1,2,5,4,7]),(34619391, [6,5,0,1,2,3,4,7]),(67173375, [6,0,1,2,3,4,5,7]),(67205119, [6,1,0,2,3,4,5,7]),(67268607, [6,2,0,1,3,4,5,7]),(67395583, [6,3,0,1,2,4,5,7]),(67649535, [6,4,0,1,2,3,5,7])]

example : degreeEdgeCodes55555511 = degreeWitnesses55555511.map Prod.fst := by
  native_decide

example : degreeWitnesses55555511.all (fun witness =>
    validHamiltonianOrderUpper
      (BitVec.ofNat (edgeCount 8) witness.1) witness.2) := by
  native_decide

/- Every labelled connected graph of degree sequence `5^6, 1^2` belongs to its unique
isomorphism class, represented by all thirty degree-preserving labellings. -/
set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
example : ∀ (g : BitVec (edgeCount 8)),
    (connectedUpper (n := 8) g &&
      fixedDegreeSequenceUpper (n := 8) g [5, 5, 5, 5, 5, 5, 1, 1] &&
      !oneOfEdgeCodes (n := 8) g degreeEdgeCodes55555511) = false := by
  simp (config := { maxSteps := 100000000 }) only
    [edgeCount, connectedUpper, reachableFromZeroUpper,
    fixedDegreeSequenceUpper, matchesDegreesFromUpper, degreeBitsUpper,
    BoolFour.increment, BoolFour.same, BoolFour.ofNat,
    oneOfEdgeCodes, sameEdgeCode, degreeEdgeCodes55555511,
    adjUpper, setBit, bitMask, natBit,
    List.range, List.range.loop, List.foldl, List.length, List.all, List.any]
  bv_decide (maxSteps := 100000000) (timeout := 600)

def degreeEdgeCodes44444222 : List Nat := [6403052,6403058,6411132,6411194,6415222,6415278,6462456,6465524,6466540,6466546,6468572,6468593,6473660,6474620,6474682,6476540,6476729,6480380,6480630,6480757,6480798,6480813,6480819,6494200,6498284,6498290,6499306,6501338,6501353,6506364,6506426,6507386,6509306,6509433,6513146,6513390,6513502,6513517,6513523,6513579,6592500,6593516,6593522,6597606,6599638,6599653,6604726,6605686,6605742,6607356,6607606,6607733,6607774,6607789,6607795,6611446,6611879,6625260,6625266,6626282,6629350,6632398,6632419,6637430,6637486,6638446,6640122,6640366,6640478,6640493,6640499,6640555,6644206,6644583,6688748,6688754,6690780,6690801,6691802,6691817,6694870,6694885,6695886,6695907,6697933,6697939,6702588,6702838,6702965,6703006,6703021,6703027,6703610,6703854,6703966,6703981,6703987,6704043,6705657,6705886,6705901,6705907,6706013,6706075,6709726,6709741,6709747,6709991,6710103,6710159,6854588,6855548,6855610,6858678,6859638,6859694,6861308,6861558,6861685,6861726,6861741,6861747,6867774,6869694,6869821,6873534,6873911,6887292,6887354,6888314,6891382,6891438,6892398,6894074,6894318,6894430,6894445,6894451,6894507,6899518,6902398,6902587,6906238,6906671,6950780,6950842,6952700,6952889,6953722,6953849,6956540,6956790,6956917,6956958,6956973,6956979,6957562,6957806,6957918,6957933,6957939,6957995,6959609,6959838,6959853,6959859,6959965,6960027,6964926,6965053,6965886,6966075,6967933,6967995,6971646,6971773,6971835,6972023,6972079,6972191,7081846,7081902,7083516,7083766,7083893,7083934,7083949,7083955,7084538,7084782,7084894,7084909,7084915,7084971,7087606,7088039,7088622,7088999,7090654,7090669,7090675,7090919,7091031,7091087,7095742,7096119,7096702,7097135,7098622,7098749,7098811,7098999,7099055,7099167,7102839,7102895,7377916,7382006,7390142,7410682,7414766,7422846,7473148,7474170,7476217,7480286,7480301,7480307,7488254,7488381,7488443,7604214,7605230,7607262,7607277,7607283,7611367,7619070,7619447,7619503,7866302,7867262,7869182,7869309,7869371,7873022,7873399,7873455,7881535,10591224,10594292,10595308,10595314,10597340,10597361,10602428,10603388,10603450,10605308,10605497,10609148,10609398,10609525,10609566,10609581,10609587,10660828,10660849,10668796,10668985,10674933,10675101,10686456,10692572,10692593,10693594,10693609,10695641,10700540,10700729,10701562,10701689,10703609,10707449,10707678,10707693,10707699,10707805,10707867,10784756,10787804,10787825,10791894,10791909,10793941,10799029,10799612,10799862,10799989,10800030,10800045,10800051,10801909,10802077,10805749,10806167,10817516,10817522,10819548,10819569,10820570,10820585,10823638,10823653,10824654,10824675,10826701,10826707,10831356,10831606,10831733,10831774,10831789,10831795,10832378,10832622,10832734,10832749,10832755,10832811,10834425,10834654,10834669,10834675,10834781,10834843,10838494,10838509,10838515,10838759,10838871,10838927,10883036,10883057,10886105,10889173,10890189,10890195,10897141,10897309,10897913,10898142,10898157,10898163,10898269,10898331,10900189,10904029,10904279,11046844,11049724,11049913,11052981,11053564,11053814,11053941,11053982,11053997,11054003,11055861,11056029,11061950,11062077,11063997,11067837,11068087,11079548,11079610,11081468,11081657,11082490,11082617,11085308,11085558,11085685,11085726,11085741,11085747,11086330,11086574,11086686,11086701,11086707,11086763,11088377,11088606,11088621,11088627,11088733,11088795,11093694,11093821,11094654,11094843,11096701,11096763,11100414,11100541,11100603,11100791,11100847,11100959,11144956,11145145,11148025,11151093,11151261,11151865,11152094,11152109,11152115,11152221,11152283,11154141,11159229,11160189,11160251,11165949,11166367,11275772,11276022,11276149,11276190,11276205,11276211,11278069,11278237,11278841,11279070,11279085,11279091,11279197,11279259,11281909,11282327,11282910,11282925,11282931,11283175,11283287,11283343,11284957,11285207,11290045,11290295,11290878,11291005,11291067,11291255,11291311,11291423,11292925,11293343,11297015,11297183,11570172,11576309,11584445,11601916,11602938,11604985,11609054,11609069,11609075,11617022,11617149,11617211,11668473,11674589,11682557,11798517,11799518,11799533,11799539,11801565,11805655,11813373,11813623,11813791,12060605,12061438,12061565,12061627,12063485,12067325,12067575,12067743,12075711,12687352,12691436,12691442,12692458,12694490,12694505,12699516,12699578,12700538,12702458,12702585,12706298,12706542,12706654,12706669,12706675,12706731,12750840,12756956,12756977,12757978,12757993,12760025,12764924,12765113,12765946,12766073,12767993,12771833,12772062,12772077,12772083,12772189,12772251,12789722,12789737,12797690,12797817,12804843,12804955,12881900,12881906,12883932,12883953,12884954,12884969,12888022,12888037,12889038,12889059,12891085,12891091,12895740,12895990,12896117,12896158,12896173,12896179,12896762,12897006,12897118,12897133,12897139,12897195,12898809,12899038,12899053,12899059,12899165,12899227,12902878,12902893,12902899,12903143,12903255,12903311,12914666,12916698,12916713,12920782,12920803,12923851,12928506,12928750,12928862,12928877,12928883,12928939,12929899,12931819,12931931,12935659,12936015,12980186,12980201,12982233,12986317,12986323,12987339,12994041,12994270,12994285,12994291,12994397,12994459,12995307,12995419,12997339,13001179,13001423,13143932,13143994,13145852,13146041,13146874,13147001,13149692,13149942,13150069,13150110,13150125,13150131,13150714,13150958,13151070,13151085,13151091,13151147,13152761,13152990,13153005,13153011,13153117,13153179,13158078,13158205,13159038,13159227,13161085,13161147,13164798,13164925,13164987,13165175,13165231,13165343,13176698,13178618,13178745,13182458,13182702,13182814,13182829,13182835,13182891,13183851,13185771,13185883,13190782,13190971,13193851,13197691,13197935,13242106,13242233,13244153,13247993,13248222,13248237,13248243,13248349,13248411,13249259,13249371,13251291,13256317,13256379,13257339,13263099,13263455,13372922,13373166,13373278,13373293,13373299,13373355,13374969,13375198,13375213,13375219,13375325,13375387,13376235,13376347,13379038,13379053,13379059,13379303,13379415,13379471,13380075,13380431,13382107,13382351,13387006,13387133,13387195,13387383,13387439,13387551,13388155,13388399,13390075,13390431,13394159,13394271,13666300,13667322,13669369,13673438,13673453,13673459,13681406,13681533,13681595,13699066,13706219,13714299,13764601,13771739,13779707,13895646,13895661,13895667,13896683,13898715,13902799,13910523,13910767,13910879,14157566,14157693,14157755,14158715,14160635,14164475,14164719,14164831,14172799,18978804,18979820,18979826,18983910,18985942,18985957,18991030,18991990,18992046,18993660,18993910,18994037,18994078,18994093,18994099,18997750,18998183,19042292,19045340,19045361,19049430,19049445,19051477,19056565,19057148,19057398,19057525,19057566,19057581,19057587,19059445,19059613,19063285,19063703,19075052,19075058,19077084,19077105,19078106,19078121,19081174,19081189,19082190,19082211,19084237,19084243,19088892,19089142,19089269,19089310,19089325,19089331,19089914,19090158,19090270,19090285,19090291,19090347,19091961,19092190,19092205,19092211,19092317,19092379,19096030,19096045,19096051,19096295,19096407,19096463,19176406,19176421,19188214,19188647,19190261,19190679,19206118,19208150,19208165,19209166,19209187,19215303,19219958,19220391,19220974,19221351,19223006,19223021,19223027,19223271,19223383,19223439,19227111,19271638,19271653,19273685,19274701,19274707,19278791,19285493,19285911,19286494,19286509,19286515,19286759,19286871,19286927,19288541,19288791,19292631,19435446,19437493,19438076,19438326,19438453,19438494,19438509,19438515,19442166,19442599,19444213,19444631,19450302,19450679,19452349,19452599,19456439,19468150,19468206,19469820,19470070,19470197,19470238,19470253,19470259,19470842,19471086,19471198,19471213,19471219,19471275,19473910,19474343,19474926,19475303,19476958,19476973,19476979,19477223,19477335,19477391,19482046,19482423,19483006,19483439,19484926,19485053,19485115,19485303,19485359,19485471,19489143,19489199,19533308,19533558,19533685,19533726,19533741,19533747,19535605,19535773,19536377,19536606,19536621,19536627,19536733,19536795,19539445,19539863,19540446,19540461,19540467,19540711,19540823,19540879,19542493,19542743,19547581,19547831,19548414,19548541,19548603,19548791,19548847,19548959,19550461,19550879,19554551,19554719,19664374,19664807,19666421,19666839,19667422,19667437,19667443,19667687,19667799,19667855,19671527,19673559,19678647,19679607,19679663,19681527,19681695,19958774,19960821,19973047,19990518,19991534,19993566,19993581,19993587,19997671,20005374,20005751,20005807,20056053,20057054,20057069,20057075,20059101,20063191,20070909,20071159,20071327,20188135,20190167,20201975,20449207,20449790,20450167,20450223,20451837,20452087,20452255,20455927,20464063,21075948,21075954,21076970,21080038,21083086,21083107,21088118,21088174,21089134,21090810,21091054,21091166,21091181,21091187,21091243,21094894,21095271,21139436,21139442,21141468,21141489,21142490,21142505,21145558,21145573,21146574,21146595,21148621,21148627,21153276,21153526,21153653,21153694,21153709,21153715,21154298,21154542,21154654,21154669,21154675,21154731,21156345,21156574,21156589,21156595,21156701,21156763,21160414,21160429,21160435,21160679,21160791,21160847,21172202,21174234,21174249,21178318,21178339,21181387,21186042,21186286,21186398,21186413,21186419,21186475,21187435,21189355,21189467,21193195,21193551,21270502,21272534,21272549,21273550,21273571,21279687,21284342,21284775,21285358,21285735,21287390,21287405,21287411,21287655,21287767,21287823,21291495,21305294,21305315,21317102,21317479,21320171,21320527,21368782,21368803,21370829,21370835,21371851,21374919,21382622,21382637,21382643,21382887,21382999,21383055,21383659,21384015,21385691,21385935,21389775,21532534,21532590,21534204,21534454,21534581,21534622,21534637,21534643,21535226,21535470,21535582,21535597,21535603,21535659,21538294,21538727,21539310,21539687,21541342,21541357,21541363,21541607,21541719,21541775,21546430,21546807,21547390,21547823,21549310,21549437,21549499,21549687,21549743,21549855,21553527,21553583,21565294,21566970,21567214,21567326,21567341,21567347,21567403,21568363,21571054,21571431,21574123,21574479,21579134,21579567,21582203,21582447,21586287,21630458,21630702,21630814,21630829,21630835,21630891,21632505,21632734,21632749,21632755,21632861,21632923,21633771,21633883,21636574,21636589,21636595,21636839,21636951,21637007,21637611,21637967,21639643,21639887,21644542,21644669,21644731,21644919,21644975,21645087,21645691,21645935,21647611,21647967,21651695,21651807,21761518,21761895,21763550,21763565,21763571,21763815,21763927,21763983,21764587,21764943,21767655,21770703,21775735,21775791,21776751,21778671,21778783,22054902,22055918,22057950,22057965,22057971,22062055,22069758,22070135,22070191,22087662,22090731,22102895,22153182,22153197,22153203,22154219,22156251,22160335,22168059,22168303,22168415,22284263,22287311,22299119,22545918,22546295,22546351,22547311,22548987,22549231,22549343,22553071,22561151,25268204,25268210,25270236,25270257,25271258,25271273,25274326,25274341,25275342,25275363,25277389,25277395,25282044,25282294,25282421,25282462,25282477,25282483,25283066,25283310,25283422,25283437,25283443,25283499,25285113,25285342,25285357,25285363,25285469,25285531,25289182,25289197,25289203,25289447,25289559,25289615,25333724,25333745,25336793,25339861,25340877,25340883,25347829,25347997,25348601,25348830,25348845,25348851,25348957,25349019,25350877,25354717,25354967,25366490,25366505,25368537,25372621,25372627,25373643,25380345,25380574,25380589,25380595,25380701,25380763,25381611,25381723,25383643,25387483,25387727,25464790,25464805,25466837,25467853,25467859,25471943,25478645,25479063,25479646,25479661,25479667,25479911,25480023,25480079,25481693,25481943,25485783,25497550,25497571,25499597,25499603,25500619,25503687,25511390,25511405,25511411,25511655,25511767,25511823,25512427,25512783,25514459,25514703,25518543,25563085,25563091,25576925,25577175,25577947,25578191,25726460,25726710,25726837,25726878,25726893,25726899,25728757,25728925,25729529,25729758,25729773,25729779,25729885,25729947,25732597,25733015,25733598,25733613,25733619,25733863,25733975,25734031,25735645,25735895,25740733,25740983,25741566,25741693,25741755,25741943,25741999,25742111,25743613,25744031,25747703,25747871,25759226,25759470,25759582,25759597,25759603,25759659,25761273,25761502,25761517,25761523,25761629,25761691,25762539,25762651,25765342,25765357,25765363,25765607,25765719,25765775,25766379,25766735,25768411,25768655,25773310,25773437,25773499,25773687,25773743,25773855,25774459,25774703,25776379,25776735,25780463,25780575,25824761,25824990,25825005,25825011,25825117,25825179,25827037,25828059,25830877,25831127,25831899,25832143,25838845,25839263,25839867,25840223,25845983,25955806,25955821,25955827,25956071,25956183,25956239,25957853,25958103,25958875,25959119,25961943,25962959,25969911,25970079,25970927,25971039,25972959,26249205,26250206,26250221,26250227,26252253,26256343,26264061,26264311,26264479,26281950,26281965,26281971,26282987,26285019,26289103,26296827,26297071,26297183,26347485,26348507,26362591,26478551,26479567,26493407,26740221,26740471,26740639,26741243,26741487,26741599,26743519,26747359,26755327,35755964,35756924,35756986,35760054,35761014,35761070,35762684,35762934,35763061,35763102,35763117,35763123,35769150,35771070,35771197,35774910,35775287,35819452,35822332,35822521,35825589,35826172,35826422,35826549,35826590,35826605,35826611,35828469,35828637,35834558,35834685,35836605,35840445,35840695,35852156,35852218,35854076,35854265,35855098,35855225,35857916,35858166,35858293,35858334,35858349,35858355,35858938,35859182,35859294,35859309,35859315,35859371,35860985,35861214,35861229,35861235,35861341,35861403,35866302,35866429,35867262,35867451,35869309,35869371,35873022,35873149,35873211,35873399,35873455,35873567,35950518,35952565,35953148,35953398,35953525,35953566,35953581,35953587,35957238,35957671,35959285,35959703,35965374,35965751,35967421,35967671,35971511,35983222,35983278,35984892,35985142,35985269,35985310,35985325,35985331,35985914,35986158,35986270,35986285,35986291,35986347,35988982,35989415,35989998,35990375,35992030,35992045,35992051,35992295,35992407,35992463,35997118,35997495,35998078,35998511,35999998,36000125,36000187,36000375,36000431,36000543,36004215,36004271,36048380,36048630,36048757,36048798,36048813,36048819,36050677,36050845,36051449,36051678,36051693,36051699,36051805,36051867,36054517,36054935,36055518,36055533,36055539,36055783,36055895,36055951,36057565,36057815,36062653,36062903,36063486,36063613,36063675,36063863,36063919,36064031,36065533,36065951,36069623,36069791,36215486,36215613,36219326,36219703,36221373,36221623,36245310,36247230,36247357,36248190,36248379,36251070,36251447,36252030,36252463,36253950,36254077,36254139,36254327,36254383,36254495,36262463,36266303,36310718,36310845,36312765,36313725,36313787,36316605,36316855,36317438,36317565,36317627,36317815,36317871,36317983,36319485,36319903,36325951,36331711,36441534,36441911,36443581,36443831,36444414,36444541,36444603,36444791,36444847,36444959,36447671,36448631,36448687,36450551,36450719,36456767,36458687,36735934,36737981,36742071,36767678,36768638,36770558,36770685,36770747,36774398,36774775,36774831,36782911,36833213,36834046,36834173,36834235,36836093,36839933,36840183,36840351,36848319,36964279,36964862,36965239,36965295,36966909,36967159,36967327,36970999,36979135,37227327,37229247,37233087,37853052,37853114,37854074,37857142,37857198,37858158,37859834,37860078,37860190,37860205,37860211,37860267,37865278,37868158,37868347,37871998,37872431,37916540,37916602,37918460,37918649,37919482,37919609,37922300,37922550,37922677,37922718,37922733,37922739,37923322,37923566,37923678,37923693,37923699,37923755,37925369,37925598,37925613,37925619,37925725,37925787,37930686,37930813,37931646,37931835,37933693,37933755,37937406,37937533,37937595,37937783,37937839,37937951,37949306,37951226,37951353,37955066,37955310,37955422,37955437,37955443,37955499,37956459,37958379,37958491,37963390,37963579,37966459,37970299,37970543,38047606,38047662,38049276,38049526,38049653,38049694,38049709,38049715,38050298,38050542,38050654,38050669,38050675,38050731,38053366,38053799,38054382,38054759,38056414,38056429,38056435,38056679,38056791,38056847,38061502,38061879,38062462,38062895,38064382,38064509,38064571,38064759,38064815,38064927,38068599,38068655,38080366,38082042,38082286,38082398,38082413,38082419,38082475,38083435,38086126,38086503,38089195,38089551,38094206,38094639,38097275,38097519,38101359,38145530,38145774,38145886,38145901,38145907,38145963,38147577,38147806,38147821,38147827,38147933,38147995,38148843,38148955,38151646,38151661,38151667,38151911,38152023,38152079,38152683,38153039,38154715,38154959,38159614,38159741,38159803,38159991,38160047,38160159,38160763,38161007,38162683,38163039,38166767,38166879,38309694,38311614,38311741,38312574,38312763,38315454,38315831,38316414,38316847,38318334,38318461,38318523,38318711,38318767,38318879,38326847,38330687,38344318,38344507,38348158,38348591,38351227,38351471,38407806,38407995,38409853,38409915,38410875,38413566,38413693,38413755,38413943,38413999,38414111,38414715,38414959,38416635,38416991,38422079,38428799,38538622,38539055,38540542,38540669,38540731,38540919,38540975,38541087,38541691,38541935,38544759,38544815,38545775,38547695,38547807,38552895,38555775,38832062,38833022,38834942,38835069,38835131,38838782,38839159,38839215,38847295,38864766,38867835,38871919,38930174,38930301,38930363,38931323,38933243,38937083,38937327,38937439,38945407,39060990,39061367,39061423,39062383,39064059,39064303,39064415,39068143,39076223,39323455,39326335,39330175,42045308,42045370,42047228,42047417,42048250,42048377,42051068,42051318,42051445,42051486,42051501,42051507,42052090,42052334,42052446,42052461,42052467,42052523,42054137,42054366,42054381,42054387,42054493,42054555,42059454,42059581,42060414,42060603,42062461,42062523,42066174,42066301,42066363,42066551,42066607,42066719,42110716,42110905,42113785,42116853,42117021,42117625,42117854,42117869,42117875,42117981,42118043,42119901,42124989,42125949,42126011,42131709,42132127,42143482,42143609,42145529,42149369,42149598,42149613,42149619,42149725,42149787,42150635,42150747,42152667,42157693,42157755,42158715,42164475,42164831,42241532,42241782,42241909,42241950,42241965,42241971,42243829,42243997,42244601,42244830,42244845,42244851,42244957,42245019,42247669,42248087,42248670,42248685,42248691,42248935,42249047,42249103,42250717,42250967,42255805,42256055,42256638,42256765,42256827,42257015,42257071,42257183,42258685,42259103,42262775,42262943,42274298,42274542,42274654,42274669,42274675,42274731,42276345,42276574,42276589,42276595,42276701,42276763,42277611,42277723,42280414,42280429,42280435,42280679,42280791,42280847,42281451,42281807,42283483,42283727,42288382,42288509,42288571,42288759,42288815,42288927,42289531,42289775,42291451,42291807,42295535,42295647,42339833,42340062,42340077,42340083,42340189,42340251,42342109,42343131,42345949,42346199,42346971,42347215,42353917,42354335,42354939,42355295,42361055,42503870,42503997,42505917,42506877,42506939,42509757,42510007,42510590,42510717,42510779,42510967,42511023,42511135,42512637,42513055,42519103,42524863,42536574,42536763,42538621,42538683,42539643,42542334,42542461,42542523,42542711,42542767,42542879,42543483,42543727,42545403,42545759,42550847,42557567,42602109,42602171,42607869,42608287,42608891,42609247,42732798,42732925,42732987,42733175,42733231,42733343,42734845,42735263,42735867,42736223,42738935,42739103,42739951,42740063,42741983,42747071,42748031,43026365,43027198,43027325,43027387,43029245,43033085,43033335,43033503,43041471,43058942,43059069,43059131,43060091,43062011,43065851,43066095,43066207,43074175,43124477,43125499,43131615,43255293,43255543,43255711,43256315,43256559,43256671,43258591,43262431,43270399,43517631,43518591,43524351,50433910,50433966,50435580,50435830,50435957,50435998,50436013,50436019,50436602,50436846,50436958,50436973,50436979,50437035,50439670,50440103,50440686,50441063,50442718,50442733,50442739,50442983,50443095,50443151,50447806,50448183,50448766,50449199,50450686,50450813,50450875,50451063,50451119,50451231,50454903,50454959,50499068,50499318,50499445,50499486,50499501,50499507,50501365,50501533,50502137,50502366,50502381,50502387,50502493,50502555,50505205,50505623,50506206,50506221,50506227,50506471,50506583,50506639,50508253,50508503,50513341,50513591,50514174,50514301,50514363,50514551,50514607,50514719,50516221,50516639,50520311,50520479,50531834,50532078,50532190,50532205,50532211,50532267,50533881,50534110,50534125,50534131,50534237,50534299,50535147,50535259,50537950,50537965,50537971,50538215,50538327,50538383,50538987,50539343,50541019,50541263,50545918,50546045,50546107,50546295,50546351,50546463,50547067,50547311,50548987,50549343,50553071,50553183,50630134,50630567,50632181,50632599,50633182,50633197,50633203,50633447,50633559,50633615,50637287,50639319,50644407,50645367,50645423,50647287,50647455,50662894,50663271,50664926,50664941,50664947,50665191,50665303,50665359,50665963,50666319,50669031,50672079,50677111,50677167,50678127,50680047,50680159,50728414,50728429,50728435,50728679,50728791,50728847,50730461,50730711,50731483,50731727,50734551,50735567,50742519,50742687,50743535,50743647,50745567,50892222,50892599,50894269,50894519,50895102,50895229,50895291,50895479,50895535,50895647,50898359,50899319,50899375,50901239,50901407,50907455,50909375,50924926,50925359,50926846,50926973,50927035,50927223,50927279,50927391,50927995,50928239,50931063,50931119,50932079,50933999,50934111,50939199,50942079,50990334,50990461,50990523,50990711,50990767,50990879,50992381,50992799,50993403,50993759,50996471,50996639,50997487,50997599,50999519,51004607,51005567,51121527,51121583,51123447,51123615,51124463,51124575,51414967,51415550,51415927,51415983,51417597,51417847,51418015,51421687,51429823,51447294,51447671,51447727,51448687,51450363,51450607,51450719,51454447,51462527,51512829,51513079,51513247,51513851,51514095,51514207,51516127,51519967,51527935,51643895,51644911,51646943,51905983,51906943,51908863,69309436,69313526,69321662,69372924,69379061,69387197,69404668,69405690,69407737,69411806,69411821,69411827,69419774,69419901,69419963,69503990,69506037,69518263,69535734,69536750,69538782,69538797,69538803,69542887,69550590,69550967,69551023,69601269,69602270,69602285,69602291,69604317,69608407,69616125,69616375,69616543,69766078,69768125,69772215,69797822,69798782,69800702,69800829,69800891,69804542,69804919,69804975,69813055,69863357,69864190,69864317,69864379,69866237,69870077,69870327,69870495,69878463,69994423,69995006,69995383,69995439,69997053,69997303,69997471,70001143,70009279,70321150,70386685,70517751,70779839,71406586,71410670,71418750,71469052,71470074,71472121,71476190,71476205,71476211,71484158,71484285,71484347,71501818,71508971,71517051,71600118,71601134,71603166,71603181,71603187,71607271,71614974,71615351,71615407,71632878,71635947,71648111,71698398,71698413,71698419,71699435,71701467,71705551,71713275,71713519,71713631,71862206,71863166,71865086,71865213,71865275,71868926,71869303,71869359,71877439,71894910,71897979,71902063,71960318,71960445,71960507,71961467,71963387,71967227,71967471,71967583,71975551,72091134,72091511,72091567,72092527,72094203,72094447,72094559,72098287,72106367,72385534,72483835,72614895,72876927,75597820,75598842,75600889,75604958,75604973,75604979,75612926,75613053,75613115,75664377,75670493,75678461,75696121,75703259,75711227,75794421,75795422,75795437,75795443,75797469,75801559,75809277,75809527,75809695,75827166,75827181,75827187,75828203,75830235,75834319,75842043,75842287,75842399,75892701,75893723,75907807,76056509,76057342,76057469,76057531,76059389,76063229,76063479,76063647,76071615,76089086,76089213,76089275,76090235,76092155,76095995,76096239,76096351,76104319,76154621,76155643,76161759,76285437,76285687,76285855,76286459,76286703,76286815,76288735,76292575,76300543,76579837,76612603,76809183,77071103,83986422,83987438,83989470,83989485,83989491,83993575,84001278,84001655,84001711,84051957,84052958,84052973,84052979,84055005,84059095,84066813,84067063,84067231,84084702,84084717,84084723,84085739,84087771,84091855,84099579,84099823,84099935,84184039,84186071,84197879,84215783,84218831,84230639,84281303,84282319,84296159,84445111,84445694,84446071,84446127,84447741,84447991,84448159,84451831,84459967,84477438,84477815,84477871,84478831,84480507,84480751,84480863,84484591,84492671,84542973,84543223,84543391,84543995,84544239,84544351,84546271,84550111,84558079,84674039,84675055,84677087,84968439,85001199,85066719,85459455,100763582,100764542,100766462,100766589,100766651,100770302,100770679,100770735,100778815,100829117,100829950,100830077,100830139,100831997,100835837,100836087,100836255,100844223,100861694,100861821,100861883,100862843,100864763,100868603,100868847,100868959,100876927,100960183,100960766,100961143,100961199,100962813,100963063,100963231,100966903,100975039,100992510,100992887,100992943,100993903,100995579,100995823,100995935,100999663,101007743,101058045,101058295,101058463,101059067,101059311,101059423,101061343,101065183,101073151,101223231,101225151,101228991,101254975,101257855,101261695,101320383,101321343,101327103,101451199,101452159,101454079,101745599,101778303,101843711,101974527,136354812,136358902,136360949,136367038,136369085,136373175,136386556,136387578,136390646,136391662,136393694,136393709,136393715,136398782,136399742,136401662,136401789,136401851,136405502,136405879,136405935,136450044,136453113,136456181,136457182,136457197,136457203,136459229,136464317,136465150,136465277,136465339,136467197,136471037,136471287,136471455,136581110,136583157,136584158,136584173,136584179,136588263,136590295,136595383,136595966,136596343,136596399,136598013,136598263,136598431,136602103,136843198,136845245,136846078,136846205,136846267,136849335,136849918,136850295,136850351,136851965,136852215,136852383,136858431,136860351,136864191,137366526,137368573,137372663,137380799,138450940,138451962,138455030,138456046,138458078,138458093,138458099,138463166,138464126,138466046,138466173,138466235,138469886,138470263,138470319,138483706,138487790,138490859,138495870,138498939,138503023,138547194,138549241,138553310,138553325,138553331,138554347,138556379,138561278,138561405,138561467,138562427,138564347,138568187,138568431,138568543,138678254,138680286,138680301,138680307,138681323,138684391,138687439,138692094,138692471,138692527,138693487,138695163,138695407,138695519,138699247,138940286,138942206,138942333,138942395,138943355,138946046,138946423,138946479,138947439,138949115,138949359,138949471,138954559,138957439,138961279,139462654,139465723,139469807,139477887,142643196,142646265,142649333,142650334,142650349,142650355,142652381,142657469,142658302,142658429,142658491,142660349,142664189,142664439,142664607,142675962,142678009,142682078,142682093,142682099,142683115,142685147,142690046,142690173,142690235,142691195,142693115,142696955,142697199,142697311,142741497,142747613,142748635,142755581,142756603,142762719,142872542,142872557,142872563,142874589,142875611,142878679,142879695,142886397,142886647,142886815,142887419,142887663,142887775,142889695,142893535,143134462,143134589,143134651,143136509,143137531,143140349,143140599,143140767,143141371,143141615,143141727,143143647,143148735,143149695,143155455,143656957,143657979,143664095,143672063,151031798,151033845,151034846,151034861,151034867,151038951,151040983,151046071,151046654,151047031,151047087,151048701,151048951,151049119,151052791,151064558,151066590,151066605,151066611,151067627,151070695,151073743,151078398,151078775,151078831,151079791,151081467,151081711,151081823,151085551,151130078,151130093,151130099,151132125,151133147,151136215,151137231,151143933,151144183,151144351,151144955,151145199,151145311,151147231,151151071,151261159,151263191,151264207,151274999,151276015,151278047,151522814,151523191,151523247,151524861,151525111,151525279,151525883,151526127,151526239,151528951,151529967,151531999,151537087,151538047,151539967,152045559,152046575,152048607,152060415,167808958,167811005,167811838,167811965,167812027,167815095,167815678,167816055,167816111,167817725,167817975,167818143,167824191,167826111,167829951,167841662,167843582,167843709,167843771,167844731,167847422,167847799,167847855,167848815,167850491,167850735,167850847,167855935,167858815,167862655,167907070,167907197,167907259,167909117,167910139,167912957,167913207,167913375,167913979,167914223,167914335,167916255,167921343,167922303,167928063,168037886,168038263,168038319,168039933,168040183,168040351,168040955,168041199,168041311,168044023,168045039,168047071,168052159,168053119,168055039,168300351,168302271,168303231,168306111,168307071,168308991,168822719,168823679,168825599,168829439,201362430,201364477,201368567,201376703,201394174,201397243,201401327,201409407,201459709,201460731,201466847,201474815,201590775,201591791,201593823,201605631,201852863,201853823,201855743,201859583]

def memberDegreeEdgeCodes44444222
    (g : BitVec (edgeCount 8)) : Bool :=
  (bif g.getLsbD 27 then (bif g.getLsbD 26 then (bif g.getLsbD 19 then (bif g.getLsbD 13 then true else (bif g.getLsbD 12 then true else (bif g.getLsbD 11 then true else true))) else (bif g.getLsbD 18 then (bif g.getLsbD 14 then true else (bif g.getLsbD 12 then true else (bif g.getLsbD 11 then true else true))) else (bif g.getLsbD 17 then (bif g.getLsbD 14 then true else (bif g.getLsbD 13 then true else (bif g.getLsbD 11 then true else true))) else (bif g.getLsbD 16 then (bif g.getLsbD 14 then true else (bif g.getLsbD 13 then true else (bif g.getLsbD 12 then true else true))) else (bif g.getLsbD 14 then true else (bif g.getLsbD 13 then true else (bif g.getLsbD 12 then true else true))))))) else (bif g.getLsbD 25 then (bif g.getLsbD 20 then (bif g.getLsbD 13 then true else (bif g.getLsbD 12 then true else (bif g.getLsbD 11 then true else true))) else (bif g.getLsbD 19 then (bif g.getLsbD 13 then (bif g.getLsbD 12 then true else (bif g.getLsbD 11 then true else true)) else (bif g.getLsbD 12 then (bif g.getLsbD 11 then true else true) else true)) else (bif g.getLsbD 18 then (bif g.getLsbD 14 then (bif g.getLsbD 12 then true else (bif g.getLsbD 11 then true else true)) else (bif g.getLsbD 13 then (bif g.getLsbD 12 then true else (bif g.getLsbD 11 then true else true)) else (bif g.getLsbD 12 then (bif g.getLsbD 11 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then true else true) else true) else (bif g.getLsbD 9 then (bif g.getLsbD 8 then true else true) else true)) else (bif g.getLsbD 9 then (bif g.getLsbD 7 then true else true) else true)))) else (bif g.getLsbD 17 then (bif g.getLsbD 14 then (bif g.getLsbD 13 then true else (bif g.getLsbD 11 then true else true)) else (bif g.getLsbD 13 then (bif g.getLsbD 12 then true else (bif g.getLsbD 11 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then true else true) else true) else (bif g.getLsbD 9 then (bif g.getLsbD 8 then true else true) else true))) else (bif g.getLsbD 12 then (bif g.getLsbD 11 then true else true) else (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else true)))) else (bif g.getLsbD 16 then (bif g.getLsbD 14 then (bif g.getLsbD 13 then true else (bif g.getLsbD 12 then true else true)) else (bif g.getLsbD 13 then (bif g.getLsbD 12 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then true else true) else true) else (bif g.getLsbD 11 then true else (bif g.getLsbD 9 then (bif g.getLsbD 7 then true else true) else true))) else (bif g.getLsbD 12 then (bif g.getLsbD 11 then true else (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else true)) else true))) else (bif g.getLsbD 14 then (bif g.getLsbD 13 then true else (bif g.getLsbD 12 then true else true)) else (bif g.getLsbD 13 then (bif g.getLsbD 12 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then true else true) else true) else (bif g.getLsbD 11 then (bif g.getLsbD 9 then (bif g.getLsbD 7 then true else true) else true) else true)) else (bif g.getLsbD 12 then (bif g.getLsbD 11 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else true) else true) else true)))))))) else (bif g.getLsbD 24 then (bif g.getLsbD 20 then (bif g.getLsbD 14 then true else (bif g.getLsbD 12 then true else (bif g.getLsbD 11 then true else true))) else (bif g.getLsbD 19 then (bif g.getLsbD 14 then (bif g.getLsbD 12 then true else (bif g.getLsbD 11 then true else true)) else (bif g.getLsbD 13 then (bif g.getLsbD 12 then true else (bif g.getLsbD 11 then true else true)) else (bif g.getLsbD 12 then (bif g.getLsbD 11 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then true else true) else true) else (bif g.getLsbD 9 then (bif g.getLsbD 8 then true else true) else true)) else (bif g.getLsbD 9 then (bif g.getLsbD 7 then true else true) else true)))) else (bif g.getLsbD 18 then (bif g.getLsbD 14 then (bif g.getLsbD 12 then true else (bif g.getLsbD 11 then true else true)) else (bif g.getLsbD 12 then (bif g.getLsbD 11 then true else true) else true)) else (bif g.getLsbD 17 then (bif g.getLsbD 14 then (bif g.getLsbD 13 then true else (bif g.getLsbD 12 then true else (bif g.getLsbD 11 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then true else true) else true) else (bif g.getLsbD 9 then (bif g.getLsbD 8 then true else true) else true)))) else (bif g.getLsbD 13 then (bif g.getLsbD 11 then true else true) else (bif g.getLsbD 12 then (bif g.getLsbD 11 then true else true) else (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true)))) else (bif g.getLsbD 16 then (bif g.getLsbD 14 then (bif g.getLsbD 13 then true else (bif g.getLsbD 12 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then true else true) else true) else (bif g.getLsbD 11 then true else (bif g.getLsbD 9 then (bif g.getLsbD 7 then true else true) else true)))) else (bif g.getLsbD 13 then (bif g.getLsbD 12 then true else true) else (bif g.getLsbD 12 then (bif g.getLsbD 11 then true else (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true)) else true))) else (bif g.getLsbD 14 then (bif g.getLsbD 13 then true else (bif g.getLsbD 12 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then true else true) else true) else (bif g.getLsbD 11 then (bif g.getLsbD 9 then (bif g.getLsbD 7 then true else true) else true) else true))) else (bif g.getLsbD 13 then (bif g.getLsbD 12 then true else true) else (bif g.getLsbD 12 then (bif g.getLsbD 11 then (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true) else true) else true)))))))) else (bif g.getLsbD 23 then (bif g.getLsbD 20 then (bif g.getLsbD 14 then true else (bif g.getLsbD 13 then true else (bif g.getLsbD 11 then true else true))) else (bif g.getLsbD 19 then (bif g.getLsbD 14 then (bif g.getLsbD 13 then true else (bif g.getLsbD 11 then true else true)) else (bif g.getLsbD 13 then (bif g.getLsbD 12 then true else (bif g.getLsbD 11 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then true else true) else true) else (bif g.getLsbD 9 then (bif g.getLsbD 8 then true else true) else true))) else (bif g.getLsbD 12 then (bif g.getLsbD 11 then true else true) else (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else true)))) else (bif g.getLsbD 18 then (bif g.getLsbD 14 then (bif g.getLsbD 13 then true else (bif g.getLsbD 12 then true else (bif g.getLsbD 11 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then true else true) else true) else (bif g.getLsbD 9 then (bif g.getLsbD 8 then true else true) else true)))) else (bif g.getLsbD 13 then (bif g.getLsbD 11 then true else true) else (bif g.getLsbD 12 then (bif g.getLsbD 11 then true else true) else (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true)))) else (bif g.getLsbD 17 then (bif g.getLsbD 14 then (bif g.getLsbD 13 then true else (bif g.getLsbD 11 then true else true)) else (bif g.getLsbD 13 then (bif g.getLsbD 11 then true else true) else true)) else (bif g.getLsbD 16 then (bif g.getLsbD 14 then (bif g.getLsbD 13 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then true else true) else true) else (bif g.getLsbD 12 then true else (bif g.getLsbD 11 then true else (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else true)))) else (bif g.getLsbD 13 then (bif g.getLsbD 12 then true else (bif g.getLsbD 11 then true else (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true))) else (bif g.getLsbD 12 then true else true))) else (bif g.getLsbD 14 then (bif g.getLsbD 13 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then true else true) else true) else (bif g.getLsbD 12 then true else (bif g.getLsbD 11 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else true) else true))) else (bif g.getLsbD 13 then (bif g.getLsbD 12 then true else (bif g.getLsbD 11 then (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true) else true)) else (bif g.getLsbD 12 then true else true)))))))) else (bif g.getLsbD 22 then (bif g.getLsbD 20 then (bif g.getLsbD 14 then true else (bif g.getLsbD 13 then true else (bif g.getLsbD 12 then true else true))) else (bif g.getLsbD 19 then (bif g.getLsbD 14 then (bif g.getLsbD 13 then true else (bif g.getLsbD 12 then true else true)) else (bif g.getLsbD 13 then (bif g.getLsbD 12 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then true else true) else true) else (bif g.getLsbD 11 then true else (bif g.getLsbD 9 then (bif g.getLsbD 7 then true else true) else true))) else (bif g.getLsbD 12 then (bif g.getLsbD 11 then true else (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else true)) else true))) else (bif g.getLsbD 18 then (bif g.getLsbD 14 then (bif g.getLsbD 13 then true else (bif g.getLsbD 12 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then true else true) else true) else (bif g.getLsbD 11 then true else (bif g.getLsbD 9 then (bif g.getLsbD 7 then true else true) else true)))) else (bif g.getLsbD 13 then (bif g.getLsbD 12 then true else true) else (bif g.getLsbD 12 then (bif g.getLsbD 11 then true else (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true)) else true))) else (bif g.getLsbD 17 then (bif g.getLsbD 14 then (bif g.getLsbD 13 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then true else true) else true) else (bif g.getLsbD 12 then true else (bif g.getLsbD 11 then true else (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else true)))) else (bif g.getLsbD 13 then (bif g.getLsbD 12 then true else (bif g.getLsbD 11 then true else (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true))) else (bif g.getLsbD 12 then true else true))) else (bif g.getLsbD 16 then (bif g.getLsbD 14 then (bif g.getLsbD 13 then true else (bif g.getLsbD 12 then true else true)) else (bif g.getLsbD 13 then (bif g.getLsbD 12 then true else true) else true)) else (bif g.getLsbD 14 then (bif g.getLsbD 13 then (bif g.getLsbD 9 then (bif g.getLsbD 7 then true else true) else true) else (bif g.getLsbD 12 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else true) else (bif g.getLsbD 11 then true else true))) else (bif g.getLsbD 13 then (bif g.getLsbD 12 then (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true) else (bif g.getLsbD 11 then true else true)) else (bif g.getLsbD 11 then true else true)))))))) else (bif g.getLsbD 20 then (bif g.getLsbD 14 then true else (bif g.getLsbD 13 then true else (bif g.getLsbD 12 then true else true))) else (bif g.getLsbD 19 then (bif g.getLsbD 14 then (bif g.getLsbD 13 then true else (bif g.getLsbD 12 then true else true)) else (bif g.getLsbD 13 then (bif g.getLsbD 12 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then true else true) else true) else (bif g.getLsbD 11 then (bif g.getLsbD 9 then (bif g.getLsbD 7 then true else true) else true) else true)) else (bif g.getLsbD 12 then (bif g.getLsbD 11 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else true) else true) else true))) else (bif g.getLsbD 18 then (bif g.getLsbD 14 then (bif g.getLsbD 13 then true else (bif g.getLsbD 12 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then true else true) else true) else (bif g.getLsbD 11 then (bif g.getLsbD 9 then (bif g.getLsbD 7 then true else true) else true) else true))) else (bif g.getLsbD 13 then (bif g.getLsbD 12 then true else true) else (bif g.getLsbD 12 then (bif g.getLsbD 11 then (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true) else true) else true))) else (bif g.getLsbD 17 then (bif g.getLsbD 14 then (bif g.getLsbD 13 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then true else true) else true) else (bif g.getLsbD 12 then true else (bif g.getLsbD 11 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else true) else true))) else (bif g.getLsbD 13 then (bif g.getLsbD 12 then true else (bif g.getLsbD 11 then (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true) else true)) else (bif g.getLsbD 12 then true else true))) else (bif g.getLsbD 16 then (bif g.getLsbD 14 then (bif g.getLsbD 13 then (bif g.getLsbD 9 then (bif g.getLsbD 7 then true else true) else true) else (bif g.getLsbD 12 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else true) else (bif g.getLsbD 11 then true else true))) else (bif g.getLsbD 13 then (bif g.getLsbD 12 then (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true) else (bif g.getLsbD 11 then true else true)) else (bif g.getLsbD 11 then true else true))) else (bif g.getLsbD 14 then (bif g.getLsbD 13 then true else (bif g.getLsbD 12 then true else true)) else (bif g.getLsbD 13 then (bif g.getLsbD 12 then true else true) else true)))))))))))) else (bif g.getLsbD 26 then (bif g.getLsbD 25 then (bif g.getLsbD 20 then (bif g.getLsbD 18 then true else (bif g.getLsbD 17 then true else (bif g.getLsbD 16 then true else true))) else (bif g.getLsbD 19 then (bif g.getLsbD 18 then (bif g.getLsbD 12 then true else (bif g.getLsbD 11 then true else true)) else (bif g.getLsbD 17 then (bif g.getLsbD 13 then true else (bif g.getLsbD 11 then true else true)) else (bif g.getLsbD 16 then (bif g.getLsbD 13 then true else (bif g.getLsbD 12 then true else true)) else (bif g.getLsbD 13 then true else (bif g.getLsbD 12 then true else true))))) else (bif g.getLsbD 18 then (bif g.getLsbD 17 then (bif g.getLsbD 14 then true else (bif g.getLsbD 13 then true else (bif g.getLsbD 12 then true else (bif g.getLsbD 11 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then true else true) else true) else (bif g.getLsbD 9 then (bif g.getLsbD 8 then true else true) else true))))) else (bif g.getLsbD 16 then (bif g.getLsbD 14 then true else (bif g.getLsbD 13 then true else (bif g.getLsbD 12 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then true else true) else true) else (bif g.getLsbD 11 then true else (bif g.getLsbD 9 then (bif g.getLsbD 7 then true else true) else true))))) else (bif g.getLsbD 14 then true else (bif g.getLsbD 13 then true else (bif g.getLsbD 12 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then true else true) else true) else (bif g.getLsbD 11 then (bif g.getLsbD 9 then (bif g.getLsbD 7 then true else true) else true) else true)))))) else (bif g.getLsbD 17 then (bif g.getLsbD 16 then (bif g.getLsbD 14 then true else (bif g.getLsbD 13 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then true else true) else true) else (bif g.getLsbD 12 then true else (bif g.getLsbD 11 then true else (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else true))))) else (bif g.getLsbD 14 then true else (bif g.getLsbD 13 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then true else true) else true) else (bif g.getLsbD 12 then true else (bif g.getLsbD 11 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else true) else true))))) else (bif g.getLsbD 14 then true else (bif g.getLsbD 13 then (bif g.getLsbD 9 then (bif g.getLsbD 7 then true else true) else true) else (bif g.getLsbD 12 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else true) else (bif g.getLsbD 11 then true else true)))))))) else (bif g.getLsbD 24 then (bif g.getLsbD 20 then (bif g.getLsbD 19 then true else (bif g.getLsbD 17 then true else (bif g.getLsbD 16 then true else true))) else (bif g.getLsbD 19 then (bif g.getLsbD 18 then (bif g.getLsbD 12 then true else (bif g.getLsbD 11 then true else true)) else (bif g.getLsbD 17 then (bif g.getLsbD 14 then true else (bif g.getLsbD 13 then true else (bif g.getLsbD 12 then true else (bif g.getLsbD 11 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then true else true) else true) else (bif g.getLsbD 9 then (bif g.getLsbD 8 then true else true) else true))))) else (bif g.getLsbD 16 then (bif g.getLsbD 14 then true else (bif g.getLsbD 13 then true else (bif g.getLsbD 12 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then true else true) else true) else (bif g.getLsbD 11 then true else (bif g.getLsbD 9 then (bif g.getLsbD 7 then true else true) else true))))) else (bif g.getLsbD 14 then true else (bif g.getLsbD 13 then true else (bif g.getLsbD 12 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then true else true) else true) else (bif g.getLsbD 11 then (bif g.getLsbD 9 then (bif g.getLsbD 7 then true else true) else true) else true))))))) else (bif g.getLsbD 18 then (bif g.getLsbD 17 then (bif g.getLsbD 14 then true else (bif g.getLsbD 11 then true else true)) else (bif g.getLsbD 16 then (bif g.getLsbD 14 then true else (bif g.getLsbD 12 then true else true)) else (bif g.getLsbD 14 then true else (bif g.getLsbD 12 then true else true)))) else (bif g.getLsbD 17 then (bif g.getLsbD 16 then (bif g.getLsbD 14 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then true else true) else true) else (bif g.getLsbD 13 then true else (bif g.getLsbD 12 then true else (bif g.getLsbD 11 then true else (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true))))) else (bif g.getLsbD 14 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then true else true) else true) else (bif g.getLsbD 13 then true else (bif g.getLsbD 12 then true else (bif g.getLsbD 11 then (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true) else true))))) else (bif g.getLsbD 14 then (bif g.getLsbD 9 then (bif g.getLsbD 7 then true else true) else true) else (bif g.getLsbD 13 then true else (bif g.getLsbD 12 then (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true) else (bif g.getLsbD 11 then true else true)))))))) else (bif g.getLsbD 23 then (bif g.getLsbD 20 then (bif g.getLsbD 19 then true else (bif g.getLsbD 18 then true else (bif g.getLsbD 16 then true else true))) else (bif g.getLsbD 19 then (bif g.getLsbD 18 then (bif g.getLsbD 14 then true else (bif g.getLsbD 13 then true else (bif g.getLsbD 12 then true else (bif g.getLsbD 11 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then true else true) else true) else (bif g.getLsbD 9 then (bif g.getLsbD 8 then true else true) else true))))) else (bif g.getLsbD 17 then (bif g.getLsbD 13 then true else (bif g.getLsbD 11 then true else true)) else (bif g.getLsbD 16 then (bif g.getLsbD 14 then true else (bif g.getLsbD 13 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then true else true) else true) else (bif g.getLsbD 12 then true else (bif g.getLsbD 11 then true else (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else true))))) else (bif g.getLsbD 14 then true else (bif g.getLsbD 13 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then true else true) else true) else (bif g.getLsbD 12 then true else (bif g.getLsbD 11 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else true) else true))))))) else (bif g.getLsbD 18 then (bif g.getLsbD 17 then (bif g.getLsbD 14 then true else (bif g.getLsbD 11 then true else true)) else (bif g.getLsbD 16 then (bif g.getLsbD 14 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then true else true) else true) else (bif g.getLsbD 13 then true else (bif g.getLsbD 12 then true else (bif g.getLsbD 11 then true else (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true))))) else (bif g.getLsbD 14 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then true else true) else true) else (bif g.getLsbD 13 then true else (bif g.getLsbD 12 then true else (bif g.getLsbD 11 then (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true) else true)))))) else (bif g.getLsbD 17 then (bif g.getLsbD 16 then (bif g.getLsbD 14 then true else (bif g.getLsbD 13 then true else true)) else (bif g.getLsbD 14 then true else (bif g.getLsbD 13 then true else true))) else (bif g.getLsbD 14 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else true) else (bif g.getLsbD 13 then (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true) else (bif g.getLsbD 12 then true else (bif g.getLsbD 11 then true else true)))))))) else (bif g.getLsbD 22 then (bif g.getLsbD 20 then (bif g.getLsbD 19 then true else (bif g.getLsbD 18 then true else (bif g.getLsbD 17 then true else true))) else (bif g.getLsbD 19 then (bif g.getLsbD 18 then (bif g.getLsbD 14 then true else (bif g.getLsbD 13 then true else (bif g.getLsbD 12 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then true else true) else true) else (bif g.getLsbD 11 then true else (bif g.getLsbD 9 then (bif g.getLsbD 7 then true else true) else true))))) else (bif g.getLsbD 17 then (bif g.getLsbD 14 then true else (bif g.getLsbD 13 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then true else true) else true) else (bif g.getLsbD 12 then true else (bif g.getLsbD 11 then true else (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else true))))) else (bif g.getLsbD 16 then (bif g.getLsbD 13 then true else (bif g.getLsbD 12 then true else true)) else (bif g.getLsbD 14 then true else (bif g.getLsbD 13 then (bif g.getLsbD 9 then (bif g.getLsbD 7 then true else true) else true) else (bif g.getLsbD 12 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else true) else (bif g.getLsbD 11 then true else true))))))) else (bif g.getLsbD 18 then (bif g.getLsbD 17 then (bif g.getLsbD 14 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then true else true) else true) else (bif g.getLsbD 13 then true else (bif g.getLsbD 12 then true else (bif g.getLsbD 11 then true else (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true))))) else (bif g.getLsbD 16 then (bif g.getLsbD 14 then true else (bif g.getLsbD 12 then true else true)) else (bif g.getLsbD 14 then (bif g.getLsbD 9 then (bif g.getLsbD 7 then true else true) else true) else (bif g.getLsbD 13 then true else (bif g.getLsbD 12 then (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true) else (bif g.getLsbD 11 then true else true)))))) else (bif g.getLsbD 17 then (bif g.getLsbD 16 then (bif g.getLsbD 14 then true else (bif g.getLsbD 13 then true else true)) else (bif g.getLsbD 14 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else true) else (bif g.getLsbD 13 then (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true) else (bif g.getLsbD 12 then true else (bif g.getLsbD 11 then true else true))))) else (bif g.getLsbD 14 then true else (bif g.getLsbD 13 then true else true)))))) else (bif g.getLsbD 20 then (bif g.getLsbD 19 then true else (bif g.getLsbD 18 then true else (bif g.getLsbD 17 then true else true))) else (bif g.getLsbD 19 then (bif g.getLsbD 18 then (bif g.getLsbD 14 then true else (bif g.getLsbD 13 then true else (bif g.getLsbD 12 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then true else true) else true) else (bif g.getLsbD 11 then (bif g.getLsbD 9 then (bif g.getLsbD 7 then true else true) else true) else true)))) else (bif g.getLsbD 17 then (bif g.getLsbD 14 then true else (bif g.getLsbD 13 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then true else true) else true) else (bif g.getLsbD 12 then true else (bif g.getLsbD 11 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else true) else true)))) else (bif g.getLsbD 16 then (bif g.getLsbD 14 then true else (bif g.getLsbD 13 then (bif g.getLsbD 9 then (bif g.getLsbD 7 then true else true) else true) else (bif g.getLsbD 12 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else true) else (bif g.getLsbD 11 then true else true)))) else (bif g.getLsbD 13 then true else (bif g.getLsbD 12 then true else true))))) else (bif g.getLsbD 18 then (bif g.getLsbD 17 then (bif g.getLsbD 14 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then true else true) else true) else (bif g.getLsbD 13 then true else (bif g.getLsbD 12 then true else (bif g.getLsbD 11 then (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true) else true)))) else (bif g.getLsbD 16 then (bif g.getLsbD 14 then (bif g.getLsbD 9 then (bif g.getLsbD 7 then true else true) else true) else (bif g.getLsbD 13 then true else (bif g.getLsbD 12 then (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true) else (bif g.getLsbD 11 then true else true)))) else (bif g.getLsbD 14 then true else (bif g.getLsbD 12 then true else true)))) else (bif g.getLsbD 17 then (bif g.getLsbD 16 then (bif g.getLsbD 14 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else true) else (bif g.getLsbD 13 then (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true) else (bif g.getLsbD 12 then true else (bif g.getLsbD 11 then true else true)))) else (bif g.getLsbD 14 then true else (bif g.getLsbD 13 then true else true))) else (bif g.getLsbD 14 then true else (bif g.getLsbD 13 then true else true)))))))))) else (bif g.getLsbD 25 then (bif g.getLsbD 24 then (bif g.getLsbD 20 then (bif g.getLsbD 19 then (bif g.getLsbD 12 then true else (bif g.getLsbD 11 then true else true)) else (bif g.getLsbD 18 then (bif g.getLsbD 12 then true else (bif g.getLsbD 11 then true else true)) else (bif g.getLsbD 17 then (bif g.getLsbD 14 then true else (bif g.getLsbD 13 then true else (bif g.getLsbD 12 then true else (bif g.getLsbD 11 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then true else true) else true) else (bif g.getLsbD 9 then (bif g.getLsbD 8 then true else true) else true))))) else (bif g.getLsbD 16 then (bif g.getLsbD 14 then true else (bif g.getLsbD 13 then true else (bif g.getLsbD 12 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then true else true) else true) else (bif g.getLsbD 11 then true else (bif g.getLsbD 9 then (bif g.getLsbD 7 then true else true) else true))))) else (bif g.getLsbD 14 then true else (bif g.getLsbD 13 then true else (bif g.getLsbD 12 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then true else true) else true) else (bif g.getLsbD 11 then (bif g.getLsbD 9 then (bif g.getLsbD 7 then true else true) else true) else true)))))))) else (bif g.getLsbD 19 then (bif g.getLsbD 18 then (bif g.getLsbD 12 then (bif g.getLsbD 11 then (bif g.getLsbD 8 then true else true) else (bif g.getLsbD 8 then true else true)) else (bif g.getLsbD 7 then true else true)) else (bif g.getLsbD 17 then (bif g.getLsbD 14 then (bif g.getLsbD 11 then true else true) else (bif g.getLsbD 13 then (bif g.getLsbD 12 then true else (bif g.getLsbD 11 then (bif g.getLsbD 8 then true else true) else (bif g.getLsbD 8 then true else true))) else (bif g.getLsbD 12 then (bif g.getLsbD 11 then (bif g.getLsbD 9 then true else true) else (bif g.getLsbD 9 then true else true)) else (bif g.getLsbD 9 then (bif g.getLsbD 8 then true else (bif g.getLsbD 7 then true else true)) else (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else true))))) else (bif g.getLsbD 16 then (bif g.getLsbD 14 then (bif g.getLsbD 12 then true else true) else (bif g.getLsbD 13 then (bif g.getLsbD 12 then (bif g.getLsbD 8 then true else true) else (bif g.getLsbD 11 then true else (bif g.getLsbD 7 then true else true))) else (bif g.getLsbD 12 then (bif g.getLsbD 11 then (bif g.getLsbD 9 then true else true) else (bif g.getLsbD 9 then (bif g.getLsbD 8 then true else (bif g.getLsbD 7 then true else true)) else (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else true))) else (bif g.getLsbD 9 then true else true)))) else (bif g.getLsbD 14 then (bif g.getLsbD 12 then true else true) else (bif g.getLsbD 13 then (bif g.getLsbD 12 then (bif g.getLsbD 8 then true else true) else (bif g.getLsbD 11 then (bif g.getLsbD 7 then true else true) else true)) else (bif g.getLsbD 12 then (bif g.getLsbD 11 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then true else (bif g.getLsbD 7 then true else true)) else (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else true)) else (bif g.getLsbD 9 then true else true)) else (bif g.getLsbD 9 then true else true))))))) else (bif g.getLsbD 18 then (bif g.getLsbD 17 then (bif g.getLsbD 14 then (bif g.getLsbD 12 then true else (bif g.getLsbD 11 then (bif g.getLsbD 8 then true else true) else (bif g.getLsbD 8 then true else true))) else (bif g.getLsbD 13 then (bif g.getLsbD 11 then true else true) else (bif g.getLsbD 12 then (bif g.getLsbD 11 then (bif g.getLsbD 9 then true else true) else (bif g.getLsbD 9 then true else true)) else (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else true) else (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true))))) else (bif g.getLsbD 16 then (bif g.getLsbD 14 then (bif g.getLsbD 12 then (bif g.getLsbD 8 then true else true) else (bif g.getLsbD 11 then true else (bif g.getLsbD 7 then true else true))) else (bif g.getLsbD 13 then (bif g.getLsbD 12 then true else true) else (bif g.getLsbD 12 then (bif g.getLsbD 11 then (bif g.getLsbD 9 then true else true) else (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else true) else (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true))) else (bif g.getLsbD 9 then true else true)))) else (bif g.getLsbD 14 then (bif g.getLsbD 12 then (bif g.getLsbD 8 then true else true) else (bif g.getLsbD 11 then (bif g.getLsbD 7 then true else true) else true)) else (bif g.getLsbD 13 then (bif g.getLsbD 12 then true else true) else (bif g.getLsbD 12 then (bif g.getLsbD 11 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else true) else (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true)) else (bif g.getLsbD 9 then true else true)) else (bif g.getLsbD 9 then true else true)))))) else (bif g.getLsbD 17 then (bif g.getLsbD 16 then (bif g.getLsbD 14 then (bif g.getLsbD 13 then (bif g.getLsbD 8 then true else true) else (bif g.getLsbD 12 then (bif g.getLsbD 9 then true else true) else (bif g.getLsbD 11 then (bif g.getLsbD 9 then true else true) else (bif g.getLsbD 9 then (bif g.getLsbD 8 then true else (bif g.getLsbD 7 then true else true)) else (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else true))))) else (bif g.getLsbD 13 then (bif g.getLsbD 12 then (bif g.getLsbD 9 then true else true) else (bif g.getLsbD 11 then (bif g.getLsbD 9 then true else true) else (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else true) else (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true)))) else (bif g.getLsbD 12 then (bif g.getLsbD 11 then (bif g.getLsbD 8 then true else true) else (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true)) else true)) else (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true)) else true) else true)))) else (bif g.getLsbD 14 then (bif g.getLsbD 13 then (bif g.getLsbD 8 then true else true) else (bif g.getLsbD 12 then (bif g.getLsbD 9 then true else true) else (bif g.getLsbD 11 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then true else (bif g.getLsbD 7 then true else true)) else (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else true)) else (bif g.getLsbD 9 then true else true)))) else (bif g.getLsbD 13 then (bif g.getLsbD 12 then (bif g.getLsbD 9 then true else true) else (bif g.getLsbD 11 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else true) else (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true)) else (bif g.getLsbD 9 then true else true))) else (bif g.getLsbD 12 then (bif g.getLsbD 11 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true)) else true) else (bif g.getLsbD 8 then true else true)) else (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true) else true) else true) else true))))) else (bif g.getLsbD 14 then (bif g.getLsbD 13 then (bif g.getLsbD 7 then true else true) else (bif g.getLsbD 12 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then true else (bif g.getLsbD 7 then true else true)) else (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else true)) else (bif g.getLsbD 11 then (bif g.getLsbD 9 then true else true) else (bif g.getLsbD 9 then true else true)))) else (bif g.getLsbD 13 then (bif g.getLsbD 12 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else true) else (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true)) else (bif g.getLsbD 11 then (bif g.getLsbD 9 then true else true) else (bif g.getLsbD 9 then true else true))) else (bif g.getLsbD 12 then (bif g.getLsbD 11 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true)) else true) else true) else (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true) else true) else true) else true)) else (bif g.getLsbD 7 then true else true)))))))) else (bif g.getLsbD 23 then (bif g.getLsbD 20 then (bif g.getLsbD 19 then (bif g.getLsbD 13 then true else (bif g.getLsbD 11 then true else true)) else (bif g.getLsbD 18 then (bif g.getLsbD 14 then true else (bif g.getLsbD 13 then true else (bif g.getLsbD 12 then true else (bif g.getLsbD 11 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then true else true) else true) else (bif g.getLsbD 9 then (bif g.getLsbD 8 then true else true) else true))))) else (bif g.getLsbD 17 then (bif g.getLsbD 13 then true else (bif g.getLsbD 11 then true else true)) else (bif g.getLsbD 16 then (bif g.getLsbD 14 then true else (bif g.getLsbD 13 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then true else true) else true) else (bif g.getLsbD 12 then true else (bif g.getLsbD 11 then true else (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else true))))) else (bif g.getLsbD 14 then true else (bif g.getLsbD 13 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then true else true) else true) else (bif g.getLsbD 12 then true else (bif g.getLsbD 11 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else true) else true)))))))) else (bif g.getLsbD 19 then (bif g.getLsbD 18 then (bif g.getLsbD 14 then (bif g.getLsbD 11 then true else true) else (bif g.getLsbD 13 then (bif g.getLsbD 12 then true else (bif g.getLsbD 11 then (bif g.getLsbD 8 then true else true) else (bif g.getLsbD 8 then true else true))) else (bif g.getLsbD 12 then (bif g.getLsbD 11 then (bif g.getLsbD 9 then true else true) else (bif g.getLsbD 9 then true else true)) else (bif g.getLsbD 9 then (bif g.getLsbD 8 then true else (bif g.getLsbD 7 then true else true)) else (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else true))))) else (bif g.getLsbD 17 then (bif g.getLsbD 13 then (bif g.getLsbD 11 then (bif g.getLsbD 9 then true else true) else (bif g.getLsbD 9 then true else true)) else (bif g.getLsbD 7 then true else true)) else (bif g.getLsbD 16 then (bif g.getLsbD 14 then (bif g.getLsbD 13 then true else true) else (bif g.getLsbD 13 then (bif g.getLsbD 12 then (bif g.getLsbD 9 then true else true) else (bif g.getLsbD 11 then (bif g.getLsbD 9 then true else true) else (bif g.getLsbD 9 then (bif g.getLsbD 8 then true else (bif g.getLsbD 7 then true else true)) else (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else true)))) else (bif g.getLsbD 12 then (bif g.getLsbD 11 then true else (bif g.getLsbD 7 then true else true)) else (bif g.getLsbD 8 then true else true)))) else (bif g.getLsbD 14 then (bif g.getLsbD 13 then true else true) else (bif g.getLsbD 13 then (bif g.getLsbD 12 then (bif g.getLsbD 9 then true else true) else (bif g.getLsbD 11 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then true else (bif g.getLsbD 7 then true else true)) else (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else true)) else (bif g.getLsbD 9 then true else true))) else (bif g.getLsbD 12 then (bif g.getLsbD 11 then (bif g.getLsbD 7 then true else true) else true) else (bif g.getLsbD 8 then true else true))))))) else (bif g.getLsbD 18 then (bif g.getLsbD 17 then (bif g.getLsbD 14 then (bif g.getLsbD 13 then true else (bif g.getLsbD 11 then (bif g.getLsbD 9 then true else true) else (bif g.getLsbD 9 then true else true))) else (bif g.getLsbD 13 then (bif g.getLsbD 11 then (bif g.getLsbD 9 then true else true) else (bif g.getLsbD 9 then true else true)) else (bif g.getLsbD 12 then (bif g.getLsbD 11 then true else true) else (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true)) else true)))) else (bif g.getLsbD 16 then (bif g.getLsbD 14 then (bif g.getLsbD 13 then (bif g.getLsbD 8 then true else true) else (bif g.getLsbD 12 then (bif g.getLsbD 9 then true else true) else (bif g.getLsbD 11 then (bif g.getLsbD 9 then true else true) else (bif g.getLsbD 9 then (bif g.getLsbD 8 then true else (bif g.getLsbD 7 then true else true)) else (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else true))))) else (bif g.getLsbD 13 then (bif g.getLsbD 12 then (bif g.getLsbD 9 then true else true) else (bif g.getLsbD 11 then (bif g.getLsbD 9 then true else true) else (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else true) else (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true)))) else (bif g.getLsbD 12 then (bif g.getLsbD 11 then (bif g.getLsbD 8 then true else true) else (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true)) else true)) else (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true)) else true) else true)))) else (bif g.getLsbD 14 then (bif g.getLsbD 13 then (bif g.getLsbD 8 then true else true) else (bif g.getLsbD 12 then (bif g.getLsbD 9 then true else true) else (bif g.getLsbD 11 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then true else (bif g.getLsbD 7 then true else true)) else (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else true)) else (bif g.getLsbD 9 then true else true)))) else (bif g.getLsbD 13 then (bif g.getLsbD 12 then (bif g.getLsbD 9 then true else true) else (bif g.getLsbD 11 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else true) else (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true)) else (bif g.getLsbD 9 then true else true))) else (bif g.getLsbD 12 then (bif g.getLsbD 11 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true)) else true) else (bif g.getLsbD 8 then true else true)) else (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true) else true) else true) else true)))))) else (bif g.getLsbD 17 then (bif g.getLsbD 16 then (bif g.getLsbD 14 then (bif g.getLsbD 13 then (bif g.getLsbD 9 then true else true) else (bif g.getLsbD 11 then true else (bif g.getLsbD 7 then true else true))) else (bif g.getLsbD 13 then (bif g.getLsbD 12 then true else (bif g.getLsbD 11 then (bif g.getLsbD 8 then true else true) else (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true)) else true))) else (bif g.getLsbD 12 then true else (bif g.getLsbD 8 then true else true)))) else (bif g.getLsbD 14 then (bif g.getLsbD 13 then (bif g.getLsbD 9 then true else true) else (bif g.getLsbD 11 then (bif g.getLsbD 7 then true else true) else true)) else (bif g.getLsbD 13 then (bif g.getLsbD 12 then true else (bif g.getLsbD 11 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true)) else true) else (bif g.getLsbD 8 then true else true))) else (bif g.getLsbD 12 then true else (bif g.getLsbD 8 then true else true))))) else (bif g.getLsbD 14 then (bif g.getLsbD 13 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then true else (bif g.getLsbD 7 then true else true)) else (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else true)) else (bif g.getLsbD 12 then (bif g.getLsbD 7 then true else true) else (bif g.getLsbD 11 then (bif g.getLsbD 8 then true else true) else (bif g.getLsbD 8 then true else true)))) else (bif g.getLsbD 13 then (bif g.getLsbD 12 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true)) else true) else (bif g.getLsbD 11 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true)) else true) else true) else (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true) else true) else true) else true))) else (bif g.getLsbD 12 then (bif g.getLsbD 11 then (bif g.getLsbD 8 then true else true) else (bif g.getLsbD 8 then true else true)) else (bif g.getLsbD 7 then true else true)))))))) else (bif g.getLsbD 22 then (bif g.getLsbD 20 then (bif g.getLsbD 19 then (bif g.getLsbD 13 then true else (bif g.getLsbD 12 then true else true)) else (bif g.getLsbD 18 then (bif g.getLsbD 14 then true else (bif g.getLsbD 13 then true else (bif g.getLsbD 12 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then true else true) else true) else (bif g.getLsbD 11 then true else (bif g.getLsbD 9 then (bif g.getLsbD 7 then true else true) else true))))) else (bif g.getLsbD 17 then (bif g.getLsbD 14 then true else (bif g.getLsbD 13 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then true else true) else true) else (bif g.getLsbD 12 then true else (bif g.getLsbD 11 then true else (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else true))))) else (bif g.getLsbD 16 then (bif g.getLsbD 13 then true else (bif g.getLsbD 12 then true else true)) else (bif g.getLsbD 14 then true else (bif g.getLsbD 13 then (bif g.getLsbD 9 then (bif g.getLsbD 7 then true else true) else true) else (bif g.getLsbD 12 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else true) else (bif g.getLsbD 11 then true else true)))))))) else (bif g.getLsbD 19 then (bif g.getLsbD 18 then (bif g.getLsbD 14 then (bif g.getLsbD 12 then true else true) else (bif g.getLsbD 13 then (bif g.getLsbD 12 then (bif g.getLsbD 8 then true else true) else (bif g.getLsbD 11 then true else (bif g.getLsbD 7 then true else true))) else (bif g.getLsbD 12 then (bif g.getLsbD 11 then (bif g.getLsbD 9 then true else true) else (bif g.getLsbD 9 then (bif g.getLsbD 8 then true else (bif g.getLsbD 7 then true else true)) else (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else true))) else (bif g.getLsbD 9 then true else true)))) else (bif g.getLsbD 17 then (bif g.getLsbD 14 then (bif g.getLsbD 13 then true else true) else (bif g.getLsbD 13 then (bif g.getLsbD 12 then (bif g.getLsbD 9 then true else true) else (bif g.getLsbD 11 then (bif g.getLsbD 9 then true else true) else (bif g.getLsbD 9 then (bif g.getLsbD 8 then true else (bif g.getLsbD 7 then true else true)) else (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else true)))) else (bif g.getLsbD 12 then (bif g.getLsbD 11 then true else (bif g.getLsbD 7 then true else true)) else (bif g.getLsbD 8 then true else true)))) else (bif g.getLsbD 16 then (bif g.getLsbD 13 then (bif g.getLsbD 12 then (bif g.getLsbD 9 then true else true) else (bif g.getLsbD 9 then true else true)) else (bif g.getLsbD 8 then true else true)) else (bif g.getLsbD 14 then (bif g.getLsbD 13 then true else true) else (bif g.getLsbD 13 then (bif g.getLsbD 12 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then true else (bif g.getLsbD 7 then true else true)) else (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else true)) else (bif g.getLsbD 11 then (bif g.getLsbD 9 then true else true) else (bif g.getLsbD 9 then true else true))) else (bif g.getLsbD 12 then (bif g.getLsbD 11 then (bif g.getLsbD 8 then true else true) else (bif g.getLsbD 8 then true else true)) else true)))))) else (bif g.getLsbD 18 then (bif g.getLsbD 17 then (bif g.getLsbD 14 then (bif g.getLsbD 13 then (bif g.getLsbD 8 then true else true) else (bif g.getLsbD 12 then (bif g.getLsbD 9 then true else true) else (bif g.getLsbD 11 then (bif g.getLsbD 9 then true else true) else (bif g.getLsbD 9 then (bif g.getLsbD 8 then true else (bif g.getLsbD 7 then true else true)) else (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else true))))) else (bif g.getLsbD 13 then (bif g.getLsbD 12 then (bif g.getLsbD 9 then true else true) else (bif g.getLsbD 11 then (bif g.getLsbD 9 then true else true) else (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else true) else (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true)))) else (bif g.getLsbD 12 then (bif g.getLsbD 11 then (bif g.getLsbD 8 then true else true) else (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true)) else true)) else (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true)) else true) else true)))) else (bif g.getLsbD 16 then (bif g.getLsbD 14 then (bif g.getLsbD 13 then true else (bif g.getLsbD 12 then (bif g.getLsbD 9 then true else true) else (bif g.getLsbD 9 then true else true))) else (bif g.getLsbD 13 then (bif g.getLsbD 12 then (bif g.getLsbD 9 then true else true) else (bif g.getLsbD 9 then true else true)) else (bif g.getLsbD 12 then (bif g.getLsbD 11 then true else (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true)) else true) else true)) else true))) else (bif g.getLsbD 14 then (bif g.getLsbD 13 then (bif g.getLsbD 7 then true else true) else (bif g.getLsbD 12 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then true else (bif g.getLsbD 7 then true else true)) else (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else true)) else (bif g.getLsbD 11 then (bif g.getLsbD 9 then true else true) else (bif g.getLsbD 9 then true else true)))) else (bif g.getLsbD 13 then (bif g.getLsbD 12 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else true) else (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true)) else (bif g.getLsbD 11 then (bif g.getLsbD 9 then true else true) else (bif g.getLsbD 9 then true else true))) else (bif g.getLsbD 12 then (bif g.getLsbD 11 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true)) else true) else true) else (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true) else true) else true) else true)) else (bif g.getLsbD 7 then true else true)))))) else (bif g.getLsbD 17 then (bif g.getLsbD 16 then (bif g.getLsbD 14 then (bif g.getLsbD 13 then (bif g.getLsbD 9 then true else true) else (bif g.getLsbD 12 then true else (bif g.getLsbD 8 then true else true))) else (bif g.getLsbD 13 then (bif g.getLsbD 12 then (bif g.getLsbD 8 then true else true) else (bif g.getLsbD 11 then true else (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true)) else true) else true))) else (bif g.getLsbD 12 then (bif g.getLsbD 8 then true else true) else true))) else (bif g.getLsbD 14 then (bif g.getLsbD 13 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then true else (bif g.getLsbD 7 then true else true)) else (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else true)) else (bif g.getLsbD 12 then (bif g.getLsbD 7 then true else true) else (bif g.getLsbD 11 then (bif g.getLsbD 8 then true else true) else (bif g.getLsbD 8 then true else true)))) else (bif g.getLsbD 13 then (bif g.getLsbD 12 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true)) else true) else (bif g.getLsbD 11 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true)) else true) else true) else (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true) else true) else true) else true))) else (bif g.getLsbD 12 then (bif g.getLsbD 11 then (bif g.getLsbD 8 then true else true) else (bif g.getLsbD 8 then true else true)) else (bif g.getLsbD 7 then true else true))))) else (bif g.getLsbD 14 then (bif g.getLsbD 13 then (bif g.getLsbD 9 then true else true) else (bif g.getLsbD 12 then (bif g.getLsbD 8 then true else true) else true)) else (bif g.getLsbD 13 then (bif g.getLsbD 12 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true)) else true) else true) else (bif g.getLsbD 11 then true else (bif g.getLsbD 7 then true else true))) else (bif g.getLsbD 11 then true else (bif g.getLsbD 7 then true else true)))))))) else (bif g.getLsbD 20 then (bif g.getLsbD 19 then (bif g.getLsbD 13 then true else (bif g.getLsbD 12 then true else true)) else (bif g.getLsbD 18 then (bif g.getLsbD 14 then true else (bif g.getLsbD 13 then true else (bif g.getLsbD 12 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then true else true) else true) else (bif g.getLsbD 11 then (bif g.getLsbD 9 then (bif g.getLsbD 7 then true else true) else true) else true)))) else (bif g.getLsbD 17 then (bif g.getLsbD 14 then true else (bif g.getLsbD 13 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then true else true) else true) else (bif g.getLsbD 12 then true else (bif g.getLsbD 11 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else true) else true)))) else (bif g.getLsbD 16 then (bif g.getLsbD 14 then true else (bif g.getLsbD 13 then (bif g.getLsbD 9 then (bif g.getLsbD 7 then true else true) else true) else (bif g.getLsbD 12 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else true) else (bif g.getLsbD 11 then true else true)))) else (bif g.getLsbD 13 then true else (bif g.getLsbD 12 then true else true)))))) else (bif g.getLsbD 19 then (bif g.getLsbD 18 then (bif g.getLsbD 14 then (bif g.getLsbD 12 then true else true) else (bif g.getLsbD 13 then (bif g.getLsbD 12 then (bif g.getLsbD 8 then true else true) else (bif g.getLsbD 11 then (bif g.getLsbD 7 then true else true) else true)) else (bif g.getLsbD 12 then (bif g.getLsbD 11 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then true else (bif g.getLsbD 7 then true else true)) else (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else true)) else (bif g.getLsbD 9 then true else true)) else (bif g.getLsbD 9 then true else true)))) else (bif g.getLsbD 17 then (bif g.getLsbD 14 then (bif g.getLsbD 13 then true else true) else (bif g.getLsbD 13 then (bif g.getLsbD 12 then (bif g.getLsbD 9 then true else true) else (bif g.getLsbD 11 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then true else (bif g.getLsbD 7 then true else true)) else (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else true)) else (bif g.getLsbD 9 then true else true))) else (bif g.getLsbD 12 then (bif g.getLsbD 11 then (bif g.getLsbD 7 then true else true) else true) else (bif g.getLsbD 8 then true else true)))) else (bif g.getLsbD 16 then (bif g.getLsbD 14 then (bif g.getLsbD 13 then true else true) else (bif g.getLsbD 13 then (bif g.getLsbD 12 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then true else (bif g.getLsbD 7 then true else true)) else (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else true)) else (bif g.getLsbD 11 then (bif g.getLsbD 9 then true else true) else (bif g.getLsbD 9 then true else true))) else (bif g.getLsbD 12 then (bif g.getLsbD 11 then (bif g.getLsbD 8 then true else true) else (bif g.getLsbD 8 then true else true)) else true))) else (bif g.getLsbD 13 then (bif g.getLsbD 12 then (bif g.getLsbD 9 then true else true) else (bif g.getLsbD 9 then true else true)) else (bif g.getLsbD 8 then true else true))))) else (bif g.getLsbD 18 then (bif g.getLsbD 17 then (bif g.getLsbD 14 then (bif g.getLsbD 13 then (bif g.getLsbD 8 then true else true) else (bif g.getLsbD 12 then (bif g.getLsbD 9 then true else true) else (bif g.getLsbD 11 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then true else (bif g.getLsbD 7 then true else true)) else (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else true)) else (bif g.getLsbD 9 then true else true)))) else (bif g.getLsbD 13 then (bif g.getLsbD 12 then (bif g.getLsbD 9 then true else true) else (bif g.getLsbD 11 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else true) else (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true)) else (bif g.getLsbD 9 then true else true))) else (bif g.getLsbD 12 then (bif g.getLsbD 11 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true)) else true) else (bif g.getLsbD 8 then true else true)) else (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true) else true) else true) else true)))) else (bif g.getLsbD 16 then (bif g.getLsbD 14 then (bif g.getLsbD 13 then (bif g.getLsbD 7 then true else true) else (bif g.getLsbD 12 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then true else (bif g.getLsbD 7 then true else true)) else (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else true)) else (bif g.getLsbD 11 then (bif g.getLsbD 9 then true else true) else (bif g.getLsbD 9 then true else true)))) else (bif g.getLsbD 13 then (bif g.getLsbD 12 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else true) else (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true)) else (bif g.getLsbD 11 then (bif g.getLsbD 9 then true else true) else (bif g.getLsbD 9 then true else true))) else (bif g.getLsbD 12 then (bif g.getLsbD 11 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true)) else true) else true) else (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true) else true) else true) else true)) else (bif g.getLsbD 7 then true else true)))) else (bif g.getLsbD 14 then (bif g.getLsbD 13 then true else (bif g.getLsbD 12 then (bif g.getLsbD 9 then true else true) else (bif g.getLsbD 9 then true else true))) else (bif g.getLsbD 13 then (bif g.getLsbD 12 then (bif g.getLsbD 9 then true else true) else (bif g.getLsbD 9 then true else true)) else (bif g.getLsbD 12 then (bif g.getLsbD 11 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true) else true) else true) else true) else true) else true))))) else (bif g.getLsbD 17 then (bif g.getLsbD 16 then (bif g.getLsbD 14 then (bif g.getLsbD 13 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then true else (bif g.getLsbD 7 then true else true)) else (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else true)) else (bif g.getLsbD 12 then (bif g.getLsbD 7 then true else true) else (bif g.getLsbD 11 then (bif g.getLsbD 8 then true else true) else (bif g.getLsbD 8 then true else true)))) else (bif g.getLsbD 13 then (bif g.getLsbD 12 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true)) else true) else (bif g.getLsbD 11 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true)) else true) else true) else (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true) else true) else true) else true))) else (bif g.getLsbD 12 then (bif g.getLsbD 11 then (bif g.getLsbD 8 then true else true) else (bif g.getLsbD 8 then true else true)) else (bif g.getLsbD 7 then true else true)))) else (bif g.getLsbD 14 then (bif g.getLsbD 13 then (bif g.getLsbD 9 then true else true) else (bif g.getLsbD 12 then true else (bif g.getLsbD 8 then true else true))) else (bif g.getLsbD 13 then (bif g.getLsbD 12 then (bif g.getLsbD 8 then true else true) else (bif g.getLsbD 11 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true) else true) else true) else true) else true)) else (bif g.getLsbD 12 then (bif g.getLsbD 8 then true else true) else true)))) else (bif g.getLsbD 14 then (bif g.getLsbD 13 then (bif g.getLsbD 9 then true else true) else (bif g.getLsbD 12 then (bif g.getLsbD 8 then true else true) else true)) else (bif g.getLsbD 13 then (bif g.getLsbD 12 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true) else true) else true) else true) else (bif g.getLsbD 11 then (bif g.getLsbD 7 then true else true) else true)) else (bif g.getLsbD 11 then (bif g.getLsbD 7 then true else true) else true)))))))))) else (bif g.getLsbD 24 then (bif g.getLsbD 23 then (bif g.getLsbD 20 then (bif g.getLsbD 19 then (bif g.getLsbD 14 then true else (bif g.getLsbD 13 then true else (bif g.getLsbD 12 then true else (bif g.getLsbD 11 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then true else true) else true) else (bif g.getLsbD 9 then (bif g.getLsbD 8 then true else true) else true))))) else (bif g.getLsbD 18 then (bif g.getLsbD 14 then true else (bif g.getLsbD 11 then true else true)) else (bif g.getLsbD 17 then (bif g.getLsbD 14 then true else (bif g.getLsbD 11 then true else true)) else (bif g.getLsbD 16 then (bif g.getLsbD 14 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then true else true) else true) else (bif g.getLsbD 13 then true else (bif g.getLsbD 12 then true else (bif g.getLsbD 11 then true else (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true))))) else (bif g.getLsbD 14 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then true else true) else true) else (bif g.getLsbD 13 then true else (bif g.getLsbD 12 then true else (bif g.getLsbD 11 then (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true) else true)))))))) else (bif g.getLsbD 19 then (bif g.getLsbD 18 then (bif g.getLsbD 14 then (bif g.getLsbD 12 then true else (bif g.getLsbD 11 then (bif g.getLsbD 8 then true else true) else (bif g.getLsbD 8 then true else true))) else (bif g.getLsbD 13 then (bif g.getLsbD 11 then true else true) else (bif g.getLsbD 12 then (bif g.getLsbD 11 then (bif g.getLsbD 9 then true else true) else (bif g.getLsbD 9 then true else true)) else (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else true) else (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true))))) else (bif g.getLsbD 17 then (bif g.getLsbD 14 then (bif g.getLsbD 13 then true else (bif g.getLsbD 11 then (bif g.getLsbD 9 then true else true) else (bif g.getLsbD 9 then true else true))) else (bif g.getLsbD 13 then (bif g.getLsbD 11 then (bif g.getLsbD 9 then true else true) else (bif g.getLsbD 9 then true else true)) else (bif g.getLsbD 12 then (bif g.getLsbD 11 then true else true) else (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true)) else true)))) else (bif g.getLsbD 16 then (bif g.getLsbD 14 then (bif g.getLsbD 13 then (bif g.getLsbD 8 then true else true) else (bif g.getLsbD 12 then (bif g.getLsbD 9 then true else true) else (bif g.getLsbD 11 then (bif g.getLsbD 9 then true else true) else (bif g.getLsbD 9 then (bif g.getLsbD 8 then true else (bif g.getLsbD 7 then true else true)) else (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else true))))) else (bif g.getLsbD 13 then (bif g.getLsbD 12 then (bif g.getLsbD 9 then true else true) else (bif g.getLsbD 11 then (bif g.getLsbD 9 then true else true) else (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else true) else (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true)))) else (bif g.getLsbD 12 then (bif g.getLsbD 11 then (bif g.getLsbD 8 then true else true) else (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true)) else true)) else (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true)) else true) else true)))) else (bif g.getLsbD 14 then (bif g.getLsbD 13 then (bif g.getLsbD 8 then true else true) else (bif g.getLsbD 12 then (bif g.getLsbD 9 then true else true) else (bif g.getLsbD 11 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then true else (bif g.getLsbD 7 then true else true)) else (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else true)) else (bif g.getLsbD 9 then true else true)))) else (bif g.getLsbD 13 then (bif g.getLsbD 12 then (bif g.getLsbD 9 then true else true) else (bif g.getLsbD 11 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else true) else (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true)) else (bif g.getLsbD 9 then true else true))) else (bif g.getLsbD 12 then (bif g.getLsbD 11 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true)) else true) else (bif g.getLsbD 8 then true else true)) else (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true) else true) else true) else true))))))) else (bif g.getLsbD 18 then (bif g.getLsbD 17 then (bif g.getLsbD 14 then (bif g.getLsbD 11 then (bif g.getLsbD 9 then true else true) else (bif g.getLsbD 9 then true else true)) else (bif g.getLsbD 4 then true else true)) else (bif g.getLsbD 16 then (bif g.getLsbD 14 then (bif g.getLsbD 13 then true else (bif g.getLsbD 12 then (bif g.getLsbD 9 then true else true) else (bif g.getLsbD 11 then (bif g.getLsbD 9 then true else true) else (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else true) else (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true))))) else (bif g.getLsbD 13 then true else (bif g.getLsbD 12 then (bif g.getLsbD 11 then true else (bif g.getLsbD 4 then true else true)) else (bif g.getLsbD 5 then true else true)))) else (bif g.getLsbD 14 then (bif g.getLsbD 13 then true else (bif g.getLsbD 12 then (bif g.getLsbD 9 then true else true) else (bif g.getLsbD 11 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else true) else (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true)) else (bif g.getLsbD 9 then true else true)))) else (bif g.getLsbD 13 then true else (bif g.getLsbD 12 then (bif g.getLsbD 11 then (bif g.getLsbD 4 then true else true) else true) else (bif g.getLsbD 5 then true else true)))))) else (bif g.getLsbD 17 then (bif g.getLsbD 16 then (bif g.getLsbD 14 then (bif g.getLsbD 13 then (bif g.getLsbD 9 then true else true) else (bif g.getLsbD 12 then true else (bif g.getLsbD 11 then (bif g.getLsbD 8 then true else true) else (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true)) else true)))) else (bif g.getLsbD 13 then (bif g.getLsbD 11 then true else (bif g.getLsbD 4 then true else true)) else (bif g.getLsbD 12 then true else (bif g.getLsbD 5 then true else true)))) else (bif g.getLsbD 14 then (bif g.getLsbD 13 then (bif g.getLsbD 9 then true else true) else (bif g.getLsbD 12 then true else (bif g.getLsbD 11 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true)) else true) else (bif g.getLsbD 8 then true else true)))) else (bif g.getLsbD 13 then (bif g.getLsbD 11 then (bif g.getLsbD 4 then true else true) else true) else (bif g.getLsbD 12 then true else (bif g.getLsbD 5 then true else true))))) else (bif g.getLsbD 14 then (bif g.getLsbD 13 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else true) else (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true)) else (bif g.getLsbD 12 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true)) else true) else (bif g.getLsbD 11 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true)) else true) else true) else (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true) else true) else true) else true)))) else (bif g.getLsbD 13 then (bif g.getLsbD 12 then (bif g.getLsbD 4 then true else true) else (bif g.getLsbD 11 then (bif g.getLsbD 5 then true else true) else (bif g.getLsbD 5 then true else true))) else (bif g.getLsbD 12 then (bif g.getLsbD 11 then (bif g.getLsbD 5 then true else true) else (bif g.getLsbD 5 then true else true)) else (bif g.getLsbD 4 then true else true)))))))) else (bif g.getLsbD 22 then (bif g.getLsbD 20 then (bif g.getLsbD 19 then (bif g.getLsbD 14 then true else (bif g.getLsbD 13 then true else (bif g.getLsbD 12 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then true else true) else true) else (bif g.getLsbD 11 then true else (bif g.getLsbD 9 then (bif g.getLsbD 7 then true else true) else true))))) else (bif g.getLsbD 18 then (bif g.getLsbD 14 then true else (bif g.getLsbD 12 then true else true)) else (bif g.getLsbD 17 then (bif g.getLsbD 14 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then true else true) else true) else (bif g.getLsbD 13 then true else (bif g.getLsbD 12 then true else (bif g.getLsbD 11 then true else (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true))))) else (bif g.getLsbD 16 then (bif g.getLsbD 14 then true else (bif g.getLsbD 12 then true else true)) else (bif g.getLsbD 14 then (bif g.getLsbD 9 then (bif g.getLsbD 7 then true else true) else true) else (bif g.getLsbD 13 then true else (bif g.getLsbD 12 then (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true) else (bif g.getLsbD 11 then true else true)))))))) else (bif g.getLsbD 19 then (bif g.getLsbD 18 then (bif g.getLsbD 14 then (bif g.getLsbD 12 then (bif g.getLsbD 8 then true else true) else (bif g.getLsbD 11 then true else (bif g.getLsbD 7 then true else true))) else (bif g.getLsbD 13 then (bif g.getLsbD 12 then true else true) else (bif g.getLsbD 12 then (bif g.getLsbD 11 then (bif g.getLsbD 9 then true else true) else (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else true) else (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true))) else (bif g.getLsbD 9 then true else true)))) else (bif g.getLsbD 17 then (bif g.getLsbD 14 then (bif g.getLsbD 13 then (bif g.getLsbD 8 then true else true) else (bif g.getLsbD 12 then (bif g.getLsbD 9 then true else true) else (bif g.getLsbD 11 then (bif g.getLsbD 9 then true else true) else (bif g.getLsbD 9 then (bif g.getLsbD 8 then true else (bif g.getLsbD 7 then true else true)) else (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else true))))) else (bif g.getLsbD 13 then (bif g.getLsbD 12 then (bif g.getLsbD 9 then true else true) else (bif g.getLsbD 11 then (bif g.getLsbD 9 then true else true) else (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else true) else (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true)))) else (bif g.getLsbD 12 then (bif g.getLsbD 11 then (bif g.getLsbD 8 then true else true) else (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true)) else true)) else (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true)) else true) else true)))) else (bif g.getLsbD 16 then (bif g.getLsbD 14 then (bif g.getLsbD 13 then true else (bif g.getLsbD 12 then (bif g.getLsbD 9 then true else true) else (bif g.getLsbD 9 then true else true))) else (bif g.getLsbD 13 then (bif g.getLsbD 12 then (bif g.getLsbD 9 then true else true) else (bif g.getLsbD 9 then true else true)) else (bif g.getLsbD 12 then (bif g.getLsbD 11 then true else (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true)) else true) else true)) else true))) else (bif g.getLsbD 14 then (bif g.getLsbD 13 then (bif g.getLsbD 7 then true else true) else (bif g.getLsbD 12 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then true else (bif g.getLsbD 7 then true else true)) else (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else true)) else (bif g.getLsbD 11 then (bif g.getLsbD 9 then true else true) else (bif g.getLsbD 9 then true else true)))) else (bif g.getLsbD 13 then (bif g.getLsbD 12 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else true) else (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true)) else (bif g.getLsbD 11 then (bif g.getLsbD 9 then true else true) else (bif g.getLsbD 9 then true else true))) else (bif g.getLsbD 12 then (bif g.getLsbD 11 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true)) else true) else true) else (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true) else true) else true) else true)) else (bif g.getLsbD 7 then true else true))))))) else (bif g.getLsbD 18 then (bif g.getLsbD 17 then (bif g.getLsbD 14 then (bif g.getLsbD 13 then true else (bif g.getLsbD 12 then (bif g.getLsbD 9 then true else true) else (bif g.getLsbD 11 then (bif g.getLsbD 9 then true else true) else (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else true) else (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true))))) else (bif g.getLsbD 13 then true else (bif g.getLsbD 12 then (bif g.getLsbD 11 then true else (bif g.getLsbD 4 then true else true)) else (bif g.getLsbD 5 then true else true)))) else (bif g.getLsbD 16 then (bif g.getLsbD 14 then (bif g.getLsbD 12 then (bif g.getLsbD 9 then true else true) else (bif g.getLsbD 9 then true else true)) else (bif g.getLsbD 5 then true else true)) else (bif g.getLsbD 14 then (bif g.getLsbD 13 then true else (bif g.getLsbD 12 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else true) else (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true)) else (bif g.getLsbD 11 then (bif g.getLsbD 9 then true else true) else (bif g.getLsbD 9 then true else true)))) else (bif g.getLsbD 13 then true else (bif g.getLsbD 12 then (bif g.getLsbD 11 then (bif g.getLsbD 5 then true else true) else (bif g.getLsbD 5 then true else true)) else true))))) else (bif g.getLsbD 17 then (bif g.getLsbD 16 then (bif g.getLsbD 14 then (bif g.getLsbD 13 then (bif g.getLsbD 9 then true else true) else (bif g.getLsbD 12 then (bif g.getLsbD 8 then true else true) else (bif g.getLsbD 11 then true else (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true)) else true) else true)))) else (bif g.getLsbD 13 then (bif g.getLsbD 12 then true else (bif g.getLsbD 5 then true else true)) else (bif g.getLsbD 12 then (bif g.getLsbD 5 then true else true) else true))) else (bif g.getLsbD 14 then (bif g.getLsbD 13 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else true) else (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true)) else (bif g.getLsbD 12 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true)) else true) else (bif g.getLsbD 11 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true)) else true) else true) else (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true) else true) else true) else true)))) else (bif g.getLsbD 13 then (bif g.getLsbD 12 then (bif g.getLsbD 4 then true else true) else (bif g.getLsbD 11 then (bif g.getLsbD 5 then true else true) else (bif g.getLsbD 5 then true else true))) else (bif g.getLsbD 12 then (bif g.getLsbD 11 then (bif g.getLsbD 5 then true else true) else (bif g.getLsbD 5 then true else true)) else (bif g.getLsbD 4 then true else true))))) else (bif g.getLsbD 14 then (bif g.getLsbD 13 then (bif g.getLsbD 9 then true else true) else (bif g.getLsbD 12 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true)) else true) else true) else (bif g.getLsbD 11 then true else (bif g.getLsbD 7 then true else true)))) else (bif g.getLsbD 13 then (bif g.getLsbD 12 then (bif g.getLsbD 5 then true else true) else true) else (bif g.getLsbD 11 then true else (bif g.getLsbD 4 then true else true)))))))) else (bif g.getLsbD 20 then (bif g.getLsbD 19 then (bif g.getLsbD 14 then true else (bif g.getLsbD 13 then true else (bif g.getLsbD 12 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then true else true) else true) else (bif g.getLsbD 11 then (bif g.getLsbD 9 then (bif g.getLsbD 7 then true else true) else true) else true)))) else (bif g.getLsbD 18 then (bif g.getLsbD 14 then true else (bif g.getLsbD 12 then true else true)) else (bif g.getLsbD 17 then (bif g.getLsbD 14 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then true else true) else true) else (bif g.getLsbD 13 then true else (bif g.getLsbD 12 then true else (bif g.getLsbD 11 then (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true) else true)))) else (bif g.getLsbD 16 then (bif g.getLsbD 14 then (bif g.getLsbD 9 then (bif g.getLsbD 7 then true else true) else true) else (bif g.getLsbD 13 then true else (bif g.getLsbD 12 then (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true) else (bif g.getLsbD 11 then true else true)))) else (bif g.getLsbD 14 then true else (bif g.getLsbD 12 then true else true)))))) else (bif g.getLsbD 19 then (bif g.getLsbD 18 then (bif g.getLsbD 14 then (bif g.getLsbD 12 then (bif g.getLsbD 8 then true else true) else (bif g.getLsbD 11 then (bif g.getLsbD 7 then true else true) else true)) else (bif g.getLsbD 13 then (bif g.getLsbD 12 then true else true) else (bif g.getLsbD 12 then (bif g.getLsbD 11 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else true) else (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true)) else (bif g.getLsbD 9 then true else true)) else (bif g.getLsbD 9 then true else true)))) else (bif g.getLsbD 17 then (bif g.getLsbD 14 then (bif g.getLsbD 13 then (bif g.getLsbD 8 then true else true) else (bif g.getLsbD 12 then (bif g.getLsbD 9 then true else true) else (bif g.getLsbD 11 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then true else (bif g.getLsbD 7 then true else true)) else (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else true)) else (bif g.getLsbD 9 then true else true)))) else (bif g.getLsbD 13 then (bif g.getLsbD 12 then (bif g.getLsbD 9 then true else true) else (bif g.getLsbD 11 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else true) else (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true)) else (bif g.getLsbD 9 then true else true))) else (bif g.getLsbD 12 then (bif g.getLsbD 11 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true)) else true) else (bif g.getLsbD 8 then true else true)) else (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true) else true) else true) else true)))) else (bif g.getLsbD 16 then (bif g.getLsbD 14 then (bif g.getLsbD 13 then (bif g.getLsbD 7 then true else true) else (bif g.getLsbD 12 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then true else (bif g.getLsbD 7 then true else true)) else (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else true)) else (bif g.getLsbD 11 then (bif g.getLsbD 9 then true else true) else (bif g.getLsbD 9 then true else true)))) else (bif g.getLsbD 13 then (bif g.getLsbD 12 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else true) else (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true)) else (bif g.getLsbD 11 then (bif g.getLsbD 9 then true else true) else (bif g.getLsbD 9 then true else true))) else (bif g.getLsbD 12 then (bif g.getLsbD 11 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true)) else true) else true) else (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true) else true) else true) else true)) else (bif g.getLsbD 7 then true else true)))) else (bif g.getLsbD 14 then (bif g.getLsbD 13 then true else (bif g.getLsbD 12 then (bif g.getLsbD 9 then true else true) else (bif g.getLsbD 9 then true else true))) else (bif g.getLsbD 13 then (bif g.getLsbD 12 then (bif g.getLsbD 9 then true else true) else (bif g.getLsbD 9 then true else true)) else (bif g.getLsbD 12 then (bif g.getLsbD 11 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true) else true) else true) else true) else true) else true)))))) else (bif g.getLsbD 18 then (bif g.getLsbD 17 then (bif g.getLsbD 14 then (bif g.getLsbD 13 then true else (bif g.getLsbD 12 then (bif g.getLsbD 9 then true else true) else (bif g.getLsbD 11 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else true) else (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true)) else (bif g.getLsbD 9 then true else true)))) else (bif g.getLsbD 13 then true else (bif g.getLsbD 12 then (bif g.getLsbD 11 then (bif g.getLsbD 4 then true else true) else true) else (bif g.getLsbD 5 then true else true)))) else (bif g.getLsbD 16 then (bif g.getLsbD 14 then (bif g.getLsbD 13 then true else (bif g.getLsbD 12 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else true) else (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true)) else (bif g.getLsbD 11 then (bif g.getLsbD 9 then true else true) else (bif g.getLsbD 9 then true else true)))) else (bif g.getLsbD 13 then true else (bif g.getLsbD 12 then (bif g.getLsbD 11 then (bif g.getLsbD 5 then true else true) else (bif g.getLsbD 5 then true else true)) else true))) else (bif g.getLsbD 14 then (bif g.getLsbD 12 then (bif g.getLsbD 9 then true else true) else (bif g.getLsbD 9 then true else true)) else (bif g.getLsbD 5 then true else true)))) else (bif g.getLsbD 17 then (bif g.getLsbD 16 then (bif g.getLsbD 14 then (bif g.getLsbD 13 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else true) else (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true)) else (bif g.getLsbD 12 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true)) else true) else (bif g.getLsbD 11 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true)) else true) else true) else (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true) else true) else true) else true)))) else (bif g.getLsbD 13 then (bif g.getLsbD 12 then (bif g.getLsbD 4 then true else true) else (bif g.getLsbD 11 then (bif g.getLsbD 5 then true else true) else (bif g.getLsbD 5 then true else true))) else (bif g.getLsbD 12 then (bif g.getLsbD 11 then (bif g.getLsbD 5 then true else true) else (bif g.getLsbD 5 then true else true)) else (bif g.getLsbD 4 then true else true)))) else (bif g.getLsbD 14 then (bif g.getLsbD 13 then (bif g.getLsbD 9 then true else true) else (bif g.getLsbD 12 then (bif g.getLsbD 8 then true else true) else (bif g.getLsbD 11 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true) else true) else true) else true) else true))) else (bif g.getLsbD 13 then (bif g.getLsbD 12 then true else (bif g.getLsbD 5 then true else true)) else (bif g.getLsbD 12 then (bif g.getLsbD 5 then true else true) else true)))) else (bif g.getLsbD 14 then (bif g.getLsbD 13 then (bif g.getLsbD 9 then true else true) else (bif g.getLsbD 12 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true) else true) else true) else true) else (bif g.getLsbD 11 then (bif g.getLsbD 7 then true else true) else true))) else (bif g.getLsbD 13 then (bif g.getLsbD 12 then (bif g.getLsbD 5 then true else true) else true) else (bif g.getLsbD 11 then (bif g.getLsbD 4 then true else true) else true))))))))) else (bif g.getLsbD 23 then (bif g.getLsbD 22 then (bif g.getLsbD 20 then (bif g.getLsbD 19 then (bif g.getLsbD 14 then true else (bif g.getLsbD 13 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then true else true) else true) else (bif g.getLsbD 12 then true else (bif g.getLsbD 11 then true else (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else true))))) else (bif g.getLsbD 18 then (bif g.getLsbD 14 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then true else true) else true) else (bif g.getLsbD 13 then true else (bif g.getLsbD 12 then true else (bif g.getLsbD 11 then true else (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true))))) else (bif g.getLsbD 17 then (bif g.getLsbD 14 then true else (bif g.getLsbD 13 then true else true)) else (bif g.getLsbD 16 then (bif g.getLsbD 14 then true else (bif g.getLsbD 13 then true else true)) else (bif g.getLsbD 14 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else true) else (bif g.getLsbD 13 then (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true) else (bif g.getLsbD 12 then true else (bif g.getLsbD 11 then true else true)))))))) else (bif g.getLsbD 19 then (bif g.getLsbD 18 then (bif g.getLsbD 14 then (bif g.getLsbD 13 then (bif g.getLsbD 8 then true else true) else (bif g.getLsbD 12 then (bif g.getLsbD 9 then true else true) else (bif g.getLsbD 11 then (bif g.getLsbD 9 then true else true) else (bif g.getLsbD 9 then (bif g.getLsbD 8 then true else (bif g.getLsbD 7 then true else true)) else (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else true))))) else (bif g.getLsbD 13 then (bif g.getLsbD 12 then (bif g.getLsbD 9 then true else true) else (bif g.getLsbD 11 then (bif g.getLsbD 9 then true else true) else (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else true) else (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true)))) else (bif g.getLsbD 12 then (bif g.getLsbD 11 then (bif g.getLsbD 8 then true else true) else (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true)) else true)) else (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true)) else true) else true)))) else (bif g.getLsbD 17 then (bif g.getLsbD 14 then (bif g.getLsbD 13 then (bif g.getLsbD 9 then true else true) else (bif g.getLsbD 11 then true else (bif g.getLsbD 7 then true else true))) else (bif g.getLsbD 13 then (bif g.getLsbD 12 then true else (bif g.getLsbD 11 then (bif g.getLsbD 8 then true else true) else (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true)) else true))) else (bif g.getLsbD 12 then true else (bif g.getLsbD 8 then true else true)))) else (bif g.getLsbD 16 then (bif g.getLsbD 14 then (bif g.getLsbD 13 then (bif g.getLsbD 9 then true else true) else (bif g.getLsbD 12 then true else (bif g.getLsbD 8 then true else true))) else (bif g.getLsbD 13 then (bif g.getLsbD 12 then (bif g.getLsbD 8 then true else true) else (bif g.getLsbD 11 then true else (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true)) else true) else true))) else (bif g.getLsbD 12 then (bif g.getLsbD 8 then true else true) else true))) else (bif g.getLsbD 14 then (bif g.getLsbD 13 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then true else (bif g.getLsbD 7 then true else true)) else (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else true)) else (bif g.getLsbD 12 then (bif g.getLsbD 7 then true else true) else (bif g.getLsbD 11 then (bif g.getLsbD 8 then true else true) else (bif g.getLsbD 8 then true else true)))) else (bif g.getLsbD 13 then (bif g.getLsbD 12 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true)) else true) else (bif g.getLsbD 11 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true)) else true) else true) else (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true) else true) else true) else true))) else (bif g.getLsbD 12 then (bif g.getLsbD 11 then (bif g.getLsbD 8 then true else true) else (bif g.getLsbD 8 then true else true)) else (bif g.getLsbD 7 then true else true))))))) else (bif g.getLsbD 18 then (bif g.getLsbD 17 then (bif g.getLsbD 14 then (bif g.getLsbD 13 then (bif g.getLsbD 9 then true else true) else (bif g.getLsbD 12 then true else (bif g.getLsbD 11 then (bif g.getLsbD 8 then true else true) else (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true)) else true)))) else (bif g.getLsbD 13 then (bif g.getLsbD 11 then true else (bif g.getLsbD 4 then true else true)) else (bif g.getLsbD 12 then true else (bif g.getLsbD 5 then true else true)))) else (bif g.getLsbD 16 then (bif g.getLsbD 14 then (bif g.getLsbD 13 then (bif g.getLsbD 9 then true else true) else (bif g.getLsbD 12 then (bif g.getLsbD 8 then true else true) else (bif g.getLsbD 11 then true else (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true)) else true) else true)))) else (bif g.getLsbD 13 then (bif g.getLsbD 12 then true else (bif g.getLsbD 5 then true else true)) else (bif g.getLsbD 12 then (bif g.getLsbD 5 then true else true) else true))) else (bif g.getLsbD 14 then (bif g.getLsbD 13 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else true) else (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true)) else (bif g.getLsbD 12 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true)) else true) else (bif g.getLsbD 11 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true)) else true) else true) else (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true) else true) else true) else true)))) else (bif g.getLsbD 13 then (bif g.getLsbD 12 then (bif g.getLsbD 4 then true else true) else (bif g.getLsbD 11 then (bif g.getLsbD 5 then true else true) else (bif g.getLsbD 5 then true else true))) else (bif g.getLsbD 12 then (bif g.getLsbD 11 then (bif g.getLsbD 5 then true else true) else (bif g.getLsbD 5 then true else true)) else (bif g.getLsbD 4 then true else true)))))) else (bif g.getLsbD 17 then (bif g.getLsbD 16 then (bif g.getLsbD 14 then (bif g.getLsbD 13 then (bif g.getLsbD 8 then true else true) else (bif g.getLsbD 8 then true else true)) else (bif g.getLsbD 5 then true else true)) else (bif g.getLsbD 14 then (bif g.getLsbD 13 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true)) else true) else (bif g.getLsbD 12 then true else (bif g.getLsbD 11 then (bif g.getLsbD 8 then true else true) else (bif g.getLsbD 8 then true else true)))) else (bif g.getLsbD 13 then (bif g.getLsbD 12 then true else (bif g.getLsbD 11 then (bif g.getLsbD 5 then true else true) else (bif g.getLsbD 5 then true else true))) else true))) else (bif g.getLsbD 14 then (bif g.getLsbD 13 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true)) else true) else true) else (bif g.getLsbD 12 then (bif g.getLsbD 8 then true else true) else (bif g.getLsbD 11 then true else (bif g.getLsbD 7 then true else true)))) else (bif g.getLsbD 13 then (bif g.getLsbD 12 then (bif g.getLsbD 5 then true else true) else (bif g.getLsbD 11 then true else (bif g.getLsbD 4 then true else true))) else true)))))) else (bif g.getLsbD 20 then (bif g.getLsbD 19 then (bif g.getLsbD 14 then true else (bif g.getLsbD 13 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then true else true) else true) else (bif g.getLsbD 12 then true else (bif g.getLsbD 11 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else true) else true)))) else (bif g.getLsbD 18 then (bif g.getLsbD 14 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then true else true) else true) else (bif g.getLsbD 13 then true else (bif g.getLsbD 12 then true else (bif g.getLsbD 11 then (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true) else true)))) else (bif g.getLsbD 17 then (bif g.getLsbD 14 then true else (bif g.getLsbD 13 then true else true)) else (bif g.getLsbD 16 then (bif g.getLsbD 14 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else true) else (bif g.getLsbD 13 then (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true) else (bif g.getLsbD 12 then true else (bif g.getLsbD 11 then true else true)))) else (bif g.getLsbD 14 then true else (bif g.getLsbD 13 then true else true)))))) else (bif g.getLsbD 19 then (bif g.getLsbD 18 then (bif g.getLsbD 14 then (bif g.getLsbD 13 then (bif g.getLsbD 8 then true else true) else (bif g.getLsbD 12 then (bif g.getLsbD 9 then true else true) else (bif g.getLsbD 11 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then true else (bif g.getLsbD 7 then true else true)) else (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else true)) else (bif g.getLsbD 9 then true else true)))) else (bif g.getLsbD 13 then (bif g.getLsbD 12 then (bif g.getLsbD 9 then true else true) else (bif g.getLsbD 11 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else true) else (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true)) else (bif g.getLsbD 9 then true else true))) else (bif g.getLsbD 12 then (bif g.getLsbD 11 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true)) else true) else (bif g.getLsbD 8 then true else true)) else (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true) else true) else true) else true)))) else (bif g.getLsbD 17 then (bif g.getLsbD 14 then (bif g.getLsbD 13 then (bif g.getLsbD 9 then true else true) else (bif g.getLsbD 11 then (bif g.getLsbD 7 then true else true) else true)) else (bif g.getLsbD 13 then (bif g.getLsbD 12 then true else (bif g.getLsbD 11 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true)) else true) else (bif g.getLsbD 8 then true else true))) else (bif g.getLsbD 12 then true else (bif g.getLsbD 8 then true else true)))) else (bif g.getLsbD 16 then (bif g.getLsbD 14 then (bif g.getLsbD 13 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then true else (bif g.getLsbD 7 then true else true)) else (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else true)) else (bif g.getLsbD 12 then (bif g.getLsbD 7 then true else true) else (bif g.getLsbD 11 then (bif g.getLsbD 8 then true else true) else (bif g.getLsbD 8 then true else true)))) else (bif g.getLsbD 13 then (bif g.getLsbD 12 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true)) else true) else (bif g.getLsbD 11 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true)) else true) else true) else (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true) else true) else true) else true))) else (bif g.getLsbD 12 then (bif g.getLsbD 11 then (bif g.getLsbD 8 then true else true) else (bif g.getLsbD 8 then true else true)) else (bif g.getLsbD 7 then true else true)))) else (bif g.getLsbD 14 then (bif g.getLsbD 13 then (bif g.getLsbD 9 then true else true) else (bif g.getLsbD 12 then true else (bif g.getLsbD 8 then true else true))) else (bif g.getLsbD 13 then (bif g.getLsbD 12 then (bif g.getLsbD 8 then true else true) else (bif g.getLsbD 11 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true) else true) else true) else true) else true)) else (bif g.getLsbD 12 then (bif g.getLsbD 8 then true else true) else true)))))) else (bif g.getLsbD 18 then (bif g.getLsbD 17 then (bif g.getLsbD 14 then (bif g.getLsbD 13 then (bif g.getLsbD 9 then true else true) else (bif g.getLsbD 12 then true else (bif g.getLsbD 11 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true)) else true) else (bif g.getLsbD 8 then true else true)))) else (bif g.getLsbD 13 then (bif g.getLsbD 11 then (bif g.getLsbD 4 then true else true) else true) else (bif g.getLsbD 12 then true else (bif g.getLsbD 5 then true else true)))) else (bif g.getLsbD 16 then (bif g.getLsbD 14 then (bif g.getLsbD 13 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else true) else (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true)) else (bif g.getLsbD 12 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true)) else true) else (bif g.getLsbD 11 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true)) else true) else true) else (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true) else true) else true) else true)))) else (bif g.getLsbD 13 then (bif g.getLsbD 12 then (bif g.getLsbD 4 then true else true) else (bif g.getLsbD 11 then (bif g.getLsbD 5 then true else true) else (bif g.getLsbD 5 then true else true))) else (bif g.getLsbD 12 then (bif g.getLsbD 11 then (bif g.getLsbD 5 then true else true) else (bif g.getLsbD 5 then true else true)) else (bif g.getLsbD 4 then true else true)))) else (bif g.getLsbD 14 then (bif g.getLsbD 13 then (bif g.getLsbD 9 then true else true) else (bif g.getLsbD 12 then (bif g.getLsbD 8 then true else true) else (bif g.getLsbD 11 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true) else true) else true) else true) else true))) else (bif g.getLsbD 13 then (bif g.getLsbD 12 then true else (bif g.getLsbD 5 then true else true)) else (bif g.getLsbD 12 then (bif g.getLsbD 5 then true else true) else true))))) else (bif g.getLsbD 17 then (bif g.getLsbD 16 then (bif g.getLsbD 14 then (bif g.getLsbD 13 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true)) else true) else (bif g.getLsbD 12 then true else (bif g.getLsbD 11 then (bif g.getLsbD 8 then true else true) else (bif g.getLsbD 8 then true else true)))) else (bif g.getLsbD 13 then (bif g.getLsbD 12 then true else (bif g.getLsbD 11 then (bif g.getLsbD 5 then true else true) else (bif g.getLsbD 5 then true else true))) else true)) else (bif g.getLsbD 14 then (bif g.getLsbD 13 then (bif g.getLsbD 8 then true else true) else (bif g.getLsbD 8 then true else true)) else (bif g.getLsbD 5 then true else true))) else (bif g.getLsbD 14 then (bif g.getLsbD 13 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true) else true) else true) else true) else (bif g.getLsbD 12 then (bif g.getLsbD 8 then true else true) else (bif g.getLsbD 11 then (bif g.getLsbD 7 then true else true) else true))) else (bif g.getLsbD 13 then (bif g.getLsbD 12 then (bif g.getLsbD 5 then true else true) else (bif g.getLsbD 11 then (bif g.getLsbD 4 then true else true) else true)) else true))))))) else (bif g.getLsbD 20 then (bif g.getLsbD 19 then (bif g.getLsbD 14 then true else (bif g.getLsbD 13 then (bif g.getLsbD 9 then (bif g.getLsbD 7 then true else true) else true) else (bif g.getLsbD 12 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else true) else (bif g.getLsbD 11 then true else true)))) else (bif g.getLsbD 18 then (bif g.getLsbD 14 then (bif g.getLsbD 9 then (bif g.getLsbD 7 then true else true) else true) else (bif g.getLsbD 13 then true else (bif g.getLsbD 12 then (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true) else (bif g.getLsbD 11 then true else true)))) else (bif g.getLsbD 17 then (bif g.getLsbD 14 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else true) else (bif g.getLsbD 13 then (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true) else (bif g.getLsbD 12 then true else (bif g.getLsbD 11 then true else true)))) else (bif g.getLsbD 16 then (bif g.getLsbD 14 then true else (bif g.getLsbD 13 then true else true)) else (bif g.getLsbD 14 then true else (bif g.getLsbD 13 then true else true)))))) else (bif g.getLsbD 19 then (bif g.getLsbD 18 then (bif g.getLsbD 14 then (bif g.getLsbD 13 then (bif g.getLsbD 7 then true else true) else (bif g.getLsbD 12 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then true else (bif g.getLsbD 7 then true else true)) else (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else true)) else (bif g.getLsbD 11 then (bif g.getLsbD 9 then true else true) else (bif g.getLsbD 9 then true else true)))) else (bif g.getLsbD 13 then (bif g.getLsbD 12 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else true) else (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true)) else (bif g.getLsbD 11 then (bif g.getLsbD 9 then true else true) else (bif g.getLsbD 9 then true else true))) else (bif g.getLsbD 12 then (bif g.getLsbD 11 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true)) else true) else true) else (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true) else true) else true) else true)) else (bif g.getLsbD 7 then true else true)))) else (bif g.getLsbD 17 then (bif g.getLsbD 14 then (bif g.getLsbD 13 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then true else (bif g.getLsbD 7 then true else true)) else (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else true)) else (bif g.getLsbD 12 then (bif g.getLsbD 7 then true else true) else (bif g.getLsbD 11 then (bif g.getLsbD 8 then true else true) else (bif g.getLsbD 8 then true else true)))) else (bif g.getLsbD 13 then (bif g.getLsbD 12 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true)) else true) else (bif g.getLsbD 11 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true)) else true) else true) else (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true) else true) else true) else true))) else (bif g.getLsbD 12 then (bif g.getLsbD 11 then (bif g.getLsbD 8 then true else true) else (bif g.getLsbD 8 then true else true)) else (bif g.getLsbD 7 then true else true)))) else (bif g.getLsbD 16 then (bif g.getLsbD 14 then (bif g.getLsbD 13 then (bif g.getLsbD 9 then true else true) else (bif g.getLsbD 12 then (bif g.getLsbD 8 then true else true) else true)) else (bif g.getLsbD 13 then (bif g.getLsbD 12 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true)) else true) else true) else (bif g.getLsbD 11 then true else (bif g.getLsbD 7 then true else true))) else (bif g.getLsbD 11 then true else (bif g.getLsbD 7 then true else true)))) else (bif g.getLsbD 14 then (bif g.getLsbD 13 then (bif g.getLsbD 9 then true else true) else (bif g.getLsbD 12 then (bif g.getLsbD 8 then true else true) else true)) else (bif g.getLsbD 13 then (bif g.getLsbD 12 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true) else true) else true) else true) else (bif g.getLsbD 11 then (bif g.getLsbD 7 then true else true) else true)) else (bif g.getLsbD 11 then (bif g.getLsbD 7 then true else true) else true)))))) else (bif g.getLsbD 18 then (bif g.getLsbD 17 then (bif g.getLsbD 14 then (bif g.getLsbD 13 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else true) else (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true)) else (bif g.getLsbD 12 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else true) else (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true)) else true) else (bif g.getLsbD 11 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true)) else true) else true) else (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true) else true) else true) else true)))) else (bif g.getLsbD 13 then (bif g.getLsbD 12 then (bif g.getLsbD 4 then true else true) else (bif g.getLsbD 11 then (bif g.getLsbD 5 then true else true) else (bif g.getLsbD 5 then true else true))) else (bif g.getLsbD 12 then (bif g.getLsbD 11 then (bif g.getLsbD 5 then true else true) else (bif g.getLsbD 5 then true else true)) else (bif g.getLsbD 4 then true else true)))) else (bif g.getLsbD 16 then (bif g.getLsbD 14 then (bif g.getLsbD 13 then (bif g.getLsbD 9 then true else true) else (bif g.getLsbD 12 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true)) else true) else true) else (bif g.getLsbD 11 then true else (bif g.getLsbD 7 then true else true)))) else (bif g.getLsbD 13 then (bif g.getLsbD 12 then (bif g.getLsbD 5 then true else true) else true) else (bif g.getLsbD 11 then true else (bif g.getLsbD 4 then true else true)))) else (bif g.getLsbD 14 then (bif g.getLsbD 13 then (bif g.getLsbD 9 then true else true) else (bif g.getLsbD 12 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true) else true) else true) else true) else (bif g.getLsbD 11 then (bif g.getLsbD 7 then true else true) else true))) else (bif g.getLsbD 13 then (bif g.getLsbD 12 then (bif g.getLsbD 5 then true else true) else true) else (bif g.getLsbD 11 then (bif g.getLsbD 4 then true else true) else true))))) else (bif g.getLsbD 17 then (bif g.getLsbD 16 then (bif g.getLsbD 14 then (bif g.getLsbD 13 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then true else (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true)) else true) else true) else (bif g.getLsbD 12 then (bif g.getLsbD 8 then true else true) else (bif g.getLsbD 11 then true else (bif g.getLsbD 7 then true else true)))) else (bif g.getLsbD 13 then (bif g.getLsbD 12 then (bif g.getLsbD 5 then true else true) else (bif g.getLsbD 11 then true else (bif g.getLsbD 4 then true else true))) else true)) else (bif g.getLsbD 14 then (bif g.getLsbD 13 then (bif g.getLsbD 9 then (bif g.getLsbD 8 then (bif g.getLsbD 7 then (bif g.getLsbD 5 then (bif g.getLsbD 4 then true else true) else true) else true) else true) else true) else (bif g.getLsbD 12 then (bif g.getLsbD 8 then true else true) else (bif g.getLsbD 11 then (bif g.getLsbD 7 then true else true) else true))) else (bif g.getLsbD 13 then (bif g.getLsbD 12 then (bif g.getLsbD 5 then true else true) else (bif g.getLsbD 11 then (bif g.getLsbD 4 then true else true) else true)) else true))) else (bif g.getLsbD 14 then (bif g.getLsbD 13 then (bif g.getLsbD 7 then true else true) else (bif g.getLsbD 7 then true else true)) else (bif g.getLsbD 4 then true else true)))))))))))

def memberDegreeEdgeCodes44444222BDD
    (g : BitVec (edgeCount 8)) : Bool :=
  let n2 := bif g.getLsbD 0 then false else true
  let n3 := bif g.getLsbD 1 then false else n2
  let n4 := bif g.getLsbD 2 then n3 else false
  let n5 := bif g.getLsbD 3 then n4 else false
  let n6 := bif g.getLsbD 1 then n2 else false
  let n7 := bif g.getLsbD 2 then false else n6
  let n8 := bif g.getLsbD 3 then false else n7
  let n9 := bif g.getLsbD 4 then n8 else n5
  let n10 := bif g.getLsbD 5 then n9 else false
  let n11 := bif g.getLsbD 6 then n10 else false
  let n12 := bif g.getLsbD 7 then n11 else false
  let n13 := bif g.getLsbD 8 then n12 else false
  let n14 := bif g.getLsbD 9 then n13 else false
  let n15 := bif g.getLsbD 10 then false else n14
  let n16 := bif g.getLsbD 11 then false else n15
  let n17 := bif g.getLsbD 12 then n16 else false
  let n18 := bif g.getLsbD 13 then n17 else false
  let n19 := bif g.getLsbD 4 then n5 else false
  let n20 := bif g.getLsbD 5 then n19 else false
  let n21 := bif g.getLsbD 6 then n20 else false
  let n22 := bif g.getLsbD 3 then n7 else false
  let n23 := bif g.getLsbD 4 then n22 else false
  let n24 := bif g.getLsbD 5 then n23 else false
  let n25 := bif g.getLsbD 6 then false else n24
  let n26 := bif g.getLsbD 7 then n25 else n21
  let n27 := bif g.getLsbD 8 then n26 else false
  let n28 := bif g.getLsbD 9 then n27 else false
  let n29 := bif g.getLsbD 10 then false else n28
  let n30 := bif g.getLsbD 11 then false else n29
  let n31 := bif g.getLsbD 12 then n30 else false
  let n32 := bif g.getLsbD 2 then n6 else false
  let n33 := bif g.getLsbD 3 then false else n32
  let n34 := bif g.getLsbD 4 then n33 else false
  let n35 := bif g.getLsbD 5 then n34 else false
  let n36 := bif g.getLsbD 6 then n35 else false
  let n37 := bif g.getLsbD 3 then n32 else false
  let n38 := bif g.getLsbD 4 then false else n37
  let n39 := bif g.getLsbD 5 then n38 else false
  let n40 := bif g.getLsbD 6 then false else n39
  let n41 := bif g.getLsbD 7 then n40 else n36
  let n42 := bif g.getLsbD 8 then n41 else false
  let n43 := bif g.getLsbD 9 then n42 else false
  let n44 := bif g.getLsbD 10 then false else n43
  let n45 := bif g.getLsbD 11 then false else n44
  let n46 := bif g.getLsbD 12 then false else n45
  let n47 := bif g.getLsbD 13 then n46 else n31
  let n48 := bif g.getLsbD 14 then n47 else n18
  let n49 := bif g.getLsbD 15 then n48 else false
  let n50 := bif g.getLsbD 16 then n49 else false
  let n51 := bif g.getLsbD 2 then false else n3
  let n52 := bif g.getLsbD 3 then n51 else false
  let n53 := bif g.getLsbD 4 then n52 else false
  let n54 := bif g.getLsbD 5 then n53 else false
  let n55 := bif g.getLsbD 6 then n54 else false
  let n56 := bif g.getLsbD 7 then n55 else false
  let n57 := bif g.getLsbD 8 then n56 else false
  let n58 := bif g.getLsbD 9 then n57 else false
  let n59 := bif g.getLsbD 10 then false else n58
  let n60 := bif g.getLsbD 11 then n59 else false
  let n61 := bif g.getLsbD 12 then n60 else false
  let n62 := bif g.getLsbD 3 then false else n4
  let n63 := bif g.getLsbD 4 then n62 else false
  let n64 := bif g.getLsbD 5 then n63 else false
  let n65 := bif g.getLsbD 6 then n64 else false
  let n66 := bif g.getLsbD 7 then n65 else false
  let n67 := bif g.getLsbD 8 then n66 else false
  let n68 := bif g.getLsbD 9 then n67 else false
  let n69 := bif g.getLsbD 10 then n68 else false
  let n70 := bif g.getLsbD 11 then n15 else n69
  let n71 := bif g.getLsbD 0 then true else false
  let n72 := bif g.getLsbD 1 then false else n71
  let n73 := bif g.getLsbD 2 then false else n72
  let n74 := bif g.getLsbD 3 then false else n73
  let n75 := bif g.getLsbD 4 then n74 else false
  let n76 := bif g.getLsbD 5 then n75 else n19
  let n77 := bif g.getLsbD 6 then n76 else false
  let n78 := bif g.getLsbD 7 then n77 else false
  let n79 := bif g.getLsbD 8 then n78 else false
  let n80 := bif g.getLsbD 9 then n79 else false
  let n81 := bif g.getLsbD 10 then false else n80
  let n82 := bif g.getLsbD 11 then false else n81
  let n83 := bif g.getLsbD 12 then n82 else n70
  let n84 := bif g.getLsbD 13 then n83 else n61
  let n85 := bif g.getLsbD 6 then false else n20
  let n86 := bif g.getLsbD 7 then n85 else false
  let n87 := bif g.getLsbD 8 then n86 else false
  let n88 := bif g.getLsbD 9 then n87 else false
  let n89 := bif g.getLsbD 10 then n88 else false
  let n90 := bif g.getLsbD 11 then n29 else n89
  let n91 := bif g.getLsbD 7 then n21 else false
  let n92 := bif g.getLsbD 3 then n73 else false
  let n93 := bif g.getLsbD 4 then n92 else false
  let n94 := bif g.getLsbD 5 then n93 else false
  let n95 := bif g.getLsbD 6 then false else n94
  let n96 := bif g.getLsbD 7 then n95 else false
  let n97 := bif g.getLsbD 8 then n96 else n91
  let n98 := bif g.getLsbD 9 then n97 else false
  let n99 := bif g.getLsbD 10 then false else n98
  let n100 := bif g.getLsbD 11 then false else n99
  let n101 := bif g.getLsbD 12 then n100 else n90
  let n102 := bif g.getLsbD 8 then n91 else false
  let n103 := bif g.getLsbD 7 then n36 else false
  let n104 := bif g.getLsbD 2 then n72 else false
  let n105 := bif g.getLsbD 3 then false else n104
  let n106 := bif g.getLsbD 4 then n105 else false
  let n107 := bif g.getLsbD 5 then n106 else false
  let n108 := bif g.getLsbD 6 then n107 else false
  let n109 := bif g.getLsbD 4 then n37 else false
  let n110 := bif g.getLsbD 3 then n104 else false
  let n111 := bif g.getLsbD 1 then n71 else false
  let n112 := bif g.getLsbD 2 then false else n111
  let n113 := bif g.getLsbD 3 then false else n112
  let n114 := bif g.getLsbD 4 then n113 else n110
  let n115 := bif g.getLsbD 5 then n114 else n109
  let n116 := bif g.getLsbD 6 then false else n115
  let n117 := bif g.getLsbD 7 then n116 else n108
  let n118 := bif g.getLsbD 8 then n117 else n103
  let n119 := bif g.getLsbD 9 then n118 else n102
  let n120 := bif g.getLsbD 10 then false else n119
  let n121 := bif g.getLsbD 11 then false else n120
  let n122 := bif g.getLsbD 12 then false else n121
  let n123 := bif g.getLsbD 13 then n122 else n101
  let n124 := bif g.getLsbD 14 then n123 else n84
  let n125 := bif g.getLsbD 15 then n124 else false
  let n126 := bif g.getLsbD 10 then n58 else false
  let n127 := bif g.getLsbD 11 then false else n126
  let n128 := bif g.getLsbD 12 then n127 else false
  let n129 := bif g.getLsbD 10 then n14 else false
  let n130 := bif g.getLsbD 4 then false else n22
  let n131 := bif g.getLsbD 5 then n130 else false
  let n132 := bif g.getLsbD 6 then n131 else false
  let n133 := bif g.getLsbD 7 then n132 else false
  let n134 := bif g.getLsbD 8 then n133 else false
  let n135 := bif g.getLsbD 9 then n134 else false
  let n136 := bif g.getLsbD 10 then false else n135
  let n137 := bif g.getLsbD 11 then n136 else n129
  let n138 := bif g.getLsbD 4 then false else n92
  let n139 := bif g.getLsbD 5 then n138 else n23
  let n140 := bif g.getLsbD 6 then n139 else false
  let n141 := bif g.getLsbD 7 then n140 else false
  let n142 := bif g.getLsbD 8 then n141 else false
  let n143 := bif g.getLsbD 9 then n142 else false
  let n144 := bif g.getLsbD 10 then false else n143
  let n145 := bif g.getLsbD 11 then false else n144
  let n146 := bif g.getLsbD 12 then n145 else n137
  let n147 := bif g.getLsbD 13 then n146 else n128
  let n148 := bif g.getLsbD 10 then n28 else false
  let n149 := bif g.getLsbD 6 then n24 else false
  let n150 := bif g.getLsbD 7 then false else n149
  let n151 := bif g.getLsbD 8 then n150 else false
  let n152 := bif g.getLsbD 9 then n151 else false
  let n153 := bif g.getLsbD 10 then false else n152
  let n154 := bif g.getLsbD 11 then n153 else n148
  let n155 := bif g.getLsbD 7 then n149 else false
  let n156 := bif g.getLsbD 6 then n94 else false
  let n157 := bif g.getLsbD 7 then false else n156
  let n158 := bif g.getLsbD 8 then n157 else n155
  let n159 := bif g.getLsbD 9 then n158 else false
  let n160 := bif g.getLsbD 10 then false else n159
  let n161 := bif g.getLsbD 11 then false else n160
  let n162 := bif g.getLsbD 12 then n161 else n154
  let n163 := bif g.getLsbD 8 then n155 else false
  let n164 := bif g.getLsbD 6 then n39 else false
  let n165 := bif g.getLsbD 7 then n164 else false
  let n166 := bif g.getLsbD 6 then n115 else false
  let n167 := bif g.getLsbD 3 then n112 else false
  let n168 := bif g.getLsbD 4 then false else n167
  let n169 := bif g.getLsbD 5 then n168 else false
  let n170 := bif g.getLsbD 6 then false else n169
  let n171 := bif g.getLsbD 7 then n170 else n166
  let n172 := bif g.getLsbD 8 then n171 else n165
  let n173 := bif g.getLsbD 9 then n172 else n163
  let n174 := bif g.getLsbD 10 then false else n173
  let n175 := bif g.getLsbD 11 then false else n174
  let n176 := bif g.getLsbD 12 then false else n175
  let n177 := bif g.getLsbD 13 then n176 else n162
  let n178 := bif g.getLsbD 14 then n177 else n147
  let n179 := bif g.getLsbD 15 then false else n178
  let n180 := bif g.getLsbD 16 then n179 else n125
  let n181 := bif g.getLsbD 17 then n180 else n50
  let n182 := bif g.getLsbD 12 then n70 else false
  let n183 := bif g.getLsbD 4 then false else n33
  let n184 := bif g.getLsbD 5 then n183 else false
  let n185 := bif g.getLsbD 6 then n184 else false
  let n186 := bif g.getLsbD 7 then n185 else false
  let n187 := bif g.getLsbD 8 then n186 else false
  let n188 := bif g.getLsbD 9 then n187 else false
  let n189 := bif g.getLsbD 10 then false else n188
  let n190 := bif g.getLsbD 11 then n189 else false
  let n191 := bif g.getLsbD 4 then false else n105
  let n192 := bif g.getLsbD 5 then n191 else n34
  let n193 := bif g.getLsbD 6 then n192 else false
  let n194 := bif g.getLsbD 7 then n193 else false
  let n195 := bif g.getLsbD 8 then n194 else false
  let n196 := bif g.getLsbD 9 then n195 else false
  let n197 := bif g.getLsbD 10 then false else n196
  let n198 := bif g.getLsbD 11 then false else n197
  let n199 := bif g.getLsbD 12 then n198 else n190
  let n200 := bif g.getLsbD 13 then n199 else n182
  let n201 := bif g.getLsbD 6 then false else n35
  let n202 := bif g.getLsbD 7 then n201 else false
  let n203 := bif g.getLsbD 8 then n202 else false
  let n204 := bif g.getLsbD 9 then n203 else false
  let n205 := bif g.getLsbD 10 then n204 else false
  let n206 := bif g.getLsbD 11 then n44 else n205
  let n207 := bif g.getLsbD 12 then n121 else n206
  let n208 := bif g.getLsbD 8 then n103 else false
  let n209 := bif g.getLsbD 2 then n111 else false
  let n210 := bif g.getLsbD 3 then false else n209
  let n211 := bif g.getLsbD 4 then false else n210
  let n212 := bif g.getLsbD 5 then n211 else false
  let n213 := bif g.getLsbD 6 then false else n212
  let n214 := bif g.getLsbD 7 then n213 else false
  let n215 := bif g.getLsbD 8 then n214 else false
  let n216 := bif g.getLsbD 9 then n215 else n208
  let n217 := bif g.getLsbD 10 then false else n216
  let n218 := bif g.getLsbD 11 then false else n217
  let n219 := bif g.getLsbD 12 then false else n218
  let n220 := bif g.getLsbD 13 then n219 else n207
  let n221 := bif g.getLsbD 14 then n220 else n200
  let n222 := bif g.getLsbD 15 then n221 else false
  let n223 := bif g.getLsbD 12 then n137 else false
  let n224 := bif g.getLsbD 10 then n188 else false
  let n225 := bif g.getLsbD 11 then false else n224
  let n226 := bif g.getLsbD 4 then false else n113
  let n227 := bif g.getLsbD 5 then n226 else n38
  let n228 := bif g.getLsbD 6 then n227 else false
  let n229 := bif g.getLsbD 7 then n228 else false
  let n230 := bif g.getLsbD 8 then n229 else false
  let n231 := bif g.getLsbD 9 then n230 else false
  let n232 := bif g.getLsbD 10 then false else n231
  let n233 := bif g.getLsbD 11 then false else n232
  let n234 := bif g.getLsbD 12 then n233 else n225
  let n235 := bif g.getLsbD 13 then n234 else n223
  let n236 := bif g.getLsbD 10 then n43 else false
  let n237 := bif g.getLsbD 7 then false else n164
  let n238 := bif g.getLsbD 8 then n237 else false
  let n239 := bif g.getLsbD 9 then n238 else false
  let n240 := bif g.getLsbD 10 then false else n239
  let n241 := bif g.getLsbD 11 then n240 else n236
  let n242 := bif g.getLsbD 12 then n175 else n241
  let n243 := bif g.getLsbD 8 then n165 else false
  let n244 := bif g.getLsbD 6 then n212 else false
  let n245 := bif g.getLsbD 7 then false else n244
  let n246 := bif g.getLsbD 8 then n245 else false
  let n247 := bif g.getLsbD 9 then n246 else n243
  let n248 := bif g.getLsbD 10 then false else n247
  let n249 := bif g.getLsbD 11 then false else n248
  let n250 := bif g.getLsbD 12 then false else n249
  let n251 := bif g.getLsbD 13 then n250 else n242
  let n252 := bif g.getLsbD 14 then n251 else n235
  let n253 := bif g.getLsbD 15 then false else n252
  let n254 := bif g.getLsbD 16 then n253 else n222
  let n255 := bif g.getLsbD 11 then n129 else false
  let n256 := bif g.getLsbD 10 then n80 else false
  let n257 := bif g.getLsbD 11 then n144 else n256
  let n258 := bif g.getLsbD 12 then n257 else n255
  let n259 := bif g.getLsbD 10 then n196 else false
  let n260 := bif g.getLsbD 11 then n232 else n259
  let n261 := bif g.getLsbD 5 then false else n114
  let n262 := bif g.getLsbD 6 then n261 else false
  let n263 := bif g.getLsbD 7 then n262 else false
  let n264 := bif g.getLsbD 8 then n263 else false
  let n265 := bif g.getLsbD 9 then n264 else false
  let n266 := bif g.getLsbD 10 then false else n265
  let n267 := bif g.getLsbD 11 then false else n266
  let n268 := bif g.getLsbD 12 then n267 else n260
  let n269 := bif g.getLsbD 13 then n268 else n258
  let n270 := bif g.getLsbD 10 then n119 else false
  let n271 := bif g.getLsbD 11 then n174 else n270
  let n272 := bif g.getLsbD 7 then n156 else false
  let n273 := bif g.getLsbD 8 then n272 else false
  let n274 := bif g.getLsbD 7 then n166 else false
  let n275 := bif g.getLsbD 4 then n110 else false
  let n276 := bif g.getLsbD 5 then false else n275
  let n277 := bif g.getLsbD 6 then n276 else false
  let n278 := bif g.getLsbD 4 then n167 else false
  let n279 := bif g.getLsbD 5 then false else n278
  let n280 := bif g.getLsbD 6 then false else n279
  let n281 := bif g.getLsbD 7 then n280 else n277
  let n282 := bif g.getLsbD 8 then n281 else n274
  let n283 := bif g.getLsbD 9 then n282 else n273
  let n284 := bif g.getLsbD 10 then false else n283
  let n285 := bif g.getLsbD 11 then false else n284
  let n286 := bif g.getLsbD 12 then n285 else n271
  let n287 := bif g.getLsbD 8 then n274 else false
  let n288 := bif g.getLsbD 7 then n244 else false
  let n289 := bif g.getLsbD 4 then n210 else false
  let n290 := bif g.getLsbD 5 then false else n289
  let n291 := bif g.getLsbD 6 then n290 else false
  let n292 := bif g.getLsbD 3 then n209 else false
  let n293 := bif g.getLsbD 4 then false else n292
  let n294 := bif g.getLsbD 5 then false else n293
  let n295 := bif g.getLsbD 6 then false else n294
  let n296 := bif g.getLsbD 7 then n295 else n291
  let n297 := bif g.getLsbD 8 then n296 else n288
  let n298 := bif g.getLsbD 9 then n297 else n287
  let n299 := bif g.getLsbD 10 then false else n298
  let n300 := bif g.getLsbD 11 then false else n299
  let n301 := bif g.getLsbD 12 then false else n300
  let n302 := bif g.getLsbD 13 then n301 else n286
  let n303 := bif g.getLsbD 14 then n302 else n269
  let n304 := bif g.getLsbD 15 then false else n303
  let n305 := bif g.getLsbD 16 then false else n304
  let n306 := bif g.getLsbD 17 then n305 else n254
  let n307 := bif g.getLsbD 18 then n306 else n181
  let n308 := bif g.getLsbD 12 then n90 else false
  let n309 := bif g.getLsbD 13 then n207 else n308
  let n310 := bif g.getLsbD 5 then n109 else false
  let n311 := bif g.getLsbD 6 then false else n310
  let n312 := bif g.getLsbD 7 then false else n311
  let n313 := bif g.getLsbD 8 then n312 else false
  let n314 := bif g.getLsbD 9 then n313 else false
  let n315 := bif g.getLsbD 10 then false else n314
  let n316 := bif g.getLsbD 11 then n315 else false
  let n317 := bif g.getLsbD 7 then n311 else false
  let n318 := bif g.getLsbD 5 then n275 else false
  let n319 := bif g.getLsbD 6 then false else n318
  let n320 := bif g.getLsbD 7 then false else n319
  let n321 := bif g.getLsbD 8 then n320 else n317
  let n322 := bif g.getLsbD 9 then n321 else false
  let n323 := bif g.getLsbD 10 then false else n322
  let n324 := bif g.getLsbD 11 then false else n323
  let n325 := bif g.getLsbD 12 then n324 else n316
  let n326 := bif g.getLsbD 8 then n317 else false
  let n327 := bif g.getLsbD 5 then n289 else false
  let n328 := bif g.getLsbD 6 then false else n327
  let n329 := bif g.getLsbD 7 then false else n328
  let n330 := bif g.getLsbD 8 then n329 else false
  let n331 := bif g.getLsbD 9 then n330 else n326
  let n332 := bif g.getLsbD 10 then false else n331
  let n333 := bif g.getLsbD 11 then false else n332
  let n334 := bif g.getLsbD 12 then false else n333
  let n335 := bif g.getLsbD 13 then n334 else n325
  let n336 := bif g.getLsbD 14 then n335 else n309
  let n337 := bif g.getLsbD 15 then n336 else false
  let n338 := bif g.getLsbD 12 then n154 else false
  let n339 := bif g.getLsbD 13 then n242 else n338
  let n340 := bif g.getLsbD 10 then n314 else false
  let n341 := bif g.getLsbD 11 then false else n340
  let n342 := bif g.getLsbD 6 then n310 else false
  let n343 := bif g.getLsbD 7 then false else n342
  let n344 := bif g.getLsbD 5 then n278 else false
  let n345 := bif g.getLsbD 6 then false else n344
  let n346 := bif g.getLsbD 7 then false else n345
  let n347 := bif g.getLsbD 8 then n346 else n343
  let n348 := bif g.getLsbD 9 then n347 else false
  let n349 := bif g.getLsbD 10 then false else n348
  let n350 := bif g.getLsbD 11 then false else n349
  let n351 := bif g.getLsbD 12 then n350 else n341
  let n352 := bif g.getLsbD 8 then n343 else false
  let n353 := bif g.getLsbD 5 then n293 else false
  let n354 := bif g.getLsbD 6 then false else n353
  let n355 := bif g.getLsbD 7 then false else n354
  let n356 := bif g.getLsbD 8 then n355 else false
  let n357 := bif g.getLsbD 9 then n356 else n352
  let n358 := bif g.getLsbD 10 then false else n357
  let n359 := bif g.getLsbD 11 then false else n358
  let n360 := bif g.getLsbD 12 then false else n359
  let n361 := bif g.getLsbD 13 then n360 else n351
  let n362 := bif g.getLsbD 14 then n361 else n339
  let n363 := bif g.getLsbD 15 then false else n362
  let n364 := bif g.getLsbD 16 then n363 else n337
  let n365 := bif g.getLsbD 11 then n148 else false
  let n366 := bif g.getLsbD 10 then n98 else false
  let n367 := bif g.getLsbD 11 then n160 else n366
  let n368 := bif g.getLsbD 12 then n367 else n365
  let n369 := bif g.getLsbD 13 then n286 else n368
  let n370 := bif g.getLsbD 10 then n322 else false
  let n371 := bif g.getLsbD 11 then n349 else n370
  let n372 := bif g.getLsbD 6 then n318 else false
  let n373 := bif g.getLsbD 7 then n345 else n372
  let n374 := bif g.getLsbD 8 then false else n373
  let n375 := bif g.getLsbD 9 then n374 else false
  let n376 := bif g.getLsbD 10 then false else n375
  let n377 := bif g.getLsbD 11 then false else n376
  let n378 := bif g.getLsbD 12 then n377 else n371
  let n379 := bif g.getLsbD 7 then n342 else false
  let n380 := bif g.getLsbD 8 then n373 else n379
  let n381 := bif g.getLsbD 6 then n327 else false
  let n382 := bif g.getLsbD 7 then n354 else n381
  let n383 := bif g.getLsbD 4 then n292 else false
  let n384 := bif g.getLsbD 5 then false else n383
  let n385 := bif g.getLsbD 6 then false else n384
  let n386 := bif g.getLsbD 7 then false else n385
  let n387 := bif g.getLsbD 8 then n386 else n382
  let n388 := bif g.getLsbD 9 then n387 else n380
  let n389 := bif g.getLsbD 10 then false else n388
  let n390 := bif g.getLsbD 11 then false else n389
  let n391 := bif g.getLsbD 12 then false else n390
  let n392 := bif g.getLsbD 13 then n391 else n378
  let n393 := bif g.getLsbD 14 then n392 else n369
  let n394 := bif g.getLsbD 15 then false else n393
  let n395 := bif g.getLsbD 16 then false else n394
  let n396 := bif g.getLsbD 17 then n395 else n364
  let n397 := bif g.getLsbD 11 then n236 else false
  let n398 := bif g.getLsbD 12 then n271 else n397
  let n399 := bif g.getLsbD 10 then n216 else false
  let n400 := bif g.getLsbD 11 then n248 else n399
  let n401 := bif g.getLsbD 12 then n300 else n400
  let n402 := bif g.getLsbD 13 then n401 else n398
  let n403 := bif g.getLsbD 10 then n331 else false
  let n404 := bif g.getLsbD 11 then n358 else n403
  let n405 := bif g.getLsbD 12 then n390 else n404
  let n406 := bif g.getLsbD 8 then n382 else false
  let n407 := bif g.getLsbD 9 then false else n406
  let n408 := bif g.getLsbD 10 then false else n407
  let n409 := bif g.getLsbD 11 then false else n408
  let n410 := bif g.getLsbD 12 then false else n409
  let n411 := bif g.getLsbD 13 then n410 else n405
  let n412 := bif g.getLsbD 14 then n411 else n402
  let n413 := bif g.getLsbD 15 then false else n412
  let n414 := bif g.getLsbD 16 then false else n413
  let n415 := bif g.getLsbD 17 then false else n414
  let n416 := bif g.getLsbD 18 then n415 else n396
  let n417 := bif g.getLsbD 19 then n416 else n307
  let n418 := bif g.getLsbD 9 then n102 else false
  let n419 := bif g.getLsbD 10 then false else n418
  let n420 := bif g.getLsbD 11 then false else n419
  let n421 := bif g.getLsbD 12 then n420 else false
  let n422 := bif g.getLsbD 9 then n208 else false
  let n423 := bif g.getLsbD 10 then false else n422
  let n424 := bif g.getLsbD 11 then false else n423
  let n425 := bif g.getLsbD 12 then false else n424
  let n426 := bif g.getLsbD 13 then n425 else n421
  let n427 := bif g.getLsbD 9 then n326 else false
  let n428 := bif g.getLsbD 10 then false else n427
  let n429 := bif g.getLsbD 11 then false else n428
  let n430 := bif g.getLsbD 12 then false else n429
  let n431 := bif g.getLsbD 13 then false else n430
  let n432 := bif g.getLsbD 14 then n431 else n426
  let n433 := bif g.getLsbD 15 then n432 else false
  let n434 := bif g.getLsbD 9 then n163 else false
  let n435 := bif g.getLsbD 10 then false else n434
  let n436 := bif g.getLsbD 11 then false else n435
  let n437 := bif g.getLsbD 12 then n436 else false
  let n438 := bif g.getLsbD 9 then n243 else false
  let n439 := bif g.getLsbD 10 then false else n438
  let n440 := bif g.getLsbD 11 then false else n439
  let n441 := bif g.getLsbD 12 then false else n440
  let n442 := bif g.getLsbD 13 then n441 else n437
  let n443 := bif g.getLsbD 9 then n352 else false
  let n444 := bif g.getLsbD 10 then false else n443
  let n445 := bif g.getLsbD 11 then false else n444
  let n446 := bif g.getLsbD 12 then false else n445
  let n447 := bif g.getLsbD 13 then false else n446
  let n448 := bif g.getLsbD 14 then n447 else n442
  let n449 := bif g.getLsbD 15 then false else n448
  let n450 := bif g.getLsbD 16 then n449 else n433
  let n451 := bif g.getLsbD 10 then n418 else false
  let n452 := bif g.getLsbD 11 then n435 else n451
  let n453 := bif g.getLsbD 9 then n273 else false
  let n454 := bif g.getLsbD 10 then false else n453
  let n455 := bif g.getLsbD 11 then false else n454
  let n456 := bif g.getLsbD 12 then n455 else n452
  let n457 := bif g.getLsbD 9 then n287 else false
  let n458 := bif g.getLsbD 10 then false else n457
  let n459 := bif g.getLsbD 11 then false else n458
  let n460 := bif g.getLsbD 12 then false else n459
  let n461 := bif g.getLsbD 13 then n460 else n456
  let n462 := bif g.getLsbD 9 then n380 else false
  let n463 := bif g.getLsbD 10 then false else n462
  let n464 := bif g.getLsbD 11 then false else n463
  let n465 := bif g.getLsbD 12 then false else n464
  let n466 := bif g.getLsbD 13 then false else n465
  let n467 := bif g.getLsbD 14 then n466 else n461
  let n468 := bif g.getLsbD 15 then false else n467
  let n469 := bif g.getLsbD 16 then false else n468
  let n470 := bif g.getLsbD 17 then n469 else n450
  let n471 := bif g.getLsbD 10 then n422 else false
  let n472 := bif g.getLsbD 11 then n439 else n471
  let n473 := bif g.getLsbD 12 then n459 else n472
  let n474 := bif g.getLsbD 8 then n288 else false
  let n475 := bif g.getLsbD 9 then n474 else false
  let n476 := bif g.getLsbD 10 then false else n475
  let n477 := bif g.getLsbD 11 then false else n476
  let n478 := bif g.getLsbD 12 then false else n477
  let n479 := bif g.getLsbD 13 then n478 else n473
  let n480 := bif g.getLsbD 8 then n379 else false
  let n481 := bif g.getLsbD 9 then n406 else n480
  let n482 := bif g.getLsbD 10 then false else n481
  let n483 := bif g.getLsbD 11 then false else n482
  let n484 := bif g.getLsbD 12 then false else n483
  let n485 := bif g.getLsbD 13 then false else n484
  let n486 := bif g.getLsbD 14 then n485 else n479
  let n487 := bif g.getLsbD 15 then false else n486
  let n488 := bif g.getLsbD 16 then false else n487
  let n489 := bif g.getLsbD 17 then false else n488
  let n490 := bif g.getLsbD 18 then n489 else n470
  let n491 := bif g.getLsbD 10 then n427 else false
  let n492 := bif g.getLsbD 11 then n444 else n491
  let n493 := bif g.getLsbD 12 then n464 else n492
  let n494 := bif g.getLsbD 13 then n484 else n493
  let n495 := bif g.getLsbD 5 then n383 else false
  let n496 := bif g.getLsbD 6 then false else n495
  let n497 := bif g.getLsbD 7 then false else n496
  let n498 := bif g.getLsbD 8 then n497 else false
  let n499 := bif g.getLsbD 9 then n498 else false
  let n500 := bif g.getLsbD 10 then false else n499
  let n501 := bif g.getLsbD 11 then false else n500
  let n502 := bif g.getLsbD 12 then false else n501
  let n503 := bif g.getLsbD 13 then false else n502
  let n504 := bif g.getLsbD 14 then n503 else n494
  let n505 := bif g.getLsbD 15 then false else n504
  let n506 := bif g.getLsbD 16 then false else n505
  let n507 := bif g.getLsbD 17 then false else n506
  let n508 := bif g.getLsbD 18 then false else n507
  let n509 := bif g.getLsbD 19 then n508 else n490
  let n510 := bif g.getLsbD 20 then n509 else n417
  let n511 := bif g.getLsbD 21 then n510 else false
  let n512 := bif g.getLsbD 22 then n511 else false
  let n513 := bif g.getLsbD 16 then n125 else false
  let n514 := bif g.getLsbD 11 then n81 else false
  let n515 := bif g.getLsbD 12 then false else n514
  let n516 := bif g.getLsbD 13 then n515 else false
  let n517 := bif g.getLsbD 11 then n99 else false
  let n518 := bif g.getLsbD 12 then false else n517
  let n519 := bif g.getLsbD 7 then n108 else false
  let n520 := bif g.getLsbD 6 then false else n276
  let n521 := bif g.getLsbD 7 then n520 else false
  let n522 := bif g.getLsbD 8 then n521 else n519
  let n523 := bif g.getLsbD 9 then n522 else false
  let n524 := bif g.getLsbD 10 then false else n523
  let n525 := bif g.getLsbD 11 then false else n524
  let n526 := bif g.getLsbD 12 then false else n525
  let n527 := bif g.getLsbD 13 then n526 else n518
  let n528 := bif g.getLsbD 14 then n527 else n516
  let n529 := bif g.getLsbD 15 then n528 else false
  let n530 := bif g.getLsbD 11 then n126 else false
  let n531 := bif g.getLsbD 12 then false else n530
  let n532 := bif g.getLsbD 5 then false else n93
  let n533 := bif g.getLsbD 6 then n532 else false
  let n534 := bif g.getLsbD 7 then n533 else false
  let n535 := bif g.getLsbD 8 then n534 else false
  let n536 := bif g.getLsbD 9 then n535 else false
  let n537 := bif g.getLsbD 10 then false else n536
  let n538 := bif g.getLsbD 11 then false else n537
  let n539 := bif g.getLsbD 12 then n538 else n257
  let n540 := bif g.getLsbD 13 then n539 else n531
  let n541 := bif g.getLsbD 8 then false else n272
  let n542 := bif g.getLsbD 9 then n541 else false
  let n543 := bif g.getLsbD 10 then false else n542
  let n544 := bif g.getLsbD 11 then false else n543
  let n545 := bif g.getLsbD 12 then n544 else n367
  let n546 := bif g.getLsbD 12 then false else n285
  let n547 := bif g.getLsbD 13 then n546 else n545
  let n548 := bif g.getLsbD 14 then n547 else n540
  let n549 := bif g.getLsbD 15 then false else n548
  let n550 := bif g.getLsbD 16 then n549 else n529
  let n551 := bif g.getLsbD 17 then n550 else n513
  let n552 := bif g.getLsbD 11 then n69 else false
  let n553 := bif g.getLsbD 12 then n514 else n552
  let n554 := bif g.getLsbD 11 then n197 else false
  let n555 := bif g.getLsbD 5 then false else n106
  let n556 := bif g.getLsbD 6 then n555 else false
  let n557 := bif g.getLsbD 7 then n556 else false
  let n558 := bif g.getLsbD 8 then n557 else false
  let n559 := bif g.getLsbD 9 then n558 else false
  let n560 := bif g.getLsbD 10 then false else n559
  let n561 := bif g.getLsbD 11 then false else n560
  let n562 := bif g.getLsbD 12 then n561 else n554
  let n563 := bif g.getLsbD 13 then n562 else n553
  let n564 := bif g.getLsbD 6 then false else n107
  let n565 := bif g.getLsbD 7 then n564 else false
  let n566 := bif g.getLsbD 8 then n565 else false
  let n567 := bif g.getLsbD 9 then n566 else false
  let n568 := bif g.getLsbD 10 then n567 else false
  let n569 := bif g.getLsbD 11 then n120 else n568
  let n570 := bif g.getLsbD 12 then n525 else n569
  let n571 := bif g.getLsbD 8 then n519 else false
  let n572 := bif g.getLsbD 6 then false else n290
  let n573 := bif g.getLsbD 7 then n572 else false
  let n574 := bif g.getLsbD 8 then n573 else false
  let n575 := bif g.getLsbD 9 then n574 else n571
  let n576 := bif g.getLsbD 10 then false else n575
  let n577 := bif g.getLsbD 11 then false else n576
  let n578 := bif g.getLsbD 12 then false else n577
  let n579 := bif g.getLsbD 13 then n578 else n570
  let n580 := bif g.getLsbD 14 then n579 else n563
  let n581 := bif g.getLsbD 15 then n580 else false
  let n582 := bif g.getLsbD 16 then n304 else n581
  let n583 := bif g.getLsbD 11 then n256 else false
  let n584 := bif g.getLsbD 11 then n537 else false
  let n585 := bif g.getLsbD 12 then n584 else n583
  let n586 := bif g.getLsbD 10 then n559 else false
  let n587 := bif g.getLsbD 11 then n266 else n586
  let n588 := bif g.getLsbD 12 then false else n587
  let n589 := bif g.getLsbD 13 then n588 else n585
  let n590 := bif g.getLsbD 10 then n523 else false
  let n591 := bif g.getLsbD 11 then n284 else n590
  let n592 := bif g.getLsbD 7 then n277 else false
  let n593 := bif g.getLsbD 8 then false else n592
  let n594 := bif g.getLsbD 9 then n593 else false
  let n595 := bif g.getLsbD 10 then false else n594
  let n596 := bif g.getLsbD 11 then false else n595
  let n597 := bif g.getLsbD 12 then n596 else n591
  let n598 := bif g.getLsbD 8 then n592 else false
  let n599 := bif g.getLsbD 7 then n291 else false
  let n600 := bif g.getLsbD 8 then false else n599
  let n601 := bif g.getLsbD 9 then n600 else n598
  let n602 := bif g.getLsbD 10 then false else n601
  let n603 := bif g.getLsbD 11 then false else n602
  let n604 := bif g.getLsbD 12 then false else n603
  let n605 := bif g.getLsbD 13 then n604 else n597
  let n606 := bif g.getLsbD 14 then n605 else n589
  let n607 := bif g.getLsbD 15 then false else n606
  let n608 := bif g.getLsbD 16 then false else n607
  let n609 := bif g.getLsbD 17 then n608 else n582
  let n610 := bif g.getLsbD 18 then n609 else n551
  let n611 := bif g.getLsbD 11 then n89 else false
  let n612 := bif g.getLsbD 12 then n517 else n611
  let n613 := bif g.getLsbD 13 then n570 else n612
  let n614 := bif g.getLsbD 11 then n323 else false
  let n615 := bif g.getLsbD 7 then n319 else false
  let n616 := bif g.getLsbD 8 then false else n615
  let n617 := bif g.getLsbD 9 then n616 else false
  let n618 := bif g.getLsbD 10 then false else n617
  let n619 := bif g.getLsbD 11 then false else n618
  let n620 := bif g.getLsbD 12 then n619 else n614
  let n621 := bif g.getLsbD 8 then n615 else false
  let n622 := bif g.getLsbD 7 then n328 else false
  let n623 := bif g.getLsbD 8 then false else n622
  let n624 := bif g.getLsbD 9 then n623 else n621
  let n625 := bif g.getLsbD 10 then false else n624
  let n626 := bif g.getLsbD 11 then false else n625
  let n627 := bif g.getLsbD 12 then false else n626
  let n628 := bif g.getLsbD 13 then n627 else n620
  let n629 := bif g.getLsbD 14 then n628 else n613
  let n630 := bif g.getLsbD 15 then n629 else false
  let n631 := bif g.getLsbD 16 then n394 else n630
  let n632 := bif g.getLsbD 11 then n366 else false
  let n633 := bif g.getLsbD 11 then n543 else false
  let n634 := bif g.getLsbD 12 then n633 else n632
  let n635 := bif g.getLsbD 13 then n597 else n634
  let n636 := bif g.getLsbD 10 then n617 else false
  let n637 := bif g.getLsbD 11 then n376 else n636
  let n638 := bif g.getLsbD 12 then false else n637
  let n639 := bif g.getLsbD 7 then n372 else false
  let n640 := bif g.getLsbD 8 then false else n639
  let n641 := bif g.getLsbD 7 then n385 else false
  let n642 := bif g.getLsbD 8 then false else n641
  let n643 := bif g.getLsbD 9 then n642 else n640
  let n644 := bif g.getLsbD 10 then false else n643
  let n645 := bif g.getLsbD 11 then false else n644
  let n646 := bif g.getLsbD 12 then false else n645
  let n647 := bif g.getLsbD 13 then n646 else n638
  let n648 := bif g.getLsbD 14 then n647 else n635
  let n649 := bif g.getLsbD 15 then false else n648
  let n650 := bif g.getLsbD 16 then false else n649
  let n651 := bif g.getLsbD 17 then n650 else n631
  let n652 := bif g.getLsbD 11 then n270 else false
  let n653 := bif g.getLsbD 12 then n591 else n652
  let n654 := bif g.getLsbD 10 then n575 else false
  let n655 := bif g.getLsbD 11 then n299 else n654
  let n656 := bif g.getLsbD 12 then n603 else n655
  let n657 := bif g.getLsbD 13 then n656 else n653
  let n658 := bif g.getLsbD 10 then n624 else false
  let n659 := bif g.getLsbD 11 then n389 else n658
  let n660 := bif g.getLsbD 12 then n645 else n659
  let n661 := bif g.getLsbD 7 then n381 else false
  let n662 := bif g.getLsbD 8 then n641 else n661
  let n663 := bif g.getLsbD 9 then false else n662
  let n664 := bif g.getLsbD 10 then false else n663
  let n665 := bif g.getLsbD 11 then false else n664
  let n666 := bif g.getLsbD 12 then false else n665
  let n667 := bif g.getLsbD 13 then n666 else n660
  let n668 := bif g.getLsbD 14 then n667 else n657
  let n669 := bif g.getLsbD 15 then false else n668
  let n670 := bif g.getLsbD 16 then false else n669
  let n671 := bif g.getLsbD 17 then false else n670
  let n672 := bif g.getLsbD 18 then n671 else n651
  let n673 := bif g.getLsbD 19 then n672 else n610
  let n674 := bif g.getLsbD 11 then n419 else false
  let n675 := bif g.getLsbD 12 then false else n674
  let n676 := bif g.getLsbD 9 then n571 else false
  let n677 := bif g.getLsbD 10 then false else n676
  let n678 := bif g.getLsbD 11 then false else n677
  let n679 := bif g.getLsbD 12 then false else n678
  let n680 := bif g.getLsbD 13 then n679 else n675
  let n681 := bif g.getLsbD 9 then n621 else false
  let n682 := bif g.getLsbD 10 then false else n681
  let n683 := bif g.getLsbD 11 then false else n682
  let n684 := bif g.getLsbD 12 then false else n683
  let n685 := bif g.getLsbD 13 then false else n684
  let n686 := bif g.getLsbD 14 then n685 else n680
  let n687 := bif g.getLsbD 15 then n686 else false
  let n688 := bif g.getLsbD 16 then n468 else n687
  let n689 := bif g.getLsbD 11 then n454 else false
  let n690 := bif g.getLsbD 12 then false else n689
  let n691 := bif g.getLsbD 9 then n598 else false
  let n692 := bif g.getLsbD 10 then false else n691
  let n693 := bif g.getLsbD 11 then false else n692
  let n694 := bif g.getLsbD 12 then false else n693
  let n695 := bif g.getLsbD 13 then n694 else n690
  let n696 := bif g.getLsbD 9 then n640 else false
  let n697 := bif g.getLsbD 10 then false else n696
  let n698 := bif g.getLsbD 11 then false else n697
  let n699 := bif g.getLsbD 12 then false else n698
  let n700 := bif g.getLsbD 13 then false else n699
  let n701 := bif g.getLsbD 14 then n700 else n695
  let n702 := bif g.getLsbD 15 then false else n701
  let n703 := bif g.getLsbD 16 then false else n702
  let n704 := bif g.getLsbD 17 then n703 else n688
  let n705 := bif g.getLsbD 10 then n676 else false
  let n706 := bif g.getLsbD 11 then n458 else n705
  let n707 := bif g.getLsbD 12 then n693 else n706
  let n708 := bif g.getLsbD 8 then n599 else false
  let n709 := bif g.getLsbD 9 then n708 else false
  let n710 := bif g.getLsbD 10 then false else n709
  let n711 := bif g.getLsbD 11 then false else n710
  let n712 := bif g.getLsbD 12 then false else n711
  let n713 := bif g.getLsbD 13 then n712 else n707
  let n714 := bif g.getLsbD 8 then n639 else false
  let n715 := bif g.getLsbD 9 then n662 else n714
  let n716 := bif g.getLsbD 10 then false else n715
  let n717 := bif g.getLsbD 11 then false else n716
  let n718 := bif g.getLsbD 12 then false else n717
  let n719 := bif g.getLsbD 13 then false else n718
  let n720 := bif g.getLsbD 14 then n719 else n713
  let n721 := bif g.getLsbD 15 then false else n720
  let n722 := bif g.getLsbD 16 then false else n721
  let n723 := bif g.getLsbD 17 then false else n722
  let n724 := bif g.getLsbD 18 then n723 else n704
  let n725 := bif g.getLsbD 10 then n681 else false
  let n726 := bif g.getLsbD 11 then n463 else n725
  let n727 := bif g.getLsbD 12 then n698 else n726
  let n728 := bif g.getLsbD 13 then n718 else n727
  let n729 := bif g.getLsbD 7 then n496 else false
  let n730 := bif g.getLsbD 8 then false else n729
  let n731 := bif g.getLsbD 9 then n730 else false
  let n732 := bif g.getLsbD 10 then false else n731
  let n733 := bif g.getLsbD 11 then false else n732
  let n734 := bif g.getLsbD 12 then false else n733
  let n735 := bif g.getLsbD 13 then false else n734
  let n736 := bif g.getLsbD 14 then n735 else n728
  let n737 := bif g.getLsbD 15 then false else n736
  let n738 := bif g.getLsbD 16 then false else n737
  let n739 := bif g.getLsbD 17 then false else n738
  let n740 := bif g.getLsbD 18 then false else n739
  let n741 := bif g.getLsbD 19 then n740 else n724
  let n742 := bif g.getLsbD 20 then n741 else n673
  let n743 := bif g.getLsbD 21 then n742 else false
  let n744 := bif g.getLsbD 15 then n178 else false
  let n745 := bif g.getLsbD 16 then n744 else false
  let n746 := bif g.getLsbD 15 then n548 else false
  let n747 := bif g.getLsbD 10 then n143 else false
  let n748 := bif g.getLsbD 11 then false else n747
  let n749 := bif g.getLsbD 12 then false else n748
  let n750 := bif g.getLsbD 13 then n749 else false
  let n751 := bif g.getLsbD 10 then n159 else false
  let n752 := bif g.getLsbD 11 then false else n751
  let n753 := bif g.getLsbD 12 then false else n752
  let n754 := bif g.getLsbD 6 then n169 else false
  let n755 := bif g.getLsbD 7 then n754 else false
  let n756 := bif g.getLsbD 6 then n279 else false
  let n757 := bif g.getLsbD 7 then false else n756
  let n758 := bif g.getLsbD 8 then n757 else n755
  let n759 := bif g.getLsbD 9 then n758 else false
  let n760 := bif g.getLsbD 10 then false else n759
  let n761 := bif g.getLsbD 11 then false else n760
  let n762 := bif g.getLsbD 12 then false else n761
  let n763 := bif g.getLsbD 13 then n762 else n753
  let n764 := bif g.getLsbD 14 then n763 else n750
  let n765 := bif g.getLsbD 15 then false else n764
  let n766 := bif g.getLsbD 16 then n765 else n746
  let n767 := bif g.getLsbD 17 then n766 else n745
  let n768 := bif g.getLsbD 15 then n303 else false
  let n769 := bif g.getLsbD 10 then n135 else false
  let n770 := bif g.getLsbD 11 then n769 else false
  let n771 := bif g.getLsbD 12 then n748 else n770
  let n772 := bif g.getLsbD 10 then n231 else false
  let n773 := bif g.getLsbD 11 then false else n772
  let n774 := bif g.getLsbD 5 then false else n168
  let n775 := bif g.getLsbD 6 then n774 else false
  let n776 := bif g.getLsbD 7 then n775 else false
  let n777 := bif g.getLsbD 8 then n776 else false
  let n778 := bif g.getLsbD 9 then n777 else false
  let n779 := bif g.getLsbD 10 then false else n778
  let n780 := bif g.getLsbD 11 then false else n779
  let n781 := bif g.getLsbD 12 then n780 else n773
  let n782 := bif g.getLsbD 13 then n781 else n771
  let n783 := bif g.getLsbD 10 then n173 else false
  let n784 := bif g.getLsbD 7 then false else n754
  let n785 := bif g.getLsbD 8 then n784 else false
  let n786 := bif g.getLsbD 9 then n785 else false
  let n787 := bif g.getLsbD 10 then false else n786
  let n788 := bif g.getLsbD 11 then n787 else n783
  let n789 := bif g.getLsbD 12 then n761 else n788
  let n790 := bif g.getLsbD 8 then n755 else false
  let n791 := bif g.getLsbD 6 then n294 else false
  let n792 := bif g.getLsbD 7 then false else n791
  let n793 := bif g.getLsbD 8 then n792 else false
  let n794 := bif g.getLsbD 9 then n793 else n790
  let n795 := bif g.getLsbD 10 then false else n794
  let n796 := bif g.getLsbD 11 then false else n795
  let n797 := bif g.getLsbD 12 then false else n796
  let n798 := bif g.getLsbD 13 then n797 else n789
  let n799 := bif g.getLsbD 14 then n798 else n782
  let n800 := bif g.getLsbD 15 then false else n799
  let n801 := bif g.getLsbD 16 then n800 else n768
  let n802 := bif g.getLsbD 11 then n747 else false
  let n803 := bif g.getLsbD 10 then n536 else false
  let n804 := bif g.getLsbD 11 then false else n803
  let n805 := bif g.getLsbD 12 then n804 else n802
  let n806 := bif g.getLsbD 10 then n265 else false
  let n807 := bif g.getLsbD 11 then n779 else n806
  let n808 := bif g.getLsbD 12 then false else n807
  let n809 := bif g.getLsbD 13 then n808 else n805
  let n810 := bif g.getLsbD 10 then n283 else false
  let n811 := bif g.getLsbD 11 then n760 else n810
  let n812 := bif g.getLsbD 7 then n756 else false
  let n813 := bif g.getLsbD 8 then false else n812
  let n814 := bif g.getLsbD 9 then n813 else false
  let n815 := bif g.getLsbD 10 then false else n814
  let n816 := bif g.getLsbD 11 then false else n815
  let n817 := bif g.getLsbD 12 then n816 else n811
  let n818 := bif g.getLsbD 8 then n812 else false
  let n819 := bif g.getLsbD 7 then n791 else false
  let n820 := bif g.getLsbD 8 then false else n819
  let n821 := bif g.getLsbD 9 then n820 else n818
  let n822 := bif g.getLsbD 10 then false else n821
  let n823 := bif g.getLsbD 11 then false else n822
  let n824 := bif g.getLsbD 12 then false else n823
  let n825 := bif g.getLsbD 13 then n824 else n817
  let n826 := bif g.getLsbD 14 then n825 else n809
  let n827 := bif g.getLsbD 15 then false else n826
  let n828 := bif g.getLsbD 16 then false else n827
  let n829 := bif g.getLsbD 17 then n828 else n801
  let n830 := bif g.getLsbD 18 then n829 else n767
  let n831 := bif g.getLsbD 15 then n393 else false
  let n832 := bif g.getLsbD 10 then n152 else false
  let n833 := bif g.getLsbD 11 then n832 else false
  let n834 := bif g.getLsbD 12 then n752 else n833
  let n835 := bif g.getLsbD 13 then n789 else n834
  let n836 := bif g.getLsbD 10 then n348 else false
  let n837 := bif g.getLsbD 11 then false else n836
  let n838 := bif g.getLsbD 6 then n344 else false
  let n839 := bif g.getLsbD 7 then false else n838
  let n840 := bif g.getLsbD 8 then false else n839
  let n841 := bif g.getLsbD 9 then n840 else false
  let n842 := bif g.getLsbD 10 then false else n841
  let n843 := bif g.getLsbD 11 then false else n842
  let n844 := bif g.getLsbD 12 then n843 else n837
  let n845 := bif g.getLsbD 8 then n839 else false
  let n846 := bif g.getLsbD 6 then n353 else false
  let n847 := bif g.getLsbD 7 then false else n846
  let n848 := bif g.getLsbD 8 then false else n847
  let n849 := bif g.getLsbD 9 then n848 else n845
  let n850 := bif g.getLsbD 10 then false else n849
  let n851 := bif g.getLsbD 11 then false else n850
  let n852 := bif g.getLsbD 12 then false else n851
  let n853 := bif g.getLsbD 13 then n852 else n844
  let n854 := bif g.getLsbD 14 then n853 else n835
  let n855 := bif g.getLsbD 15 then false else n854
  let n856 := bif g.getLsbD 16 then n855 else n831
  let n857 := bif g.getLsbD 11 then n751 else false
  let n858 := bif g.getLsbD 10 then n542 else false
  let n859 := bif g.getLsbD 11 then false else n858
  let n860 := bif g.getLsbD 12 then n859 else n857
  let n861 := bif g.getLsbD 13 then n817 else n860
  let n862 := bif g.getLsbD 10 then n375 else false
  let n863 := bif g.getLsbD 11 then n842 else n862
  let n864 := bif g.getLsbD 12 then false else n863
  let n865 := bif g.getLsbD 7 then n838 else false
  let n866 := bif g.getLsbD 8 then false else n865
  let n867 := bif g.getLsbD 6 then n384 else false
  let n868 := bif g.getLsbD 7 then false else n867
  let n869 := bif g.getLsbD 8 then false else n868
  let n870 := bif g.getLsbD 9 then n869 else n866
  let n871 := bif g.getLsbD 10 then false else n870
  let n872 := bif g.getLsbD 11 then false else n871
  let n873 := bif g.getLsbD 12 then false else n872
  let n874 := bif g.getLsbD 13 then n873 else n864
  let n875 := bif g.getLsbD 14 then n874 else n861
  let n876 := bif g.getLsbD 15 then false else n875
  let n877 := bif g.getLsbD 16 then false else n876
  let n878 := bif g.getLsbD 17 then n877 else n856
  let n879 := bif g.getLsbD 11 then n783 else false
  let n880 := bif g.getLsbD 12 then n811 else n879
  let n881 := bif g.getLsbD 10 then n298 else false
  let n882 := bif g.getLsbD 11 then n795 else n881
  let n883 := bif g.getLsbD 12 then n823 else n882
  let n884 := bif g.getLsbD 13 then n883 else n880
  let n885 := bif g.getLsbD 10 then n388 else false
  let n886 := bif g.getLsbD 11 then n850 else n885
  let n887 := bif g.getLsbD 12 then n872 else n886
  let n888 := bif g.getLsbD 7 then n846 else false
  let n889 := bif g.getLsbD 8 then n868 else n888
  let n890 := bif g.getLsbD 9 then false else n889
  let n891 := bif g.getLsbD 10 then false else n890
  let n892 := bif g.getLsbD 11 then false else n891
  let n893 := bif g.getLsbD 12 then false else n892
  let n894 := bif g.getLsbD 13 then n893 else n887
  let n895 := bif g.getLsbD 14 then n894 else n884
  let n896 := bif g.getLsbD 15 then false else n895
  let n897 := bif g.getLsbD 16 then false else n896
  let n898 := bif g.getLsbD 17 then false else n897
  let n899 := bif g.getLsbD 18 then n898 else n878
  let n900 := bif g.getLsbD 19 then n899 else n830
  let n901 := bif g.getLsbD 15 then n467 else false
  let n902 := bif g.getLsbD 10 then n434 else false
  let n903 := bif g.getLsbD 11 then false else n902
  let n904 := bif g.getLsbD 12 then false else n903
  let n905 := bif g.getLsbD 9 then n790 else false
  let n906 := bif g.getLsbD 10 then false else n905
  let n907 := bif g.getLsbD 11 then false else n906
  let n908 := bif g.getLsbD 12 then false else n907
  let n909 := bif g.getLsbD 13 then n908 else n904
  let n910 := bif g.getLsbD 9 then n845 else false
  let n911 := bif g.getLsbD 10 then false else n910
  let n912 := bif g.getLsbD 11 then false else n911
  let n913 := bif g.getLsbD 12 then false else n912
  let n914 := bif g.getLsbD 13 then false else n913
  let n915 := bif g.getLsbD 14 then n914 else n909
  let n916 := bif g.getLsbD 15 then false else n915
  let n917 := bif g.getLsbD 16 then n916 else n901
  let n918 := bif g.getLsbD 10 then n453 else false
  let n919 := bif g.getLsbD 11 then false else n918
  let n920 := bif g.getLsbD 12 then false else n919
  let n921 := bif g.getLsbD 9 then n818 else false
  let n922 := bif g.getLsbD 10 then false else n921
  let n923 := bif g.getLsbD 11 then false else n922
  let n924 := bif g.getLsbD 12 then false else n923
  let n925 := bif g.getLsbD 13 then n924 else n920
  let n926 := bif g.getLsbD 9 then n866 else false
  let n927 := bif g.getLsbD 10 then false else n926
  let n928 := bif g.getLsbD 11 then false else n927
  let n929 := bif g.getLsbD 12 then false else n928
  let n930 := bif g.getLsbD 13 then false else n929
  let n931 := bif g.getLsbD 14 then n930 else n925
  let n932 := bif g.getLsbD 15 then false else n931
  let n933 := bif g.getLsbD 16 then false else n932
  let n934 := bif g.getLsbD 17 then n933 else n917
  let n935 := bif g.getLsbD 10 then n457 else false
  let n936 := bif g.getLsbD 11 then n906 else n935
  let n937 := bif g.getLsbD 12 then n923 else n936
  let n938 := bif g.getLsbD 8 then n819 else false
  let n939 := bif g.getLsbD 9 then n938 else false
  let n940 := bif g.getLsbD 10 then false else n939
  let n941 := bif g.getLsbD 11 then false else n940
  let n942 := bif g.getLsbD 12 then false else n941
  let n943 := bif g.getLsbD 13 then n942 else n937
  let n944 := bif g.getLsbD 8 then n865 else false
  let n945 := bif g.getLsbD 9 then n889 else n944
  let n946 := bif g.getLsbD 10 then false else n945
  let n947 := bif g.getLsbD 11 then false else n946
  let n948 := bif g.getLsbD 12 then false else n947
  let n949 := bif g.getLsbD 13 then false else n948
  let n950 := bif g.getLsbD 14 then n949 else n943
  let n951 := bif g.getLsbD 15 then false else n950
  let n952 := bif g.getLsbD 16 then false else n951
  let n953 := bif g.getLsbD 17 then false else n952
  let n954 := bif g.getLsbD 18 then n953 else n934
  let n955 := bif g.getLsbD 10 then n462 else false
  let n956 := bif g.getLsbD 11 then n911 else n955
  let n957 := bif g.getLsbD 12 then n928 else n956
  let n958 := bif g.getLsbD 13 then n948 else n957
  let n959 := bif g.getLsbD 6 then n495 else false
  let n960 := bif g.getLsbD 7 then false else n959
  let n961 := bif g.getLsbD 8 then false else n960
  let n962 := bif g.getLsbD 9 then n961 else false
  let n963 := bif g.getLsbD 10 then false else n962
  let n964 := bif g.getLsbD 11 then false else n963
  let n965 := bif g.getLsbD 12 then false else n964
  let n966 := bif g.getLsbD 13 then false else n965
  let n967 := bif g.getLsbD 14 then n966 else n958
  let n968 := bif g.getLsbD 15 then false else n967
  let n969 := bif g.getLsbD 16 then false else n968
  let n970 := bif g.getLsbD 17 then false else n969
  let n971 := bif g.getLsbD 18 then false else n970
  let n972 := bif g.getLsbD 19 then n971 else n954
  let n973 := bif g.getLsbD 20 then n972 else n900
  let n974 := bif g.getLsbD 21 then false else n973
  let n975 := bif g.getLsbD 22 then n974 else n743
  let n976 := bif g.getLsbD 23 then n975 else n512
  let n977 := bif g.getLsbD 16 then n222 else false
  let n978 := bif g.getLsbD 17 then n582 else n977
  let n979 := bif g.getLsbD 12 then n554 else false
  let n980 := bif g.getLsbD 13 then false else n979
  let n981 := bif g.getLsbD 11 then n217 else false
  let n982 := bif g.getLsbD 12 then n577 else n981
  let n983 := bif g.getLsbD 13 then false else n982
  let n984 := bif g.getLsbD 14 then n983 else n980
  let n985 := bif g.getLsbD 15 then n984 else false
  let n986 := bif g.getLsbD 11 then n224 else false
  let n987 := bif g.getLsbD 12 then n260 else n986
  let n988 := bif g.getLsbD 5 then false else n211
  let n989 := bif g.getLsbD 6 then n988 else false
  let n990 := bif g.getLsbD 7 then n989 else false
  let n991 := bif g.getLsbD 8 then n990 else false
  let n992 := bif g.getLsbD 9 then n991 else false
  let n993 := bif g.getLsbD 10 then false else n992
  let n994 := bif g.getLsbD 11 then false else n993
  let n995 := bif g.getLsbD 12 then n994 else false
  let n996 := bif g.getLsbD 13 then n995 else n987
  let n997 := bif g.getLsbD 9 then false else n474
  let n998 := bif g.getLsbD 10 then false else n997
  let n999 := bif g.getLsbD 11 then false else n998
  let n1000 := bif g.getLsbD 12 then false else n999
  let n1001 := bif g.getLsbD 13 then n1000 else n401
  let n1002 := bif g.getLsbD 14 then n1001 else n996
  let n1003 := bif g.getLsbD 15 then false else n1002
  let n1004 := bif g.getLsbD 16 then n1003 else n985
  let n1005 := bif g.getLsbD 11 then n259 else false
  let n1006 := bif g.getLsbD 12 then n587 else n1005
  let n1007 := bif g.getLsbD 11 then n993 else false
  let n1008 := bif g.getLsbD 12 then false else n1007
  let n1009 := bif g.getLsbD 13 then n1008 else n1006
  let n1010 := bif g.getLsbD 9 then false else n708
  let n1011 := bif g.getLsbD 10 then false else n1010
  let n1012 := bif g.getLsbD 11 then false else n1011
  let n1013 := bif g.getLsbD 12 then false else n1012
  let n1014 := bif g.getLsbD 13 then n1013 else n656
  let n1015 := bif g.getLsbD 14 then n1014 else n1009
  let n1016 := bif g.getLsbD 15 then false else n1015
  let n1017 := bif g.getLsbD 16 then false else n1016
  let n1018 := bif g.getLsbD 17 then n1017 else n1004
  let n1019 := bif g.getLsbD 18 then n1018 else n978
  let n1020 := bif g.getLsbD 11 then n205 else false
  let n1021 := bif g.getLsbD 12 then n569 else n1020
  let n1022 := bif g.getLsbD 13 then n982 else n1021
  let n1023 := bif g.getLsbD 11 then n332 else false
  let n1024 := bif g.getLsbD 12 then n626 else n1023
  let n1025 := bif g.getLsbD 8 then n622 else false
  let n1026 := bif g.getLsbD 9 then false else n1025
  let n1027 := bif g.getLsbD 10 then false else n1026
  let n1028 := bif g.getLsbD 11 then false else n1027
  let n1029 := bif g.getLsbD 12 then false else n1028
  let n1030 := bif g.getLsbD 13 then n1029 else n1024
  let n1031 := bif g.getLsbD 14 then n1030 else n1022
  let n1032 := bif g.getLsbD 15 then n1031 else false
  let n1033 := bif g.getLsbD 16 then n413 else n1032
  let n1034 := bif g.getLsbD 17 then n670 else n1033
  let n1035 := bif g.getLsbD 11 then n399 else false
  let n1036 := bif g.getLsbD 12 then n655 else n1035
  let n1037 := bif g.getLsbD 11 then n998 else false
  let n1038 := bif g.getLsbD 12 then n1012 else n1037
  let n1039 := bif g.getLsbD 13 then n1038 else n1036
  let n1040 := bif g.getLsbD 10 then n1026 else false
  let n1041 := bif g.getLsbD 11 then n408 else n1040
  let n1042 := bif g.getLsbD 12 then n665 else n1041
  let n1043 := bif g.getLsbD 13 then false else n1042
  let n1044 := bif g.getLsbD 14 then n1043 else n1039
  let n1045 := bif g.getLsbD 15 then false else n1044
  let n1046 := bif g.getLsbD 16 then false else n1045
  let n1047 := bif g.getLsbD 17 then false else n1046
  let n1048 := bif g.getLsbD 18 then n1047 else n1034
  let n1049 := bif g.getLsbD 19 then n1048 else n1019
  let n1050 := bif g.getLsbD 11 then n423 else false
  let n1051 := bif g.getLsbD 12 then n678 else n1050
  let n1052 := bif g.getLsbD 13 then false else n1051
  let n1053 := bif g.getLsbD 9 then n1025 else false
  let n1054 := bif g.getLsbD 10 then false else n1053
  let n1055 := bif g.getLsbD 11 then false else n1054
  let n1056 := bif g.getLsbD 12 then false else n1055
  let n1057 := bif g.getLsbD 13 then false else n1056
  let n1058 := bif g.getLsbD 14 then n1057 else n1052
  let n1059 := bif g.getLsbD 15 then n1058 else false
  let n1060 := bif g.getLsbD 16 then n487 else n1059
  let n1061 := bif g.getLsbD 17 then n722 else n1060
  let n1062 := bif g.getLsbD 11 then n476 else false
  let n1063 := bif g.getLsbD 12 then n711 else n1062
  let n1064 := bif g.getLsbD 13 then false else n1063
  let n1065 := bif g.getLsbD 8 then n661 else false
  let n1066 := bif g.getLsbD 9 then false else n1065
  let n1067 := bif g.getLsbD 10 then false else n1066
  let n1068 := bif g.getLsbD 11 then false else n1067
  let n1069 := bif g.getLsbD 12 then false else n1068
  let n1070 := bif g.getLsbD 13 then false else n1069
  let n1071 := bif g.getLsbD 14 then n1070 else n1064
  let n1072 := bif g.getLsbD 15 then false else n1071
  let n1073 := bif g.getLsbD 16 then false else n1072
  let n1074 := bif g.getLsbD 17 then false else n1073
  let n1075 := bif g.getLsbD 18 then n1074 else n1061
  let n1076 := bif g.getLsbD 10 then n1053 else false
  let n1077 := bif g.getLsbD 11 then n482 else n1076
  let n1078 := bif g.getLsbD 12 then n717 else n1077
  let n1079 := bif g.getLsbD 13 then n1069 else n1078
  let n1080 := bif g.getLsbD 8 then n729 else false
  let n1081 := bif g.getLsbD 9 then false else n1080
  let n1082 := bif g.getLsbD 10 then false else n1081
  let n1083 := bif g.getLsbD 11 then false else n1082
  let n1084 := bif g.getLsbD 12 then false else n1083
  let n1085 := bif g.getLsbD 13 then false else n1084
  let n1086 := bif g.getLsbD 14 then n1085 else n1079
  let n1087 := bif g.getLsbD 15 then false else n1086
  let n1088 := bif g.getLsbD 16 then false else n1087
  let n1089 := bif g.getLsbD 17 then false else n1088
  let n1090 := bif g.getLsbD 18 then false else n1089
  let n1091 := bif g.getLsbD 19 then n1090 else n1075
  let n1092 := bif g.getLsbD 20 then n1091 else n1049
  let n1093 := bif g.getLsbD 21 then n1092 else false
  let n1094 := bif g.getLsbD 15 then n252 else false
  let n1095 := bif g.getLsbD 16 then n1094 else false
  let n1096 := bif g.getLsbD 17 then n801 else n1095
  let n1097 := bif g.getLsbD 15 then n1002 else false
  let n1098 := bif g.getLsbD 12 then n773 else false
  let n1099 := bif g.getLsbD 13 then false else n1098
  let n1100 := bif g.getLsbD 10 then n247 else false
  let n1101 := bif g.getLsbD 11 then false else n1100
  let n1102 := bif g.getLsbD 12 then n796 else n1101
  let n1103 := bif g.getLsbD 13 then false else n1102
  let n1104 := bif g.getLsbD 14 then n1103 else n1099
  let n1105 := bif g.getLsbD 15 then false else n1104
  let n1106 := bif g.getLsbD 16 then n1105 else n1097
  let n1107 := bif g.getLsbD 11 then n772 else false
  let n1108 := bif g.getLsbD 12 then n807 else n1107
  let n1109 := bif g.getLsbD 10 then n992 else false
  let n1110 := bif g.getLsbD 11 then false else n1109
  let n1111 := bif g.getLsbD 12 then false else n1110
  let n1112 := bif g.getLsbD 13 then n1111 else n1108
  let n1113 := bif g.getLsbD 9 then false else n938
  let n1114 := bif g.getLsbD 10 then false else n1113
  let n1115 := bif g.getLsbD 11 then false else n1114
  let n1116 := bif g.getLsbD 12 then false else n1115
  let n1117 := bif g.getLsbD 13 then n1116 else n883
  let n1118 := bif g.getLsbD 14 then n1117 else n1112
  let n1119 := bif g.getLsbD 15 then false else n1118
  let n1120 := bif g.getLsbD 16 then false else n1119
  let n1121 := bif g.getLsbD 17 then n1120 else n1106
  let n1122 := bif g.getLsbD 18 then n1121 else n1096
  let n1123 := bif g.getLsbD 15 then n412 else false
  let n1124 := bif g.getLsbD 10 then n239 else false
  let n1125 := bif g.getLsbD 11 then n1124 else false
  let n1126 := bif g.getLsbD 12 then n788 else n1125
  let n1127 := bif g.getLsbD 13 then n1102 else n1126
  let n1128 := bif g.getLsbD 10 then n357 else false
  let n1129 := bif g.getLsbD 11 then false else n1128
  let n1130 := bif g.getLsbD 12 then n851 else n1129
  let n1131 := bif g.getLsbD 8 then n847 else false
  let n1132 := bif g.getLsbD 9 then false else n1131
  let n1133 := bif g.getLsbD 10 then false else n1132
  let n1134 := bif g.getLsbD 11 then false else n1133
  let n1135 := bif g.getLsbD 12 then false else n1134
  let n1136 := bif g.getLsbD 13 then n1135 else n1130
  let n1137 := bif g.getLsbD 14 then n1136 else n1127
  let n1138 := bif g.getLsbD 15 then false else n1137
  let n1139 := bif g.getLsbD 16 then n1138 else n1123
  let n1140 := bif g.getLsbD 17 then n897 else n1139
  let n1141 := bif g.getLsbD 11 then n1100 else false
  let n1142 := bif g.getLsbD 12 then n882 else n1141
  let n1143 := bif g.getLsbD 10 then n997 else false
  let n1144 := bif g.getLsbD 11 then false else n1143
  let n1145 := bif g.getLsbD 12 then n1115 else n1144
  let n1146 := bif g.getLsbD 13 then n1145 else n1142
  let n1147 := bif g.getLsbD 10 then n407 else false
  let n1148 := bif g.getLsbD 11 then n1133 else n1147
  let n1149 := bif g.getLsbD 12 then n892 else n1148
  let n1150 := bif g.getLsbD 13 then false else n1149
  let n1151 := bif g.getLsbD 14 then n1150 else n1146
  let n1152 := bif g.getLsbD 15 then false else n1151
  let n1153 := bif g.getLsbD 16 then false else n1152
  let n1154 := bif g.getLsbD 17 then false else n1153
  let n1155 := bif g.getLsbD 18 then n1154 else n1140
  let n1156 := bif g.getLsbD 19 then n1155 else n1122
  let n1157 := bif g.getLsbD 15 then n486 else false
  let n1158 := bif g.getLsbD 10 then n438 else false
  let n1159 := bif g.getLsbD 11 then false else n1158
  let n1160 := bif g.getLsbD 12 then n907 else n1159
  let n1161 := bif g.getLsbD 13 then false else n1160
  let n1162 := bif g.getLsbD 9 then n1131 else false
  let n1163 := bif g.getLsbD 10 then false else n1162
  let n1164 := bif g.getLsbD 11 then false else n1163
  let n1165 := bif g.getLsbD 12 then false else n1164
  let n1166 := bif g.getLsbD 13 then false else n1165
  let n1167 := bif g.getLsbD 14 then n1166 else n1161
  let n1168 := bif g.getLsbD 15 then false else n1167
  let n1169 := bif g.getLsbD 16 then n1168 else n1157
  let n1170 := bif g.getLsbD 17 then n952 else n1169
  let n1171 := bif g.getLsbD 10 then n475 else false
  let n1172 := bif g.getLsbD 11 then false else n1171
  let n1173 := bif g.getLsbD 12 then n941 else n1172
  let n1174 := bif g.getLsbD 13 then false else n1173
  let n1175 := bif g.getLsbD 8 then n888 else false
  let n1176 := bif g.getLsbD 9 then false else n1175
  let n1177 := bif g.getLsbD 10 then false else n1176
  let n1178 := bif g.getLsbD 11 then false else n1177
  let n1179 := bif g.getLsbD 12 then false else n1178
  let n1180 := bif g.getLsbD 13 then false else n1179
  let n1181 := bif g.getLsbD 14 then n1180 else n1174
  let n1182 := bif g.getLsbD 15 then false else n1181
  let n1183 := bif g.getLsbD 16 then false else n1182
  let n1184 := bif g.getLsbD 17 then false else n1183
  let n1185 := bif g.getLsbD 18 then n1184 else n1170
  let n1186 := bif g.getLsbD 10 then n481 else false
  let n1187 := bif g.getLsbD 11 then n1163 else n1186
  let n1188 := bif g.getLsbD 12 then n947 else n1187
  let n1189 := bif g.getLsbD 13 then n1179 else n1188
  let n1190 := bif g.getLsbD 8 then n960 else false
  let n1191 := bif g.getLsbD 9 then false else n1190
  let n1192 := bif g.getLsbD 10 then false else n1191
  let n1193 := bif g.getLsbD 11 then false else n1192
  let n1194 := bif g.getLsbD 12 then false else n1193
  let n1195 := bif g.getLsbD 13 then false else n1194
  let n1196 := bif g.getLsbD 14 then n1195 else n1189
  let n1197 := bif g.getLsbD 15 then false else n1196
  let n1198 := bif g.getLsbD 16 then false else n1197
  let n1199 := bif g.getLsbD 17 then false else n1198
  let n1200 := bif g.getLsbD 18 then false else n1199
  let n1201 := bif g.getLsbD 19 then n1200 else n1185
  let n1202 := bif g.getLsbD 20 then n1201 else n1156
  let n1203 := bif g.getLsbD 21 then false else n1202
  let n1204 := bif g.getLsbD 22 then n1203 else n1093
  let n1205 := bif g.getLsbD 16 then n768 else false
  let n1206 := bif g.getLsbD 15 then n606 else false
  let n1207 := bif g.getLsbD 16 then n827 else n1206
  let n1208 := bif g.getLsbD 17 then n1207 else n1205
  let n1209 := bif g.getLsbD 15 then n1015 else false
  let n1210 := bif g.getLsbD 16 then n1119 else n1209
  let n1211 := bif g.getLsbD 11 then n806 else false
  let n1212 := bif g.getLsbD 12 then false else n1211
  let n1213 := bif g.getLsbD 13 then false else n1212
  let n1214 := bif g.getLsbD 10 then n601 else false
  let n1215 := bif g.getLsbD 11 then n822 else n1214
  let n1216 := bif g.getLsbD 12 then false else n1215
  let n1217 := bif g.getLsbD 13 then false else n1216
  let n1218 := bif g.getLsbD 14 then n1217 else n1213
  let n1219 := bif g.getLsbD 15 then false else n1218
  let n1220 := bif g.getLsbD 16 then false else n1219
  let n1221 := bif g.getLsbD 17 then n1220 else n1210
  let n1222 := bif g.getLsbD 18 then n1221 else n1208
  let n1223 := bif g.getLsbD 15 then n668 else false
  let n1224 := bif g.getLsbD 16 then n896 else n1223
  let n1225 := bif g.getLsbD 11 then n810 else false
  let n1226 := bif g.getLsbD 10 then n594 else false
  let n1227 := bif g.getLsbD 11 then n815 else n1226
  let n1228 := bif g.getLsbD 12 then n1227 else n1225
  let n1229 := bif g.getLsbD 13 then n1216 else n1228
  let n1230 := bif g.getLsbD 10 then n643 else false
  let n1231 := bif g.getLsbD 11 then n871 else n1230
  let n1232 := bif g.getLsbD 12 then false else n1231
  let n1233 := bif g.getLsbD 7 then n867 else false
  let n1234 := bif g.getLsbD 8 then false else n1233
  let n1235 := bif g.getLsbD 9 then false else n1234
  let n1236 := bif g.getLsbD 10 then false else n1235
  let n1237 := bif g.getLsbD 11 then false else n1236
  let n1238 := bif g.getLsbD 12 then false else n1237
  let n1239 := bif g.getLsbD 13 then n1238 else n1232
  let n1240 := bif g.getLsbD 14 then n1239 else n1229
  let n1241 := bif g.getLsbD 15 then false else n1240
  let n1242 := bif g.getLsbD 16 then false else n1241
  let n1243 := bif g.getLsbD 17 then n1242 else n1224
  let n1244 := bif g.getLsbD 11 then n881 else false
  let n1245 := bif g.getLsbD 12 then n1215 else n1244
  let n1246 := bif g.getLsbD 10 then n1010 else false
  let n1247 := bif g.getLsbD 11 then n1114 else n1246
  let n1248 := bif g.getLsbD 12 then false else n1247
  let n1249 := bif g.getLsbD 13 then n1248 else n1245
  let n1250 := bif g.getLsbD 10 then n663 else false
  let n1251 := bif g.getLsbD 11 then n891 else n1250
  let n1252 := bif g.getLsbD 12 then n1237 else n1251
  let n1253 := bif g.getLsbD 13 then false else n1252
  let n1254 := bif g.getLsbD 14 then n1253 else n1249
  let n1255 := bif g.getLsbD 15 then false else n1254
  let n1256 := bif g.getLsbD 16 then false else n1255
  let n1257 := bif g.getLsbD 17 then false else n1256
  let n1258 := bif g.getLsbD 18 then n1257 else n1243
  let n1259 := bif g.getLsbD 19 then n1258 else n1222
  let n1260 := bif g.getLsbD 15 then n720 else false
  let n1261 := bif g.getLsbD 16 then n951 else n1260
  let n1262 := bif g.getLsbD 10 then n691 else false
  let n1263 := bif g.getLsbD 11 then n922 else n1262
  let n1264 := bif g.getLsbD 12 then false else n1263
  let n1265 := bif g.getLsbD 13 then false else n1264
  let n1266 := bif g.getLsbD 9 then n1234 else false
  let n1267 := bif g.getLsbD 10 then false else n1266
  let n1268 := bif g.getLsbD 11 then false else n1267
  let n1269 := bif g.getLsbD 12 then false else n1268
  let n1270 := bif g.getLsbD 13 then false else n1269
  let n1271 := bif g.getLsbD 14 then n1270 else n1265
  let n1272 := bif g.getLsbD 15 then false else n1271
  let n1273 := bif g.getLsbD 16 then false else n1272
  let n1274 := bif g.getLsbD 17 then n1273 else n1261
  let n1275 := bif g.getLsbD 10 then n709 else false
  let n1276 := bif g.getLsbD 11 then n940 else n1275
  let n1277 := bif g.getLsbD 12 then false else n1276
  let n1278 := bif g.getLsbD 13 then false else n1277
  let n1279 := bif g.getLsbD 8 then n1233 else false
  let n1280 := bif g.getLsbD 9 then false else n1279
  let n1281 := bif g.getLsbD 10 then false else n1280
  let n1282 := bif g.getLsbD 11 then false else n1281
  let n1283 := bif g.getLsbD 12 then false else n1282
  let n1284 := bif g.getLsbD 13 then false else n1283
  let n1285 := bif g.getLsbD 14 then n1284 else n1278
  let n1286 := bif g.getLsbD 15 then false else n1285
  let n1287 := bif g.getLsbD 16 then false else n1286
  let n1288 := bif g.getLsbD 17 then false else n1287
  let n1289 := bif g.getLsbD 18 then n1288 else n1274
  let n1290 := bif g.getLsbD 10 then n715 else false
  let n1291 := bif g.getLsbD 11 then n946 else n1290
  let n1292 := bif g.getLsbD 12 then n1268 else n1291
  let n1293 := bif g.getLsbD 13 then n1283 else n1292
  let n1294 := bif g.getLsbD 7 then n959 else false
  let n1295 := bif g.getLsbD 8 then false else n1294
  let n1296 := bif g.getLsbD 9 then false else n1295
  let n1297 := bif g.getLsbD 10 then false else n1296
  let n1298 := bif g.getLsbD 11 then false else n1297
  let n1299 := bif g.getLsbD 12 then false else n1298
  let n1300 := bif g.getLsbD 13 then false else n1299
  let n1301 := bif g.getLsbD 14 then n1300 else n1293
  let n1302 := bif g.getLsbD 15 then false else n1301
  let n1303 := bif g.getLsbD 16 then false else n1302
  let n1304 := bif g.getLsbD 17 then false else n1303
  let n1305 := bif g.getLsbD 18 then false else n1304
  let n1306 := bif g.getLsbD 19 then n1305 else n1289
  let n1307 := bif g.getLsbD 20 then n1306 else n1259
  let n1308 := bif g.getLsbD 21 then false else n1307
  let n1309 := bif g.getLsbD 22 then false else n1308
  let n1310 := bif g.getLsbD 23 then n1309 else n1204
  let n1311 := bif g.getLsbD 24 then n1310 else n976
  let n1312 := bif g.getLsbD 16 then n337 else false
  let n1313 := bif g.getLsbD 17 then n631 else n1312
  let n1314 := bif g.getLsbD 18 then n1034 else n1313
  let n1315 := bif g.getLsbD 12 then n614 else false
  let n1316 := bif g.getLsbD 13 then n1024 else n1315
  let n1317 := bif g.getLsbD 14 then false else n1316
  let n1318 := bif g.getLsbD 15 then n1317 else false
  let n1319 := bif g.getLsbD 11 then n340 else false
  let n1320 := bif g.getLsbD 12 then n371 else n1319
  let n1321 := bif g.getLsbD 13 then n405 else n1320
  let n1322 := bif g.getLsbD 8 then false else n497
  let n1323 := bif g.getLsbD 9 then n1322 else false
  let n1324 := bif g.getLsbD 10 then false else n1323
  let n1325 := bif g.getLsbD 11 then false else n1324
  let n1326 := bif g.getLsbD 12 then n1325 else false
  let n1327 := bif g.getLsbD 9 then false else n498
  let n1328 := bif g.getLsbD 10 then false else n1327
  let n1329 := bif g.getLsbD 11 then false else n1328
  let n1330 := bif g.getLsbD 12 then false else n1329
  let n1331 := bif g.getLsbD 13 then n1330 else n1326
  let n1332 := bif g.getLsbD 14 then n1331 else n1321
  let n1333 := bif g.getLsbD 15 then false else n1332
  let n1334 := bif g.getLsbD 16 then n1333 else n1318
  let n1335 := bif g.getLsbD 11 then n370 else false
  let n1336 := bif g.getLsbD 12 then n637 else n1335
  let n1337 := bif g.getLsbD 13 then n660 else n1336
  let n1338 := bif g.getLsbD 11 then n1324 else false
  let n1339 := bif g.getLsbD 12 then false else n1338
  let n1340 := bif g.getLsbD 9 then false else n730
  let n1341 := bif g.getLsbD 10 then false else n1340
  let n1342 := bif g.getLsbD 11 then false else n1341
  let n1343 := bif g.getLsbD 12 then false else n1342
  let n1344 := bif g.getLsbD 13 then n1343 else n1339
  let n1345 := bif g.getLsbD 14 then n1344 else n1337
  let n1346 := bif g.getLsbD 15 then false else n1345
  let n1347 := bif g.getLsbD 16 then false else n1346
  let n1348 := bif g.getLsbD 17 then n1347 else n1334
  let n1349 := bif g.getLsbD 11 then n403 else false
  let n1350 := bif g.getLsbD 12 then n659 else n1349
  let n1351 := bif g.getLsbD 13 then n1042 else n1350
  let n1352 := bif g.getLsbD 11 then n1328 else false
  let n1353 := bif g.getLsbD 12 then n1342 else n1352
  let n1354 := bif g.getLsbD 13 then false else n1353
  let n1355 := bif g.getLsbD 14 then n1354 else n1351
  let n1356 := bif g.getLsbD 15 then false else n1355
  let n1357 := bif g.getLsbD 16 then false else n1356
  let n1358 := bif g.getLsbD 17 then false else n1357
  let n1359 := bif g.getLsbD 18 then n1358 else n1348
  let n1360 := bif g.getLsbD 19 then n1359 else n1314
  let n1361 := bif g.getLsbD 11 then n428 else false
  let n1362 := bif g.getLsbD 12 then n683 else n1361
  let n1363 := bif g.getLsbD 13 then n1056 else n1362
  let n1364 := bif g.getLsbD 14 then false else n1363
  let n1365 := bif g.getLsbD 15 then n1364 else false
  let n1366 := bif g.getLsbD 16 then n505 else n1365
  let n1367 := bif g.getLsbD 17 then n738 else n1366
  let n1368 := bif g.getLsbD 18 then n1089 else n1367
  let n1369 := bif g.getLsbD 11 then n500 else false
  let n1370 := bif g.getLsbD 12 then n733 else n1369
  let n1371 := bif g.getLsbD 13 then n1084 else n1370
  let n1372 := bif g.getLsbD 14 then false else n1371
  let n1373 := bif g.getLsbD 15 then false else n1372
  let n1374 := bif g.getLsbD 16 then false else n1373
  let n1375 := bif g.getLsbD 17 then false else n1374
  let n1376 := bif g.getLsbD 18 then false else n1375
  let n1377 := bif g.getLsbD 19 then n1376 else n1368
  let n1378 := bif g.getLsbD 20 then n1377 else n1360
  let n1379 := bif g.getLsbD 21 then n1378 else false
  let n1380 := bif g.getLsbD 15 then n362 else false
  let n1381 := bif g.getLsbD 16 then n1380 else false
  let n1382 := bif g.getLsbD 17 then n856 else n1381
  let n1383 := bif g.getLsbD 18 then n1140 else n1382
  let n1384 := bif g.getLsbD 15 then n1332 else false
  let n1385 := bif g.getLsbD 12 then n837 else false
  let n1386 := bif g.getLsbD 13 then n1130 else n1385
  let n1387 := bif g.getLsbD 14 then false else n1386
  let n1388 := bif g.getLsbD 15 then false else n1387
  let n1389 := bif g.getLsbD 16 then n1388 else n1384
  let n1390 := bif g.getLsbD 11 then n836 else false
  let n1391 := bif g.getLsbD 12 then n863 else n1390
  let n1392 := bif g.getLsbD 13 then n887 else n1391
  let n1393 := bif g.getLsbD 10 then n1323 else false
  let n1394 := bif g.getLsbD 11 then false else n1393
  let n1395 := bif g.getLsbD 12 then false else n1394
  let n1396 := bif g.getLsbD 9 then false else n961
  let n1397 := bif g.getLsbD 10 then false else n1396
  let n1398 := bif g.getLsbD 11 then false else n1397
  let n1399 := bif g.getLsbD 12 then false else n1398
  let n1400 := bif g.getLsbD 13 then n1399 else n1395
  let n1401 := bif g.getLsbD 14 then n1400 else n1392
  let n1402 := bif g.getLsbD 15 then false else n1401
  let n1403 := bif g.getLsbD 16 then false else n1402
  let n1404 := bif g.getLsbD 17 then n1403 else n1389
  let n1405 := bif g.getLsbD 11 then n1128 else false
  let n1406 := bif g.getLsbD 12 then n886 else n1405
  let n1407 := bif g.getLsbD 13 then n1149 else n1406
  let n1408 := bif g.getLsbD 10 then n1327 else false
  let n1409 := bif g.getLsbD 11 then false else n1408
  let n1410 := bif g.getLsbD 12 then n1398 else n1409
  let n1411 := bif g.getLsbD 13 then false else n1410
  let n1412 := bif g.getLsbD 14 then n1411 else n1407
  let n1413 := bif g.getLsbD 15 then false else n1412
  let n1414 := bif g.getLsbD 16 then false else n1413
  let n1415 := bif g.getLsbD 17 then false else n1414
  let n1416 := bif g.getLsbD 18 then n1415 else n1404
  let n1417 := bif g.getLsbD 19 then n1416 else n1383
  let n1418 := bif g.getLsbD 15 then n504 else false
  let n1419 := bif g.getLsbD 10 then n443 else false
  let n1420 := bif g.getLsbD 11 then false else n1419
  let n1421 := bif g.getLsbD 12 then n912 else n1420
  let n1422 := bif g.getLsbD 13 then n1165 else n1421
  let n1423 := bif g.getLsbD 14 then false else n1422
  let n1424 := bif g.getLsbD 15 then false else n1423
  let n1425 := bif g.getLsbD 16 then n1424 else n1418
  let n1426 := bif g.getLsbD 17 then n969 else n1425
  let n1427 := bif g.getLsbD 18 then n1199 else n1426
  let n1428 := bif g.getLsbD 10 then n499 else false
  let n1429 := bif g.getLsbD 11 then false else n1428
  let n1430 := bif g.getLsbD 12 then n964 else n1429
  let n1431 := bif g.getLsbD 13 then n1194 else n1430
  let n1432 := bif g.getLsbD 14 then false else n1431
  let n1433 := bif g.getLsbD 15 then false else n1432
  let n1434 := bif g.getLsbD 16 then false else n1433
  let n1435 := bif g.getLsbD 17 then false else n1434
  let n1436 := bif g.getLsbD 18 then false else n1435
  let n1437 := bif g.getLsbD 19 then n1436 else n1427
  let n1438 := bif g.getLsbD 20 then n1437 else n1417
  let n1439 := bif g.getLsbD 21 then false else n1438
  let n1440 := bif g.getLsbD 22 then n1439 else n1379
  let n1441 := bif g.getLsbD 16 then n831 else false
  let n1442 := bif g.getLsbD 15 then n648 else false
  let n1443 := bif g.getLsbD 16 then n876 else n1442
  let n1444 := bif g.getLsbD 17 then n1443 else n1441
  let n1445 := bif g.getLsbD 18 then n1243 else n1444
  let n1446 := bif g.getLsbD 15 then n1345 else false
  let n1447 := bif g.getLsbD 16 then n1402 else n1446
  let n1448 := bif g.getLsbD 11 then n862 else false
  let n1449 := bif g.getLsbD 12 then false else n1448
  let n1450 := bif g.getLsbD 13 then n1232 else n1449
  let n1451 := bif g.getLsbD 14 then false else n1450
  let n1452 := bif g.getLsbD 15 then false else n1451
  let n1453 := bif g.getLsbD 16 then false else n1452
  let n1454 := bif g.getLsbD 17 then n1453 else n1447
  let n1455 := bif g.getLsbD 11 then n885 else false
  let n1456 := bif g.getLsbD 12 then n1231 else n1455
  let n1457 := bif g.getLsbD 13 then n1252 else n1456
  let n1458 := bif g.getLsbD 10 then n1340 else false
  let n1459 := bif g.getLsbD 11 then n1397 else n1458
  let n1460 := bif g.getLsbD 12 then false else n1459
  let n1461 := bif g.getLsbD 13 then false else n1460
  let n1462 := bif g.getLsbD 14 then n1461 else n1457
  let n1463 := bif g.getLsbD 15 then false else n1462
  let n1464 := bif g.getLsbD 16 then false else n1463
  let n1465 := bif g.getLsbD 17 then false else n1464
  let n1466 := bif g.getLsbD 18 then n1465 else n1454
  let n1467 := bif g.getLsbD 19 then n1466 else n1445
  let n1468 := bif g.getLsbD 15 then n736 else false
  let n1469 := bif g.getLsbD 16 then n968 else n1468
  let n1470 := bif g.getLsbD 10 then n696 else false
  let n1471 := bif g.getLsbD 11 then n927 else n1470
  let n1472 := bif g.getLsbD 12 then false else n1471
  let n1473 := bif g.getLsbD 13 then n1269 else n1472
  let n1474 := bif g.getLsbD 14 then false else n1473
  let n1475 := bif g.getLsbD 15 then false else n1474
  let n1476 := bif g.getLsbD 16 then false else n1475
  let n1477 := bif g.getLsbD 17 then n1476 else n1469
  let n1478 := bif g.getLsbD 18 then n1304 else n1477
  let n1479 := bif g.getLsbD 10 then n731 else false
  let n1480 := bif g.getLsbD 11 then n963 else n1479
  let n1481 := bif g.getLsbD 12 then false else n1480
  let n1482 := bif g.getLsbD 13 then n1299 else n1481
  let n1483 := bif g.getLsbD 14 then false else n1482
  let n1484 := bif g.getLsbD 15 then false else n1483
  let n1485 := bif g.getLsbD 16 then false else n1484
  let n1486 := bif g.getLsbD 17 then false else n1485
  let n1487 := bif g.getLsbD 18 then false else n1486
  let n1488 := bif g.getLsbD 19 then n1487 else n1478
  let n1489 := bif g.getLsbD 20 then n1488 else n1467
  let n1490 := bif g.getLsbD 21 then false else n1489
  let n1491 := bif g.getLsbD 22 then false else n1490
  let n1492 := bif g.getLsbD 23 then n1491 else n1440
  let n1493 := bif g.getLsbD 16 then n1123 else false
  let n1494 := bif g.getLsbD 17 then n1224 else n1493
  let n1495 := bif g.getLsbD 15 then n1044 else false
  let n1496 := bif g.getLsbD 16 then n1152 else n1495
  let n1497 := bif g.getLsbD 17 then n1256 else n1496
  let n1498 := bif g.getLsbD 18 then n1497 else n1494
  let n1499 := bif g.getLsbD 15 then n1355 else false
  let n1500 := bif g.getLsbD 16 then n1413 else n1499
  let n1501 := bif g.getLsbD 17 then n1464 else n1500
  let n1502 := bif g.getLsbD 11 then n1147 else false
  let n1503 := bif g.getLsbD 12 then n1251 else n1502
  let n1504 := bif g.getLsbD 13 then false else n1503
  let n1505 := bif g.getLsbD 14 then false else n1504
  let n1506 := bif g.getLsbD 15 then false else n1505
  let n1507 := bif g.getLsbD 16 then false else n1506
  let n1508 := bif g.getLsbD 17 then false else n1507
  let n1509 := bif g.getLsbD 18 then n1508 else n1501
  let n1510 := bif g.getLsbD 19 then n1509 else n1498
  let n1511 := bif g.getLsbD 15 then n1086 else false
  let n1512 := bif g.getLsbD 16 then n1197 else n1511
  let n1513 := bif g.getLsbD 17 then n1303 else n1512
  let n1514 := bif g.getLsbD 10 then n1066 else false
  let n1515 := bif g.getLsbD 11 then n1177 else n1514
  let n1516 := bif g.getLsbD 12 then n1282 else n1515
  let n1517 := bif g.getLsbD 13 then false else n1516
  let n1518 := bif g.getLsbD 14 then false else n1517
  let n1519 := bif g.getLsbD 15 then false else n1518
  let n1520 := bif g.getLsbD 16 then false else n1519
  let n1521 := bif g.getLsbD 17 then false else n1520
  let n1522 := bif g.getLsbD 18 then n1521 else n1513
  let n1523 := bif g.getLsbD 10 then n1081 else false
  let n1524 := bif g.getLsbD 11 then n1192 else n1523
  let n1525 := bif g.getLsbD 12 then n1298 else n1524
  let n1526 := bif g.getLsbD 13 then false else n1525
  let n1527 := bif g.getLsbD 14 then false else n1526
  let n1528 := bif g.getLsbD 15 then false else n1527
  let n1529 := bif g.getLsbD 16 then false else n1528
  let n1530 := bif g.getLsbD 17 then false else n1529
  let n1531 := bif g.getLsbD 18 then false else n1530
  let n1532 := bif g.getLsbD 19 then n1531 else n1522
  let n1533 := bif g.getLsbD 20 then n1532 else n1510
  let n1534 := bif g.getLsbD 21 then false else n1533
  let n1535 := bif g.getLsbD 22 then false else n1534
  let n1536 := bif g.getLsbD 23 then false else n1535
  let n1537 := bif g.getLsbD 24 then n1536 else n1492
  let n1538 := bif g.getLsbD 25 then n1537 else n1311
  let n1539 := bif g.getLsbD 16 then n433 else false
  let n1540 := bif g.getLsbD 17 then n688 else n1539
  let n1541 := bif g.getLsbD 18 then n1061 else n1540
  let n1542 := bif g.getLsbD 19 then n1368 else n1541
  let n1543 := bif g.getLsbD 9 then n480 else false
  let n1544 := bif g.getLsbD 10 then false else n1543
  let n1545 := bif g.getLsbD 11 then false else n1544
  let n1546 := bif g.getLsbD 12 then false else n1545
  let n1547 := bif g.getLsbD 13 then false else n1546
  let n1548 := bif g.getLsbD 14 then false else n1547
  let n1549 := bif g.getLsbD 15 then false else n1548
  let n1550 := bif g.getLsbD 16 then n1549 else false
  let n1551 := bif g.getLsbD 9 then n714 else false
  let n1552 := bif g.getLsbD 10 then false else n1551
  let n1553 := bif g.getLsbD 11 then false else n1552
  let n1554 := bif g.getLsbD 12 then false else n1553
  let n1555 := bif g.getLsbD 13 then false else n1554
  let n1556 := bif g.getLsbD 14 then false else n1555
  let n1557 := bif g.getLsbD 15 then false else n1556
  let n1558 := bif g.getLsbD 16 then false else n1557
  let n1559 := bif g.getLsbD 17 then n1558 else n1550
  let n1560 := bif g.getLsbD 9 then n1065 else false
  let n1561 := bif g.getLsbD 10 then false else n1560
  let n1562 := bif g.getLsbD 11 then false else n1561
  let n1563 := bif g.getLsbD 12 then false else n1562
  let n1564 := bif g.getLsbD 13 then false else n1563
  let n1565 := bif g.getLsbD 14 then false else n1564
  let n1566 := bif g.getLsbD 15 then false else n1565
  let n1567 := bif g.getLsbD 16 then false else n1566
  let n1568 := bif g.getLsbD 17 then false else n1567
  let n1569 := bif g.getLsbD 18 then n1568 else n1559
  let n1570 := bif g.getLsbD 9 then n1080 else false
  let n1571 := bif g.getLsbD 10 then false else n1570
  let n1572 := bif g.getLsbD 11 then false else n1571
  let n1573 := bif g.getLsbD 12 then false else n1572
  let n1574 := bif g.getLsbD 13 then false else n1573
  let n1575 := bif g.getLsbD 14 then false else n1574
  let n1576 := bif g.getLsbD 15 then false else n1575
  let n1577 := bif g.getLsbD 16 then false else n1576
  let n1578 := bif g.getLsbD 17 then false else n1577
  let n1579 := bif g.getLsbD 18 then false else n1578
  let n1580 := bif g.getLsbD 19 then n1579 else n1569
  let n1581 := bif g.getLsbD 20 then n1580 else n1542
  let n1582 := bif g.getLsbD 21 then n1581 else false
  let n1583 := bif g.getLsbD 15 then n448 else false
  let n1584 := bif g.getLsbD 16 then n1583 else false
  let n1585 := bif g.getLsbD 17 then n917 else n1584
  let n1586 := bif g.getLsbD 18 then n1170 else n1585
  let n1587 := bif g.getLsbD 19 then n1427 else n1586
  let n1588 := bif g.getLsbD 15 then n1548 else false
  let n1589 := bif g.getLsbD 16 then false else n1588
  let n1590 := bif g.getLsbD 9 then n944 else false
  let n1591 := bif g.getLsbD 10 then false else n1590
  let n1592 := bif g.getLsbD 11 then false else n1591
  let n1593 := bif g.getLsbD 12 then false else n1592
  let n1594 := bif g.getLsbD 13 then false else n1593
  let n1595 := bif g.getLsbD 14 then false else n1594
  let n1596 := bif g.getLsbD 15 then false else n1595
  let n1597 := bif g.getLsbD 16 then false else n1596
  let n1598 := bif g.getLsbD 17 then n1597 else n1589
  let n1599 := bif g.getLsbD 9 then n1175 else false
  let n1600 := bif g.getLsbD 10 then false else n1599
  let n1601 := bif g.getLsbD 11 then false else n1600
  let n1602 := bif g.getLsbD 12 then false else n1601
  let n1603 := bif g.getLsbD 13 then false else n1602
  let n1604 := bif g.getLsbD 14 then false else n1603
  let n1605 := bif g.getLsbD 15 then false else n1604
  let n1606 := bif g.getLsbD 16 then false else n1605
  let n1607 := bif g.getLsbD 17 then false else n1606
  let n1608 := bif g.getLsbD 18 then n1607 else n1598
  let n1609 := bif g.getLsbD 9 then n1190 else false
  let n1610 := bif g.getLsbD 10 then false else n1609
  let n1611 := bif g.getLsbD 11 then false else n1610
  let n1612 := bif g.getLsbD 12 then false else n1611
  let n1613 := bif g.getLsbD 13 then false else n1612
  let n1614 := bif g.getLsbD 14 then false else n1613
  let n1615 := bif g.getLsbD 15 then false else n1614
  let n1616 := bif g.getLsbD 16 then false else n1615
  let n1617 := bif g.getLsbD 17 then false else n1616
  let n1618 := bif g.getLsbD 18 then false else n1617
  let n1619 := bif g.getLsbD 19 then n1618 else n1608
  let n1620 := bif g.getLsbD 20 then n1619 else n1587
  let n1621 := bif g.getLsbD 21 then false else n1620
  let n1622 := bif g.getLsbD 22 then n1621 else n1582
  let n1623 := bif g.getLsbD 16 then n901 else false
  let n1624 := bif g.getLsbD 15 then n701 else false
  let n1625 := bif g.getLsbD 16 then n932 else n1624
  let n1626 := bif g.getLsbD 17 then n1625 else n1623
  let n1627 := bif g.getLsbD 18 then n1274 else n1626
  let n1628 := bif g.getLsbD 19 then n1478 else n1627
  let n1629 := bif g.getLsbD 15 then n1556 else false
  let n1630 := bif g.getLsbD 16 then n1596 else n1629
  let n1631 := bif g.getLsbD 17 then false else n1630
  let n1632 := bif g.getLsbD 9 then n1279 else false
  let n1633 := bif g.getLsbD 10 then false else n1632
  let n1634 := bif g.getLsbD 11 then false else n1633
  let n1635 := bif g.getLsbD 12 then false else n1634
  let n1636 := bif g.getLsbD 13 then false else n1635
  let n1637 := bif g.getLsbD 14 then false else n1636
  let n1638 := bif g.getLsbD 15 then false else n1637
  let n1639 := bif g.getLsbD 16 then false else n1638
  let n1640 := bif g.getLsbD 17 then false else n1639
  let n1641 := bif g.getLsbD 18 then n1640 else n1631
  let n1642 := bif g.getLsbD 9 then n1295 else false
  let n1643 := bif g.getLsbD 10 then false else n1642
  let n1644 := bif g.getLsbD 11 then false else n1643
  let n1645 := bif g.getLsbD 12 then false else n1644
  let n1646 := bif g.getLsbD 13 then false else n1645
  let n1647 := bif g.getLsbD 14 then false else n1646
  let n1648 := bif g.getLsbD 15 then false else n1647
  let n1649 := bif g.getLsbD 16 then false else n1648
  let n1650 := bif g.getLsbD 17 then false else n1649
  let n1651 := bif g.getLsbD 18 then false else n1650
  let n1652 := bif g.getLsbD 19 then n1651 else n1641
  let n1653 := bif g.getLsbD 20 then n1652 else n1628
  let n1654 := bif g.getLsbD 21 then false else n1653
  let n1655 := bif g.getLsbD 22 then false else n1654
  let n1656 := bif g.getLsbD 23 then n1655 else n1622
  let n1657 := bif g.getLsbD 16 then n1157 else false
  let n1658 := bif g.getLsbD 17 then n1261 else n1657
  let n1659 := bif g.getLsbD 15 then n1071 else false
  let n1660 := bif g.getLsbD 16 then n1182 else n1659
  let n1661 := bif g.getLsbD 17 then n1287 else n1660
  let n1662 := bif g.getLsbD 18 then n1661 else n1658
  let n1663 := bif g.getLsbD 19 then n1522 else n1662
  let n1664 := bif g.getLsbD 15 then n1565 else false
  let n1665 := bif g.getLsbD 16 then n1605 else n1664
  let n1666 := bif g.getLsbD 17 then n1639 else n1665
  let n1667 := bif g.getLsbD 18 then false else n1666
  let n1668 := bif g.getLsbD 8 then n1294 else false
  let n1669 := bif g.getLsbD 9 then false else n1668
  let n1670 := bif g.getLsbD 10 then false else n1669
  let n1671 := bif g.getLsbD 11 then false else n1670
  let n1672 := bif g.getLsbD 12 then false else n1671
  let n1673 := bif g.getLsbD 13 then false else n1672
  let n1674 := bif g.getLsbD 14 then false else n1673
  let n1675 := bif g.getLsbD 15 then false else n1674
  let n1676 := bif g.getLsbD 16 then false else n1675
  let n1677 := bif g.getLsbD 17 then false else n1676
  let n1678 := bif g.getLsbD 18 then false else n1677
  let n1679 := bif g.getLsbD 19 then n1678 else n1667
  let n1680 := bif g.getLsbD 20 then n1679 else n1663
  let n1681 := bif g.getLsbD 21 then false else n1680
  let n1682 := bif g.getLsbD 22 then false else n1681
  let n1683 := bif g.getLsbD 23 then false else n1682
  let n1684 := bif g.getLsbD 24 then n1683 else n1656
  let n1685 := bif g.getLsbD 16 then n1418 else false
  let n1686 := bif g.getLsbD 17 then n1469 else n1685
  let n1687 := bif g.getLsbD 18 then n1513 else n1686
  let n1688 := bif g.getLsbD 15 then n1372 else false
  let n1689 := bif g.getLsbD 16 then n1433 else n1688
  let n1690 := bif g.getLsbD 17 then n1485 else n1689
  let n1691 := bif g.getLsbD 18 then n1530 else n1690
  let n1692 := bif g.getLsbD 19 then n1691 else n1687
  let n1693 := bif g.getLsbD 15 then n1575 else false
  let n1694 := bif g.getLsbD 16 then n1615 else n1693
  let n1695 := bif g.getLsbD 17 then n1649 else n1694
  let n1696 := bif g.getLsbD 18 then n1677 else n1695
  let n1697 := bif g.getLsbD 19 then false else n1696
  let n1698 := bif g.getLsbD 20 then n1697 else n1692
  let n1699 := bif g.getLsbD 21 then false else n1698
  let n1700 := bif g.getLsbD 22 then false else n1699
  let n1701 := bif g.getLsbD 23 then false else n1700
  let n1702 := bif g.getLsbD 24 then false else n1701
  let n1703 := bif g.getLsbD 25 then n1702 else n1684
  let n1704 := bif g.getLsbD 26 then n1703 else n1538
  let n1705 := bif g.getLsbD 12 then n674 else false
  let n1706 := bif g.getLsbD 13 then n1051 else n1705
  let n1707 := bif g.getLsbD 14 then n1363 else n1706
  let n1708 := bif g.getLsbD 15 then n1707 else false
  let n1709 := bif g.getLsbD 12 then n452 else false
  let n1710 := bif g.getLsbD 13 then n473 else n1709
  let n1711 := bif g.getLsbD 14 then n494 else n1710
  let n1712 := bif g.getLsbD 15 then false else n1711
  let n1713 := bif g.getLsbD 16 then n1712 else n1708
  let n1714 := bif g.getLsbD 11 then n451 else false
  let n1715 := bif g.getLsbD 12 then n689 else n1714
  let n1716 := bif g.getLsbD 13 then n707 else n1715
  let n1717 := bif g.getLsbD 14 then n728 else n1716
  let n1718 := bif g.getLsbD 15 then false else n1717
  let n1719 := bif g.getLsbD 16 then false else n1718
  let n1720 := bif g.getLsbD 17 then n1719 else n1713
  let n1721 := bif g.getLsbD 11 then n471 else false
  let n1722 := bif g.getLsbD 12 then n706 else n1721
  let n1723 := bif g.getLsbD 13 then n1063 else n1722
  let n1724 := bif g.getLsbD 14 then n1079 else n1723
  let n1725 := bif g.getLsbD 15 then false else n1724
  let n1726 := bif g.getLsbD 16 then false else n1725
  let n1727 := bif g.getLsbD 17 then false else n1726
  let n1728 := bif g.getLsbD 18 then n1727 else n1720
  let n1729 := bif g.getLsbD 11 then n491 else false
  let n1730 := bif g.getLsbD 12 then n726 else n1729
  let n1731 := bif g.getLsbD 13 then n1078 else n1730
  let n1732 := bif g.getLsbD 14 then n1371 else n1731
  let n1733 := bif g.getLsbD 15 then false else n1732
  let n1734 := bif g.getLsbD 16 then false else n1733
  let n1735 := bif g.getLsbD 17 then false else n1734
  let n1736 := bif g.getLsbD 18 then false else n1735
  let n1737 := bif g.getLsbD 19 then n1736 else n1728
  let n1738 := bif g.getLsbD 11 then n1544 else false
  let n1739 := bif g.getLsbD 12 then n1553 else n1738
  let n1740 := bif g.getLsbD 13 then n1563 else n1739
  let n1741 := bif g.getLsbD 14 then n1574 else n1740
  let n1742 := bif g.getLsbD 15 then false else n1741
  let n1743 := bif g.getLsbD 16 then false else n1742
  let n1744 := bif g.getLsbD 17 then false else n1743
  let n1745 := bif g.getLsbD 18 then false else n1744
  let n1746 := bif g.getLsbD 19 then false else n1745
  let n1747 := bif g.getLsbD 20 then n1746 else n1737
  let n1748 := bif g.getLsbD 21 then n1747 else false
  let n1749 := bif g.getLsbD 15 then n1711 else false
  let n1750 := bif g.getLsbD 12 then n903 else false
  let n1751 := bif g.getLsbD 13 then n1160 else n1750
  let n1752 := bif g.getLsbD 14 then n1422 else n1751
  let n1753 := bif g.getLsbD 15 then false else n1752
  let n1754 := bif g.getLsbD 16 then n1753 else n1749
  let n1755 := bif g.getLsbD 11 then n902 else false
  let n1756 := bif g.getLsbD 12 then n919 else n1755
  let n1757 := bif g.getLsbD 13 then n937 else n1756
  let n1758 := bif g.getLsbD 14 then n958 else n1757
  let n1759 := bif g.getLsbD 15 then false else n1758
  let n1760 := bif g.getLsbD 16 then false else n1759
  let n1761 := bif g.getLsbD 17 then n1760 else n1754
  let n1762 := bif g.getLsbD 11 then n1158 else false
  let n1763 := bif g.getLsbD 12 then n936 else n1762
  let n1764 := bif g.getLsbD 13 then n1173 else n1763
  let n1765 := bif g.getLsbD 14 then n1189 else n1764
  let n1766 := bif g.getLsbD 15 then false else n1765
  let n1767 := bif g.getLsbD 16 then false else n1766
  let n1768 := bif g.getLsbD 17 then false else n1767
  let n1769 := bif g.getLsbD 18 then n1768 else n1761
  let n1770 := bif g.getLsbD 11 then n1419 else false
  let n1771 := bif g.getLsbD 12 then n956 else n1770
  let n1772 := bif g.getLsbD 13 then n1188 else n1771
  let n1773 := bif g.getLsbD 14 then n1431 else n1772
  let n1774 := bif g.getLsbD 15 then false else n1773
  let n1775 := bif g.getLsbD 16 then false else n1774
  let n1776 := bif g.getLsbD 17 then false else n1775
  let n1777 := bif g.getLsbD 18 then false else n1776
  let n1778 := bif g.getLsbD 19 then n1777 else n1769
  let n1779 := bif g.getLsbD 10 then n1543 else false
  let n1780 := bif g.getLsbD 11 then false else n1779
  let n1781 := bif g.getLsbD 12 then n1592 else n1780
  let n1782 := bif g.getLsbD 13 then n1602 else n1781
  let n1783 := bif g.getLsbD 14 then n1613 else n1782
  let n1784 := bif g.getLsbD 15 then false else n1783
  let n1785 := bif g.getLsbD 16 then false else n1784
  let n1786 := bif g.getLsbD 17 then false else n1785
  let n1787 := bif g.getLsbD 18 then false else n1786
  let n1788 := bif g.getLsbD 19 then false else n1787
  let n1789 := bif g.getLsbD 20 then n1788 else n1778
  let n1790 := bif g.getLsbD 21 then false else n1789
  let n1791 := bif g.getLsbD 22 then n1790 else n1748
  let n1792 := bif g.getLsbD 15 then n1717 else false
  let n1793 := bif g.getLsbD 16 then n1759 else n1792
  let n1794 := bif g.getLsbD 11 then n918 else false
  let n1795 := bif g.getLsbD 12 then false else n1794
  let n1796 := bif g.getLsbD 13 then n1264 else n1795
  let n1797 := bif g.getLsbD 14 then n1473 else n1796
  let n1798 := bif g.getLsbD 15 then false else n1797
  let n1799 := bif g.getLsbD 16 then false else n1798
  let n1800 := bif g.getLsbD 17 then n1799 else n1793
  let n1801 := bif g.getLsbD 11 then n935 else false
  let n1802 := bif g.getLsbD 12 then n1263 else n1801
  let n1803 := bif g.getLsbD 13 then n1277 else n1802
  let n1804 := bif g.getLsbD 14 then n1293 else n1803
  let n1805 := bif g.getLsbD 15 then false else n1804
  let n1806 := bif g.getLsbD 16 then false else n1805
  let n1807 := bif g.getLsbD 17 then false else n1806
  let n1808 := bif g.getLsbD 18 then n1807 else n1800
  let n1809 := bif g.getLsbD 11 then n955 else false
  let n1810 := bif g.getLsbD 12 then n1471 else n1809
  let n1811 := bif g.getLsbD 13 then n1292 else n1810
  let n1812 := bif g.getLsbD 14 then n1482 else n1811
  let n1813 := bif g.getLsbD 15 then false else n1812
  let n1814 := bif g.getLsbD 16 then false else n1813
  let n1815 := bif g.getLsbD 17 then false else n1814
  let n1816 := bif g.getLsbD 18 then false else n1815
  let n1817 := bif g.getLsbD 19 then n1816 else n1808
  let n1818 := bif g.getLsbD 10 then n1551 else false
  let n1819 := bif g.getLsbD 11 then n1591 else n1818
  let n1820 := bif g.getLsbD 12 then false else n1819
  let n1821 := bif g.getLsbD 13 then n1635 else n1820
  let n1822 := bif g.getLsbD 14 then n1646 else n1821
  let n1823 := bif g.getLsbD 15 then false else n1822
  let n1824 := bif g.getLsbD 16 then false else n1823
  let n1825 := bif g.getLsbD 17 then false else n1824
  let n1826 := bif g.getLsbD 18 then false else n1825
  let n1827 := bif g.getLsbD 19 then false else n1826
  let n1828 := bif g.getLsbD 20 then n1827 else n1817
  let n1829 := bif g.getLsbD 21 then false else n1828
  let n1830 := bif g.getLsbD 22 then false else n1829
  let n1831 := bif g.getLsbD 23 then n1830 else n1791
  let n1832 := bif g.getLsbD 15 then n1724 else false
  let n1833 := bif g.getLsbD 16 then n1766 else n1832
  let n1834 := bif g.getLsbD 17 then n1806 else n1833
  let n1835 := bif g.getLsbD 11 then n1171 else false
  let n1836 := bif g.getLsbD 12 then n1276 else n1835
  let n1837 := bif g.getLsbD 13 then false else n1836
  let n1838 := bif g.getLsbD 14 then n1517 else n1837
  let n1839 := bif g.getLsbD 15 then false else n1838
  let n1840 := bif g.getLsbD 16 then false else n1839
  let n1841 := bif g.getLsbD 17 then false else n1840
  let n1842 := bif g.getLsbD 18 then n1841 else n1834
  let n1843 := bif g.getLsbD 11 then n1186 else false
  let n1844 := bif g.getLsbD 12 then n1291 else n1843
  let n1845 := bif g.getLsbD 13 then n1516 else n1844
  let n1846 := bif g.getLsbD 14 then n1526 else n1845
  let n1847 := bif g.getLsbD 15 then false else n1846
  let n1848 := bif g.getLsbD 16 then false else n1847
  let n1849 := bif g.getLsbD 17 then false else n1848
  let n1850 := bif g.getLsbD 18 then false else n1849
  let n1851 := bif g.getLsbD 19 then n1850 else n1842
  let n1852 := bif g.getLsbD 10 then n1560 else false
  let n1853 := bif g.getLsbD 11 then n1600 else n1852
  let n1854 := bif g.getLsbD 12 then n1634 else n1853
  let n1855 := bif g.getLsbD 13 then false else n1854
  let n1856 := bif g.getLsbD 14 then n1673 else n1855
  let n1857 := bif g.getLsbD 15 then false else n1856
  let n1858 := bif g.getLsbD 16 then false else n1857
  let n1859 := bif g.getLsbD 17 then false else n1858
  let n1860 := bif g.getLsbD 18 then false else n1859
  let n1861 := bif g.getLsbD 19 then false else n1860
  let n1862 := bif g.getLsbD 20 then n1861 else n1851
  let n1863 := bif g.getLsbD 21 then false else n1862
  let n1864 := bif g.getLsbD 22 then false else n1863
  let n1865 := bif g.getLsbD 23 then false else n1864
  let n1866 := bif g.getLsbD 24 then n1865 else n1831
  let n1867 := bif g.getLsbD 15 then n1732 else false
  let n1868 := bif g.getLsbD 16 then n1774 else n1867
  let n1869 := bif g.getLsbD 17 then n1814 else n1868
  let n1870 := bif g.getLsbD 18 then n1849 else n1869
  let n1871 := bif g.getLsbD 11 then n1428 else false
  let n1872 := bif g.getLsbD 12 then n1480 else n1871
  let n1873 := bif g.getLsbD 13 then n1525 else n1872
  let n1874 := bif g.getLsbD 14 then false else n1873
  let n1875 := bif g.getLsbD 15 then false else n1874
  let n1876 := bif g.getLsbD 16 then false else n1875
  let n1877 := bif g.getLsbD 17 then false else n1876
  let n1878 := bif g.getLsbD 18 then false else n1877
  let n1879 := bif g.getLsbD 19 then n1878 else n1870
  let n1880 := bif g.getLsbD 10 then n1570 else false
  let n1881 := bif g.getLsbD 11 then n1610 else n1880
  let n1882 := bif g.getLsbD 12 then n1644 else n1881
  let n1883 := bif g.getLsbD 13 then n1672 else n1882
  let n1884 := bif g.getLsbD 14 then false else n1883
  let n1885 := bif g.getLsbD 15 then false else n1884
  let n1886 := bif g.getLsbD 16 then false else n1885
  let n1887 := bif g.getLsbD 17 then false else n1886
  let n1888 := bif g.getLsbD 18 then false else n1887
  let n1889 := bif g.getLsbD 19 then false else n1888
  let n1890 := bif g.getLsbD 20 then n1889 else n1879
  let n1891 := bif g.getLsbD 21 then false else n1890
  let n1892 := bif g.getLsbD 22 then false else n1891
  let n1893 := bif g.getLsbD 23 then false else n1892
  let n1894 := bif g.getLsbD 24 then false else n1893
  let n1895 := bif g.getLsbD 25 then n1894 else n1866
  let n1896 := bif g.getLsbD 15 then n1741 else false
  let n1897 := bif g.getLsbD 16 then n1784 else n1896
  let n1898 := bif g.getLsbD 17 then n1824 else n1897
  let n1899 := bif g.getLsbD 18 then n1859 else n1898
  let n1900 := bif g.getLsbD 19 then n1888 else n1899
  let n1901 := bif g.getLsbD 20 then false else n1900
  let n1902 := bif g.getLsbD 21 then false else n1901
  let n1903 := bif g.getLsbD 22 then false else n1902
  let n1904 := bif g.getLsbD 23 then false else n1903
  let n1905 := bif g.getLsbD 24 then false else n1904
  let n1906 := bif g.getLsbD 25 then false else n1905
  let n1907 := bif g.getLsbD 26 then n1906 else n1895
  let n1908 := bif g.getLsbD 27 then n1907 else n1704
  n1908

/- Every labelled connected graph of degree sequence `4^5, 2^3` belongs to one of its thirteen
isomorphism classes, represented by all 3,210 distinct degree-preserving labellings. -/
set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
example : ∀ (g : BitVec (edgeCount 8)),
    (connectedUpper (n := 8) g &&
      fixedDegreeSequenceUpper (n := 8) g [4, 4, 4, 4, 4, 2, 2, 2] &&
      !memberDegreeEdgeCodes44444222BDD g) = false := by
  simp (config := { maxSteps := 100000000 }) only
    [edgeCount, connectedUpper, reachableFromZeroUpper,
    fixedDegreeSequenceUpper, matchesDegreesFromUpper, degreeBitsUpper,
    BoolFour.increment, BoolFour.same, BoolFour.ofNat,
    memberDegreeEdgeCodes44444222BDD,
    adjUpper, setBit, bitMask, natBit,
    List.range, List.range.loop, List.foldl, List.length, List.all, List.any]
  bv_decide (maxSteps := 100000000) (timeout := 600)

def candidateHamiltonianOrders44444222 : List (List Nat) := [[5,0,1,2,6,3,4,7],[5,0,1,2,6,4,3,7],[5,0,1,3,6,4,2,7],[5,0,1,6,2,3,4,7],[5,0,1,6,3,2,4,7],[5,0,1,6,4,2,3,7],[5,1,0,6,2,3,4,7],[5,1,0,6,3,2,4,7],[5,1,0,6,4,2,3,7],[5,1,2,4,6,3,0,7],[5,1,3,4,6,2,0,7],[5,1,4,3,6,2,0,7],[5,2,0,6,1,3,4,7],[5,2,3,6,0,4,1,7],[5,2,3,6,1,4,0,7],[5,2,4,6,0,3,1,7],[5,2,4,6,1,3,0,7],[5,3,1,6,0,4,2,7],[5,3,2,6,0,4,1,7],[5,3,2,6,1,4,0,7],[6,2,1,5,4,0,3,7],[5,0,2,7,1,4,3,6],[5,0,3,4,6,1,2,7],[5,0,3,7,1,4,2,6],[5,1,3,4,6,0,2,7],[5,2,3,6,4,1,0,7],[5,2,4,1,6,0,3,7],[5,3,2,0,6,4,1,7],[5,3,2,1,6,4,0,7],[5,3,2,6,4,1,0,7],[5,4,2,1,6,3,0,7],[5,4,2,6,3,1,0,7],[5,4,3,0,6,1,2,7],[5,4,3,6,0,1,2,7],[5,4,3,1,6,2,0,7],[5,0,2,4,7,1,3,6],[5,0,4,2,6,1,3,7],[5,0,4,3,6,1,2,7],[5,0,4,6,2,3,1,7],[5,1,4,2,6,0,3,7],[6,2,4,5,3,0,1,7],[5,2,0,4,6,3,1,7],[5,2,1,3,6,0,4,7],[5,2,0,1,6,3,4,7],[5,2,0,1,6,4,3,7],[5,2,1,0,6,4,3,7],[5,3,0,2,6,1,4,7],[5,3,0,6,4,1,2,7],[5,3,1,6,4,0,2,7],[5,3,2,0,6,1,4,7],[5,4,0,6,1,2,3,7],[6,3,1,5,4,0,2,7],[5,3,0,2,6,4,1,7],[5,3,1,2,6,0,4,7],[5,4,2,6,0,1,3,7],[5,1,4,3,6,0,2,7],[5,1,4,6,3,0,2,7],[5,4,1,6,3,0,2,7],[5,0,4,6,3,2,1,7],[5,1,4,6,2,0,3,7],[6,0,2,5,4,3,1,7],[5,1,2,6,3,0,4,7],[5,2,6,3,0,4,1,7],[5,4,1,6,2,0,3,7],[5,0,1,2,3,4,6,7],[5,0,1,2,4,3,6,7],[5,0,1,3,4,2,6,7],[5,0,2,3,4,1,6,7],[5,0,6,2,1,3,4,7],[5,1,2,3,4,0,6,7],[5,4,3,2,1,7,0,6],[5,6,0,1,2,3,4,7],[5,6,1,0,2,3,4,7],[5,6,2,0,1,3,4,7],[5,6,3,0,1,2,4,7],[5,6,4,0,1,2,3,7],[5,0,1,3,2,7,4,6],[5,1,2,3,0,4,6,7],[5,1,3,4,2,0,7,6],[5,2,3,4,0,1,6,7],[5,3,1,4,2,0,6,7],[5,6,0,2,4,1,3,7],[5,6,1,2,3,4,0,7],[5,6,2,1,3,4,0,7],[5,6,3,1,2,4,0,7],[5,6,4,1,2,3,0,7],[6,2,5,1,3,0,4,7],[6,2,5,4,3,1,0,7],[6,3,5,4,0,1,2,7],[5,0,1,4,2,6,3,7],[5,0,3,2,4,6,1,7],[5,1,3,4,0,7,2,6],[5,1,6,0,3,4,2,7],[5,2,4,1,3,7,0,6],[5,3,0,4,1,2,6,7],[5,3,0,4,2,1,6,7],[5,3,6,4,2,1,0,7],[5,4,0,1,2,3,6,7],[5,6,1,4,2,0,3,7],[5,7,1,2,0,4,3,6],[5,0,2,1,4,6,3,7],[5,0,2,4,1,6,3,7],[5,0,3,4,1,7,2,6],[5,0,6,4,3,2,1,7],[5,1,6,4,3,2,0,7],[5,2,0,3,1,4,6,7],[5,2,3,4,1,0,6,7],[5,3,1,0,2,6,4,7],[5,3,1,2,4,7,0,6],[5,3,6,1,2,4,0,7],[5,6,0,3,1,4,2,7],[5,6,2,4,1,0,3,7],[5,6,3,4,1,0,2,7],[5,6,4,2,0,3,1,7],[6,0,2,3,1,4,5,7],[6,0,5,4,1,2,3,7],[5,1,3,0,4,2,6,7],[5,1,4,2,0,3,6,7],[5,2,1,6,0,3,4,7],[5,3,0,1,6,2,4,7],[5,3,6,0,2,4,1,7],[5,6,0,4,3,2,1,7],[6,2,3,1,0,4,5,7],[5,1,2,4,0,6,3,7],[5,1,4,0,7,2,3,6],[5,1,4,6,0,2,3,7],[5,2,0,4,6,1,3,7],[5,3,6,2,1,4,0,7],[5,7,2,0,1,3,4,6],[6,1,5,4,2,0,3,7],[6,2,3,1,4,0,5,7],[6,4,2,1,0,3,5,7],[5,0,6,1,4,3,2,7],[5,2,0,4,3,1,7,6],[5,2,1,0,6,3,4,7],[5,2,3,0,4,6,1,7],[5,2,6,4,0,1,3,7],[5,4,0,3,1,7,2,6],[5,6,1,3,0,4,2,7],[6,0,1,2,4,3,5,7],[6,0,4,1,3,2,5,7],[6,1,5,0,2,3,4,7],[6,2,4,0,3,1,5,7],[6,5,0,1,4,2,3,7],[5,0,1,7,4,3,2,6],[5,0,2,3,1,4,7,6],[5,1,2,0,3,6,4,7],[5,2,0,3,6,1,4,7],[5,2,6,1,0,4,3,7],[5,3,0,1,4,2,7,6],[5,3,2,4,0,6,1,7],[5,3,4,6,1,0,2,7],[5,4,2,1,7,0,3,6],[5,6,4,0,3,1,2,7],[5,7,3,0,4,2,1,6],[6,4,3,5,2,1,0,7],[6,5,3,2,0,4,1,7],[5,0,1,4,3,7,2,6],[5,0,6,3,1,4,2,7],[5,1,2,3,0,6,4,7],[5,2,0,3,6,4,1,7],[5,2,1,4,0,3,6,7],[5,3,0,6,2,4,1,7],[5,4,0,2,3,1,6,7],[5,4,0,2,3,6,1,7],[5,4,1,3,2,6,0,7],[5,4,6,0,1,3,2,7],[5,7,0,2,1,3,4,6],[6,5,4,0,1,2,3,7],[5,1,2,0,7,4,3,6],[5,2,1,4,7,3,0,6],[5,3,1,6,2,4,0,7],[5,3,2,4,6,1,0,7],[5,3,4,1,2,0,7,6],[5,4,1,0,3,2,7,6],[5,4,3,2,7,0,1,6],[5,4,7,1,0,3,2,6],[5,7,2,1,4,0,3,6],[5,7,4,0,2,1,3,6],[6,2,1,3,4,5,0,7],[6,4,1,5,0,3,2,7],[6,5,2,3,4,0,1,7],[5,0,2,6,1,3,4,7],[5,0,4,3,7,1,2,6],[5,1,0,2,4,6,3,7],[5,1,4,0,6,2,3,7],[5,1,4,7,2,0,3,6],[5,2,1,4,0,3,7,6],[5,3,1,0,6,4,2,7],[5,4,0,2,3,1,7,6],[5,4,7,1,3,2,0,6],[5,7,4,3,0,2,1,6],[6,2,4,0,3,5,1,7],[6,5,0,2,1,3,4,7],[6,5,1,4,3,2,0,7],[5,0,1,3,2,6,4,7],[5,1,2,0,3,4,7,6],[5,1,6,2,4,0,3,7],[5,1,6,3,4,0,2,7],[5,2,3,7,1,4,0,6],[5,2,4,0,3,6,1,7],[5,2,4,1,3,0,7,6],[5,3,4,1,0,6,2,7],[5,4,0,6,1,3,2,7],[5,4,2,1,0,3,7,6],[5,4,6,1,2,0,3,7],[5,4,6,3,1,2,0,7],[5,6,2,4,3,0,1,7],[5,6,4,3,1,2,0,7],[5,7,0,4,2,1,3,6],[6,3,0,1,2,5,4,7],[6,3,2,4,1,0,5,7],[6,4,5,3,1,2,0,7],[1,3,6,2,7,4,0,5],[1,3,6,5,4,0,2,7],[5,0,1,3,4,2,7,6],[5,0,3,2,4,1,7,6],[5,0,3,6,1,2,4,7],[5,0,6,3,4,2,1,7],[5,0,7,1,4,3,2,6],[5,1,2,4,0,3,7,6],[5,1,3,2,6,4,0,7],[5,1,7,2,0,4,3,6],[5,2,3,0,1,4,7,6],[5,2,4,3,6,1,0,7],[5,3,2,4,1,6,0,7],[5,4,0,1,3,7,2,6],[5,4,2,1,7,3,0,6],[5,6,1,3,2,4,0,7],[5,6,2,3,0,1,4,7],[5,7,0,1,4,3,2,6],[5,7,1,2,4,3,0,6],[5,7,1,4,3,0,2,6],[5,7,3,1,2,4,0,6],[6,5,1,4,0,3,2,7],[3,4,1,5,2,7,0,6],[5,0,2,3,1,6,4,7],[5,1,0,4,2,6,3,7],[5,1,6,3,4,2,0,7],[5,2,3,0,1,6,4,7],[5,2,3,1,0,6,4,7],[5,3,4,0,1,6,2,7],[5,3,4,1,6,0,2,7],[5,3,6,0,1,4,2,7],[5,4,0,1,2,7,3,6],[5,4,1,0,7,3,2,6],[5,4,3,2,1,0,6,7],[6,2,3,5,1,0,4,7],[6,3,0,1,2,4,5,7],[6,4,0,5,3,1,2,7],[6,5,2,0,1,3,4,7],[0,1,3,6,4,7,2,5],[0,2,4,6,1,5,3,7],[0,3,4,7,5,1,2,6],[0,3,6,5,2,4,1,7],[0,6,4,2,3,5,1,7],[0,6,4,3,1,2,7,5],[1,3,6,2,0,5,4,7],[1,5,2,3,7,0,4,6],[1,5,4,2,3,6,0,7],[1,6,2,3,4,7,0,5],[1,6,7,4,3,2,0,5],[2,4,7,1,0,5,3,6],[2,4,7,3,1,6,0,5],[5,0,1,2,7,3,4,6],[5,0,4,1,2,3,7,6],[5,0,6,4,1,2,3,7],[5,1,3,4,2,6,0,7],[5,1,6,0,2,3,4,7],[5,2,4,3,7,1,0,6],[5,4,1,2,3,0,7,6],[6,1,3,4,0,2,5,7],[6,2,3,0,4,5,1,7],[0,1,2,3,5,6,7,4],[0,1,2,4,6,3,7,5],[0,1,2,4,7,5,3,6],[0,1,2,5,3,4,6,7],[0,1,2,7,6,4,3,5],[0,1,6,3,5,4,2,7],[0,1,7,2,4,3,6,5],[0,2,1,7,3,5,4,6],[0,2,3,5,4,7,1,6],[0,2,3,7,5,4,1,6],[0,3,1,5,4,7,2,6],[0,4,2,6,1,7,3,5],[0,4,7,2,1,5,3,6],[0,5,1,7,4,3,2,6],[0,5,3,1,4,6,2,7],[0,6,4,1,3,2,5,7],[0,6,5,3,1,4,2,7],[0,7,1,4,2,5,3,6]]

def hasCandidateHamiltonianOrderUpper {n : Nat} (g : BitVec (edgeCount n))
    (orders : List (List Nat)) : Bool :=
  orders.any fun order => validHamiltonianOrderUpper g order

/- A constructive certificate for the same class: one of 291 explicit vertex orders is a
Hamiltonian path in every connected labelled realization. -/
set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
example : ∀ (g : BitVec (edgeCount 8)),
    (connectedUpper (n := 8) g &&
      fixedDegreeSequenceUpper (n := 8) g [4, 4, 4, 4, 4, 2, 2, 2] &&
      !hasCandidateHamiltonianOrderUpper g candidateHamiltonianOrders44444222) = false := by
  simp (config := { maxSteps := 100000000 }) only
    [edgeCount, connectedUpper, reachableFromZeroUpper,
    fixedDegreeSequenceUpper, matchesDegreesFromUpper, degreeBitsUpper,
    BoolFour.increment, BoolFour.same, BoolFour.ofNat,
    hasCandidateHamiltonianOrderUpper, candidateHamiltonianOrders44444222,
    validHamiltonianOrderUpper, consecutiveAdjacentUpper,
    adjUpper, setBit, bitMask, natBit,
    List.range, List.range.loop, List.foldl, List.length,
    List.nodup_cons, List.all, List.any]
  bv_decide (maxSteps := 100000000) (timeout := 600)

end WOWII217Cert
