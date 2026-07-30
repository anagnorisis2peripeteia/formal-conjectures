import WOWII217Closure13Fast
import WOWII217Finite13

/-!
Shared degree-table encoding of one relational path-closure step on order 13.

Heavy completeness certificates live in
`WOWII217Finite13ClosureSharedDegCert` so semantic bridges can import this
module without waiting on the four-round `bv_decide` chain.
-/

namespace WOWII217Finite13ClosureSharedDeg

open WOWII217FiniteBase WOWII217Closure WOWII217Closure13Fast WOWII217Finite13

def degreeTableAt13 (degrees : BitVec 52) (v : Nat) : BoolFour :=
  { b0 := degrees.getLsbD (4 * v),
    b1 := degrees.getLsbD (4 * v + 1),
    b2 := degrees.getLsbD (4 * v + 2),
    b3 := degrees.getLsbD (4 * v + 3) }

def degreeTableConsistent13 (g : BitVec 78) (degrees : BitVec 52) : Bool :=
  (List.range 13).all fun v =>
    (degreeBitsUpper (n := 13) g v).same (degreeTableAt13 degrees v)

def majority (a b c : Bool) : Bool :=
  (a && b) || (a && c) || (b && c)

/-- Unsigned sum of two four-bit numbers is at least binary `01100`. -/
def boolFourSumAtLeast12 (x y : BoolFour) : Bool :=
  let c1 := x.b0 && y.b0
  let c2 := majority x.b1 y.b1 c1
  let s2 := x.b2 ^^ y.b2 ^^ c2
  let c3 := majority x.b2 y.b2 c2
  let s3 := x.b3 ^^ y.b3 ^^ c3
  let c4 := majority x.b3 y.b3 c3
  c4 || (s3 && s2)

def boolFourValue (x : BoolFour) : Nat :=
  (if x.b0 then 1 else 0) +
    2 * (if x.b1 then 1 else 0) +
    4 * (if x.b2 then 1 else 0) +
    8 * (if x.b3 then 1 else 0)

def hasHighLowEdge13 (g : BitVec 78) : Bool :=
  (List.range 7).any fun u =>
    (List.range 6).any fun offset => adjUpper (n := 13) g u (offset + 7)

def pathClosureParallelRel13 (g next : BitVec 78) (degrees : BitVec 52) : Bool :=
  (upperPairs 13).all fun edge =>
    let u := edge.1
    let v := edge.2
    !(adjUpper (n := 13) next u v ^^
      (adjUpper (n := 13) g u v ||
        boolFourSumAtLeast12 (degreeTableAt13 degrees u)
          (degreeTableAt13 degrees v)))

theorem boolFourSumAtLeast12_iff (x y : BoolFour) :
    boolFourSumAtLeast12 x y = true ↔
      12 ≤ boolFourValue x + boolFourValue y := by
  rcases x with ⟨x0, x1, x2, x3⟩
  rcases y with ⟨y0, y1, y2, y3⟩
  fin_cases x0 <;> fin_cases x1 <;> fin_cases x2 <;> fin_cases x3 <;>
    fin_cases y0 <;> fin_cases y1 <;> fin_cases y2 <;> fin_cases y3 <;>
    decide

theorem boolFour_same_eq_true_iff (x y : BoolFour) :
    x.same y = true ↔ x = y := by
  rcases x with ⟨x0, x1, x2, x3⟩
  rcases y with ⟨y0, y1, y2, y3⟩
  fin_cases x0 <;> fin_cases x1 <;> fin_cases x2 <;> fin_cases x3 <;>
    fin_cases y0 <;> fin_cases y1 <;> fin_cases y2 <;> fin_cases y3 <;>
    simp [BoolFour.same]

theorem degreeTableAt13_eq_of_consistent (g : BitVec 78) (degrees : BitVec 52)
    (consistent : degreeTableConsistent13 g degrees = true) (v : Nat) (hv : v < 13) :
    degreeTableAt13 degrees v = degreeBitsUpper (n := 13) g v := by
  have hAll :
      ∀ w ∈ List.range 13,
        (degreeBitsUpper (n := 13) g w).same (degreeTableAt13 degrees w) = true := by
    exact (List.all_eq_true.mp consistent)
  have hEq :=
    (boolFour_same_eq_true_iff
      (degreeBitsUpper (n := 13) g v) (degreeTableAt13 degrees v)).1
      (hAll v (List.mem_range.mpr hv))
  exact hEq.symm

end WOWII217Finite13ClosureSharedDeg
