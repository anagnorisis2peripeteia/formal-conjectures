import WOWII217Finite13
import WOWII217FiniteBase
import WOWII217Encoding13
import WOWII217Closure

open WOWII217FiniteBase WOWII217Finite13 WOWII217Encoding13 WOWII217Closure

def local_hasHighLowEdge13 (g : BitVec 78) : Bool :=
  (List.range 7).any fun u =>
    (List.range 6).any fun offset => adjUpper (n := 13) g u (offset + 7)

def local_degreeTableAt13 (degrees : BitVec 52) (v : Nat) : BoolFour :=
  { b0 := degrees.getLsbD (4 * v),
    b1 := degrees.getLsbD (4 * v + 1),
    b2 := degrees.getLsbD (4 * v + 2),
    b3 := degrees.getLsbD (4 * v + 3) }

def local_degreeTableConsistent13 (g : BitVec 78) (degrees : BitVec 52) : Bool :=
  (List.range 13).all fun v =>
    (degreeBitsUpper (n := 13) g v).same (local_degreeTableAt13 degrees v)

def local_majority (a b c : Bool) : Bool := (a && b) || (a && c) || (b && c)
def local_boolFourSumAtLeast12 (x y : BoolFour) : Bool :=
  let c1 := x.b0 && y.b0
  let c2 := local_majority x.b1 y.b1 c1
  let s2 := x.b2 ^^ y.b2 ^^ c2
  let c3 := local_majority x.b2 y.b2 c2
  let s3 := x.b3 ^^ y.b3 ^^ c3
  let c4 := local_majority x.b3 y.b3 c3
  c4 || (s3 && s2)

def local_pathClosureParallelRel13 (g next : BitVec 78) (degrees : BitVec 52) : Bool :=
  (upperPairs 13).all fun edge =>
    let u := edge.1
    let v := edge.2
    !(adjUpper (n := 13) next u v ^^
      (adjUpper (n := 13) g u v ||
        local_boolFourSumAtLeast12 (local_degreeTableAt13 degrees u)
          (local_degreeTableAt13 degrees v)))

def k7k6Adj (u v : Fin 13) : Prop :=
  (u.1 = 0 || u.1 = 1 || u.1 = 2 || u.1 = 3 || u.1 = 4 || u.1 = 5 || u.1 = 7) ∧
  (v.1 = 0 || v.1 = 1 || v.1 = 2 || v.1 = 3 || v.1 = 4 || v.1 = 5 || v.1 = 7) ∨
  (u.1 = 6 || u.1 = 8 || u.1 = 9 || u.1 = 10 || u.1 = 11 || u.1 = 12) ∧
  (v.1 = 6 || v.1 = 8 || v.1 = 9 || v.1 = 10 || v.1 = 11 || v.1 = 12)

instance : DecidableRel k7k6Adj := Classical.decRel _

def G : SimpleGraph (Fin 13) where
  Adj u v :=
    if h : u = v then False else
      ((u.1 = 0 || u.1 = 1 || u.1 = 2 || u.1 = 3 || u.1 = 4 || u.1 = 5 || u.1 = 7) ∧
       (v.1 = 0 || v.1 = 1 || v.1 = 2 || v.1 = 3 || v.1 = 4 || v.1 = 5 || v.1 = 7)) ∨
      ((u.1 = 6 || u.1 = 8 || u.1 = 9 || u.1 = 10 || u.1 = 11 || u.1 = 12) ∧
       (v.1 = 6 || v.1 = 8 || v.1 = 9 || v.1 = 10 || v.1 = 11 || v.1 = 12)

def g : BitVec 78 := encodeUpper13 G

example : fixedDegreeSequenceUpper (n := 13) g
    [6, 6, 6, 6, 6, 6, 6, 5, 5, 5, 5, 5, 5] = true := by
  native_decide

example : local_hasHighLowEdge13 g = true := by
  native_decide

example : connectedUpper (n := 13) g = false := by
  native_decide

example : local_degreeTableConsistent13 g (degreeTableOfUpper13 g) = true := by
  native_decide

example : local_pathClosureParallelRel13 g g (degreeTableOfUpper13 g) = true := by
  native_decide

example :
    ¬ (∀ (d : BitVec 52),
      fixedDegreeSequenceUpper (n := 13) g
          [6, 6, 6, 6, 6, 6, 6, 5, 5, 5, 5, 5, 5] = true →
      local_degreeTableConsistent13 g d = true →
      local_pathClosureParallelRel13 g g d = true →
      completeUpper (n := 13) g = true) := by
  intro h
  have h01 : local_degreeTableConsistent13 g (degreeTableOfUpper13 g) = true := by native_decide
  have h02 : local_pathClosureParallelRel13 g g (degreeTableOfUpper13 g) = true := by
    native_decide
  have h03 : completeUpper (n := 13) g = true :=
    h (degreeTableOfUpper13 g) (by native_decide) h01 h02
  have hfalse : completeUpper (n := 13) g = false := by native_decide
  simpa [h03] using hfalse
