import WOWII217Finite13ClosureFast
import WOWII217Finite13
import WOWII217ClosureCertificateSemantics
import WOWII217ClosureSemantics
import WOWII217Encoding13
import WOWII217FiniteBase
import WOWII217Finite13

open WOWII217FiniteBase WOWII217Closure WOWII217Closure13Fast WOWII217ClosureSemantics WOWII217Finite13 WOWII217Encoding13

namespace Tmp

def hasHighLowEdge13 (g : BitVec 78) : Bool :=
  (List.range 7).any fun u =>
    (List.range 6).any fun offset => adjUpper (n := 13) g u (offset + 7)

def degreeTableAt13 (degrees : BitVec 52) (v : Nat) : BoolFour :=
  { b0 := degrees.getLsbD (4 * v),
    b1 := degrees.getLsbD (4 * v + 1),
    b2 := degrees.getLsbD (4 * v + 2),
    b3 := degrees.getLsbD (4 * v + 3) }

def majority (a b c : Bool) : Bool := (a && b) || (a && c) || (b && c)
def boolFourSumAtLeast12 (x y : BoolFour) : Bool :=
  let c1 := x.b0 && y.b0
  let c2 := majority x.b1 y.b1 c1
  let s2 := x.b2 ^^ y.b2 ^^ c2
  let c3 := majority x.b2 y.b2 c2
  let s3 := x.b3 ^^ y.b3 ^^ c3
  let c4 := majority x.b3 y.b3 c3
  c4 || (s3 && s2)

def degreeTableConsistent13 (g : BitVec 78) (degrees : BitVec 52) : Bool :=
  (List.range 13).all fun v =>
    (degreeBitsUpper (n := 13) g v).same (degreeTableAt13 degrees v)

def pathClosureParallelRel13 (g next : BitVec 78) (degrees : BitVec 52) : Bool :=
  (upperPairs 13).all fun edge =>
    let u := edge.1
    let v := edge.2
    !(adjUpper (n := 13) next u v ^^
      (adjUpper (n := 13) g u v ||
        boolFourSumAtLeast12 (degreeTableAt13 degrees u)
          (degreeTableAt13 degrees v)))

inductive S : Fin 13 → Fin 13 → Prop

instance : DecidableEq (Fin 13) := inferInstance
open scoped Finset

-- same counterexample graph as in Counter13

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

example : hasHighLowEdge13 g = true := by
  native_decide

example : degreeTableConsistent13 g (degreeTableOfUpper13 g) = true := by
  native_decide

example : pathClosureParallelRel13 g g (degreeTableOfUpper13 g) = true := by
  native_decide

example : pathClosureParallelRel13 g g (degreeTableOfUpper13 g) = true := by
  native_decide

example : completeUpper (n := 13) g = false := by
  native_decide

example : ∀ g4 : BitVec 78,
  pathClosureParallelRel13 g g4 (degreeTableOfUpper13 g) = true := by
  intro g4
  -- this one intentionally false for general g4
  sorry

example :
    hasHighLowEdge13 g = true ∧
    fixedDegreeSequenceUpper (n := 13) g
      [6, 6, 6, 6, 6, 6, 6, 5, 5, 5, 5, 5, 5] = true ∧
    degreeTableConsistent13 g (degreeTableOfUpper13 g) = true ∧
    pathClosureParallelRel13 g g (degreeTableOfUpper13 g) = true ∧
    completeUpper (n := 13) g = false := by
  constructor
  · native_decide
  · constructor
    · native_decide
    · constructor
      · native_decide
      · constructor
        · native_decide
        · native_decide

#check pathClosureParallelRel13

end Tmp
