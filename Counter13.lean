import WOWII217Finite13ClosureSharedDeg
import WOWII217ClosureCertificateSemantics

open WOWII217FiniteBase WOWII217Closure WOWII217ClosureSemantics WOWII217Encoding13 WOWII217Finite13ClosureSharedDeg WOWII217Finite13

instance : DecidableEq (Fin 13) := inferInstance

open scoped Finset

def k7k6Adj (u v : Fin 13) : Prop :=
  (u.1 = 0 ∨ u.1 = 1 ∨ u.1 = 2 ∨ u.1 = 3 ∨ u.1 = 4 ∨ u.1 = 5 ∨ u.1 = 7) ∧
  (v.1 = 0 ∨ v.1 = 1 ∨ v.1 = 2 ∨ v.1 = 3 ∨ v.1 = 4 ∨ v.1 = 5 ∨ v.1 = 7) ∨
  (u.1 = 6 ∨ u.1 = 8 ∨ u.1 = 9 ∨ u.1 = 10 ∨ u.1 = 11 ∨ u.1 = 12) ∧
  (v.1 = 6 ∨ v.1 = 8 ∨ v.1 = 9 ∨ v.1 = 10 ∨ v.1 = 11 ∨ v.1 = 12)

instance : DecidableRel k7k6Adj := Classical.decRel _

-- define disjoint union of cliques on A={0,1,2,3,4,5,7}, B={6,8,9,10,11,12}
def isHighComp : Fin 13 → Bool := fun v =>
  if v.1 = 0 || v.1 = 1 || v.1 = 2 || v.1 = 3 || v.1 = 4 || v.1 = 5 || v.1 = 7 then true else false

def isLowComp : Fin 13 → Bool := fun v =>
  if v.1 = 6 || v.1 = 8 || v.1 = 9 || v.1 = 10 || v.1 = 11 || v.1 = 12 then true else false

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

example : connectedUpper (n := 13) g = false := by
  native_decide

example : connectedUpper (n := 13) (pathClosureParallelRound13 g) = false := by
  native_decide

