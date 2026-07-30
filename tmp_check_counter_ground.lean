import WOWII217Finite13
import WOWII217Encoding13
import WOWII217FiniteBase

open WOWII217FiniteBase WOWII217Encoding13

instance : DecidableEq (Fin 13) := inferInstance
open scoped Finset

def k7k6Adj (u v : Fin 13) : Prop :=
  (u.1 = 0 || u.1 = 1 || u.1 = 2 || u.1 = 3 || u.1 = 4 || u.1 = 5 || u.1 = 7) ∧
  (v.1 = 0 || v.1 = 1 || v.1 = 2 || v.1 = 3 || v.1 = 4 || v.1 = 5 || v.1 = 7) ∨
  (u.1 = 6 || u.1 = 8 || u.1 = 9 || u.1 = 10 || u.1 = 11 || u.1 = 12) ∧
  (v.1 = 6 || v.1 = 8 || v.1 = 9 || v.1 = 10 || v.1 = 11 || v.1 = 12)

instance : DecidableRel k7k6Adj := Classical.decRel _

def G : SimpleGraph (Fin 13) where
  Adj u v :=
    if h : u = v then False else
      ((u.1 = 0 || u.1 = 1 || u.1 = 2 || u.1 = 3 || u.1 = 4 || u.1 = 5 || u.1 = 7) &&
       (v.1 = 0 || v.1 = 1 || v.1 = 2 || v.1 = 3 || v.1 = 4 || v.1 = 5 || v.1 = 7)) ||
      ((u.1 = 6 || u.1 = 8 || u.1 = 9 || u.1 = 10 || u.1 = 11 || u.1 = 12) &&
       (v.1 = 6 || v.1 = 8 || v.1 = 9 || v.1 = 10 || v.1 = 11 || v.1 = 12))

def g : BitVec 78 := encodeUpper13 G

def hasHighLowEdge13 (g : BitVec 78) : Bool :=
  (List.range 7).any fun u =>
    (List.range 6).any fun offset => adjUpper (n := 13) g u (offset + 7)

#eval (fixedDegreeSequenceUpper (n := 13) g [6, 6, 6, 6, 6, 6, 6, 5, 5, 5, 5, 5, 5])
#eval (hasHighLowEdge13 g)
#eval (connectedUpper (n := 13) g)
#eval (degreesFromUpper (n := 13) g 0)
