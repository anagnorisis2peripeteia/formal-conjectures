import WOWII217Encoding13
import WOWII217FiniteBase
import WOWII217Finite13
import WOWII217Closure13Fast
import WOWII217Relabel

open WOWII217FiniteBase WOWII217Finite13 WOWII217Encoding13

/-- Graph copied from Counter13. -/
def isHighComp (u : Fin 13) : Bool :=
  if u.1 = 0 || u.1 = 1 || u.1 = 2 || u.1 = 3 || u.1 = 4 || u.1 = 5 || u.1 = 7 then true else false

def isLowComp (u : Fin 13) : Bool :=
  if u.1 = 6 || u.1 = 8 || u.1 = 9 || u.1 = 10 || u.1 = 11 || u.1 = 12 then true else false

def gCounter : SimpleGraph (Fin 13) where
  Adj u v :=
    if h : u = v then False else
      ((isHighComp u = true) && (isHighComp v = true)) || ((isLowComp u = true) && (isLowComp v = true))

instance : DecidableRel gCounter.Adj := by
  classical infer_instance

instance : DecidableEq (Fin 13) := inferInstance

open WOWII217Closure13Fast

def gBits : BitVec 78 := encodeUpper13 gCounter

def hasHighLowEdge13_local (g : BitVec 78) : Bool :=
  (List.range 7).any fun u =>
    (List.range 6).any fun offset => adjUpper (n := 13) g u (offset + 7)

#eval (fixedDegreeSequenceUpper (n := 13) gBits [6, 6, 6, 6, 6, 6, 6, 5, 5, 5, 5, 5, 5])
#eval hasHighLowEdge13_local gBits
#eval (connectedUpper (n := 13) gBits)
#eval (List.range 13).map (fun i => degreeUpperNat (n:=13) gBits i)
