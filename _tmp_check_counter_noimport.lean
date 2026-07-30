import WOWII217Closure
import WOWII217FiniteBase
import WOWII217Finite13

open WOWII217FiniteBase WOWII217Closure WOWII217Finite13

open SimpleGraph


def isHighComp (u : Fin 13) : Bool :=
  u.1 = 0 || u.1 = 1 || u.1 = 2 || u.1 = 3 || u.1 = 4 || u.1 = 5 || u.1 = 7

def isLowComp (u : Fin 13) : Bool :=
  u.1 = 6 || u.1 = 8 || u.1 = 9 || u.1 = 10 || u.1 = 11 || u.1 = 12

def G : SimpleGraph (Fin 13) where
  Adj u v :=
    if h : u = v then False else
      (isHighComp u && isHighComp v) || (isLowComp u && isLowComp v)

instance : DecidableRel G.Adj := by
  classical infer_instance

instance : DecidableEq (Fin 13) := inferInstance


def encodeUpper13_local (G : SimpleGraph (Fin 13)) [DecidableRel G.Adj] : BitVec 78 := by
  let bits := List.ofFn fun i : Fin 78 =>
    let edge := (upperPairs 13).getD i (0, 0)
    decide (G.Adj ⟨edge.1, by omega⟩ ⟨edge.2, by omega⟩)
  exact BitVec.cast (by simp) (BitVec.ofBoolListLE bits)


def g : BitVec 78 := encodeUpper13_local G

def hasHighLowEdge13_local (g : BitVec 78) : Bool :=
  (List.range 7).any fun u =>
    (List.range 6).any fun offset => adjUpper (n := 13) g u (offset + 7)

#eval fixedDegreeSequenceUpper (n := 13) g [6,6,6,6,6,6,6,5,5,5,5,5,5]
#eval hasHighLowEdge13_local g
#eval connectedUpper (n := 13) g
#eval (List.range 13).map (fun i => degreeUpperNat (n := 13) g i)
