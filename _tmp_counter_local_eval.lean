import WOWII217Closure
import WOWII217FiniteBase
import WOWII217Finite13

open SimpleGraph
open WOWII217FiniteBase WOWII217Closure WOWII217Finite13

-- explicit graph on Fin 13 as in Counter13

def highComp (u : Fin 13) : Bool :=
  u.1 = 0 || u.1 = 1 || u.1 = 2 || u.1 = 3 || u.1 = 4 || u.1 = 5 || u.1 = 7

def lowComp (u : Fin 13) : Bool :=
  u.1 = 6 || u.1 = 8 || u.1 = 9 || u.1 = 10 || u.1 = 11 || u.1 = 12

axiom comp_eq : highComp = lowComp -> False

def G : SimpleGraph (Fin 13) where
  Adj u v :=
    if h : u = v then false else
      (highComp u && highComp v) || (lowComp u && lowComp v)

instance : DecidableRel G.Adj := fun u v => inferInstance
instance : DecidableEq (Fin 13) := inferInstance

-- local encodeUpper13 to avoid importing WOWII217Encoding13

def encodeUpper13_local (H : SimpleGraph (Fin 13)) [DecidableRel H.Adj] : BitVec 78 := by
  let bits := List.ofFn fun i : Fin 78 =>
    let e := (upperPairs 13).getD i (0, 0)
    let u : Fin 13 := Fin.ofNatEq (e.1) (by omega)
    let v : Fin 13 := Fin.ofNatEq (e.2) (by omega)
    decide (H.Adj u v)
  exact BitVec.cast (by simp) (BitVec.ofBoolListLE bits)

-- check a couple of values
example : fixedDegreeSequenceUpper (n := 13) (encodeUpper13_local G)
    [6, 6, 6, 6, 6, 6, 6, 5, 5, 5, 5, 5, 5] = true := by
  native_decide

#eval (connectedUpper (n := 13) (encodeUpper13_local G))

#eval (List.range 13).foldl (fun a i => a ++ [degreeUpperNat (n := 13) (encodeUpper13_local G) i]) ([] : List Nat)
