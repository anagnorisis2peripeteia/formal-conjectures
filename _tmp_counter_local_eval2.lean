import WOWII217Closure
import WOWII217FiniteBase
import WOWII217Finite13

open WOWII217FiniteBase
open WOWII217Closure

/-- Adjacency predicate used in Counter13-style graph. -/
def highComp (u : Nat) : Bool :=
  u = 0 || u = 1 || u = 2 || u = 3 || u = 4 || u = 5 || u = 7

def lowComp (u : Nat) : Bool :=
  u = 6 || u = 8 || u = 9 || u = 10 || u = 11 || u = 12

def adjCounter (u v : Nat) : Bool :=
  if h : u < 13 ∧ v < 13 ∧ u ≠ v then
    (highComp u && highComp v) || (lowComp u && lowComp v)
  else false

@[simp] theorem adjCounter_eq (u v : Fin 13) :
    adjCounter u.1 v.1 =
      (if hu : u.1 < v.1 then
          ((highComp u.1 && highComp v.1) || (lowComp u.1 && lowComp v.1))
        else false) := by
  simp [adjCounter, hu]

/-- Raw bit-vector encoding from upper triangle of this counterexample pattern. -/
def gCounterBits : BitVec 78 := by
  let acc0 : BitVec 78 := BitVec.zero 78
  let bits := (List.range 78).foldl
    (fun acc i =>
      let e := (upperPairs 13).getD i (0, 0)
      let b : Bool := adjCounter e.1 e.2
      if b then setBit acc i true else acc)
    acc0
  exact bits

#eval (degreeUpperNat (n := 13) gCounterBits 0)
#eval (List.range 13).foldl (fun a i => a ++ [degreeUpperNat (n := 13) gCounterBits i]) ([] : List Nat)
#eval fixedDegreeSequenceUpper (n := 13) gCounterBits [6,6,6,6,6,6,6,5,5,5,5,5,5]
#eval (connectedUpper (n := 13) gCounterBits)
#eval ((List.range 7).any fun u => (List.range 6).any fun offset => adjUpper (n := 13) gCounterBits u (offset + 7))
