import WOWII217ResidueBound
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Residue
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

open SimpleGraph List
open WOWII217ResidueBound

def stuckResidueTwoImpliesRegularList (n : ℕ) (s : List ℕ) : Bool :=
  let maxD := s.headD 0
  let minD := s.getLastD 0
  if s.length == n && 
     2 * maxD < n - 1 && 
     minD ≥ 1 && 
     residueAux s == 2 && 
     s.sum % 2 == 0 then
    (n == 4 && maxD == 1 && minD == 1) ||
    (n == 6 && maxD == 2 && minD == 2) ||
    (n == 8 && maxD == 3 && minD == 3) ||
    (n == 10 && maxD == 4 && minD == 4) ||
    (n == 12 && maxD == 5 && minD == 5)
  else true

def checkStuckResidueTwoSmallN : Bool :=
  (List.range 13).all fun n =>
    if n == 0 then true else
      forallNoninc n ((n - 2) / 2) [] (stuckResidueTwoImpliesRegularList n)

theorem checkStuckResidueTwoSmallN_eq_true : checkStuckResidueTwoSmallN = true := by
  native_decide
