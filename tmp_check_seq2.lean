import WOWII217FiniteBase
import WOWII217Closure

open WOWII217FiniteBase WOWII217Closure

namespace Scratch

def inHigh (v : Nat) : Bool :=
  decide (v = 0) || decide (v = 1) || decide (v = 2) || decide (v = 3) ||
  decide (v = 4) || decide (v = 5) || decide (v = 7)

def inLow (v : Nat) : Bool :=
  decide (v = 6) || decide (v = 8) || decide (v = 9) || decide (v = 10) ||
  decide (v = 11) || decide (v = 12)

def gCounter : BitVec 78 := by
  let h : BitVec 78 := 0#78
  let h' := (List.range 13).foldl (fun acc u =>
    (List.range 13).foldl (fun acc' v =>
      if hUV : u < v then
        if (inHigh u && inHigh v) || (inLow u && inLow v) then
          setBit acc' (upperIndex u v) true
        else
          acc'
      else
        acc') acc) h
  exact h'

#eval fixedDegreeSequenceUpper (n := 13) gCounter [6,6,6,6,6,6,6,5,5,5,5,5,5]

end Scratch
