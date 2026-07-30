import WOWII217ClosureSemantics
import WOWII217Closure
import WOWII217DP

#check boolFourValue_ofNat_of_lt_sixteen
#check boolFourValue_injective
#check boolFourSame_eq_true_iff
#check boolFourValue

example : boolFourValue (BoolFour.ofNat 6) = 6 := by
  decide

example : boolFourValue (BoolFour.ofNat 5) = 5 := by
  decide

example : boolFourValue (BoolFour.ofNat 0) = 0 := by
  decide
