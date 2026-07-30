import WOWII217Closure13Fast

example (x y : BitVec 78) : x = y ↔ (x.toNat = y.toNat) := by
  constructor
  · intro h
    simpa [h]
  · intro h
    exact BitVec.eq_of_toNat_eq h

example (x y : BitVec 78) : x = y := by
  ext i
  decide
