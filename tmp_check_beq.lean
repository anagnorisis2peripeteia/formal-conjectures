import WOWII217Closure

example (x y : BitVec 8) : (x == y) = decide (x = y) := by
  rfl

example (x y : BitVec 8) : x = y → ((x == y) = true) := by
  intro h
  simpa [h]
