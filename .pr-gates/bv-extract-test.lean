import Std.Tactic.BVDecide

example : ∀ x : BitVec 80,
    (BitVec.extractLsb' 32 4 x).ule (BitVec.ofNat 4 15) := by
  bv_decide

example : ∀ x : BitVec 80,
    (BitVec.extractLsb' 32 4 x == 0) || (BitVec.extractLsb' 32 4 x != 0) := by
  bv_decide

example : ∀ x y : BitVec 80,
    (BitVec.extractLsb' 32 4 x == BitVec.extractLsb' 32 4 y) ||
      (BitVec.extractLsb' 32 4 x != BitVec.extractLsb' 32 4 y) := by
  bv_decide

example : ∀ (a b c i : BitVec 4),
    a == (bif i == 0 then b else c) && i == 0 → a == b := by
  bv_decide

example : ∀ (wide : BitVec 80) (a b c i : BitVec 4),
    BitVec.extractLsb' 32 4 wide == (bif i == 0 then b + 15 else c) && i == 0 →
      BitVec.extractLsb' 32 4 wide == b - 1 := by
  bv_decide
