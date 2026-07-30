import FormalConjecturesUtil
import Std.Tactic.BVDecide

example : ∀ x : BitVec 8, x.getLsbD 3 = x.getLsbD 3 := by
  simp only [BitVec.getLsbD_eq_extractLsb']
  bv_decide

example : ∀ x : BitVec 8, x.getLsbD 3 == x.getLsbD 3 := by
  simp only [BitVec.getLsbD_eq_extractLsb']
  bv_decide

example : ∀ x y : BitVec 8, x = y → x.getLsbD 3 = y.getLsbD 3 := by
  simp only [BitVec.getLsbD_eq_extractLsb']
  bv_decide

example : ∀ x y : BitVec 8, x == y → x.getLsbD 3 == y.getLsbD 3 := by
  simp only [BitVec.getLsbD_eq_extractLsb']
  bv_decide

example : ∀ x : BitVec (4 * 4), x.getLsbD 3 = x.getLsbD 3 := by
  simp only [BitVec.getLsbD_eq_extractLsb']
  bv_decide

example : ∀ x : BitVec ((2 ^ 4) * 4), x.getLsbD 55 = x.getLsbD 55 := by
  simp only [BitVec.getLsbD_eq_extractLsb']
  bv_decide

example : ∀ x y : BitVec (4 * 4),
    BitVec.extractLsb' 0 4 x == BitVec.extractLsb' 0 4 y →
      BitVec.extractLsb' 0 4 x == BitVec.extractLsb' 0 4 y := by
  bv_decide

example : ∀ x : BitVec 4, x == 0 → x.ule 1 := by
  bv_decide

example : ∀ x : BitVec 16,
    BitVec.extractLsb' 0 4 x == 0 → (BitVec.extractLsb' 0 4 x).ule 1 := by
  bv_decide

example : ∀ x y : BitVec 16,
    BitVec.extractLsb' 0 4 x == BitVec.extractLsb' 4 4 y →
      (BitVec.extractLsb' 0 4 x).ule (BitVec.extractLsb' 4 4 y) := by
  bv_decide
