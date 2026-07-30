import WOWII217FiniteBase

lemma setBit_getLsbD_fin {w i : Nat} (x : BitVec w) (j : Fin w) (b : Bool) :
    (setBit x i b).getLsbD j = (x.getLsbD j || ((i = j) && b)) := by
  cases b <;> simp [setBit, BitVec.getLsbD_or, BitVec.getLsbD_and, bitMask, j.isLt, eq_comm]
