import WOWII217Closure
import WOWII217ClosureSemantics
import WOWII217FiniteBase
import WOWII217Connected10
open WOWII217FiniteBase WOWII217Closure WOWII217Connected10

lemma bitMask_getLsbD_copy {w : Nat} (b : Bool) (v : Fin w) :
    (bitMask (w := w) b).getLsbD v = b := by
  simpa using WOWII217Connected10.bitMask_getLsbD (w := w) b v

lemma setBit_getLsbD_fin_copy {w i : Nat} (x : BitVec w) (j : Fin w) (b : Bool) :
    (setBit x i b).getLsbD j = (x.getLsbD j || ((i = j) && b)) := by
  cases b <;> simp [setBit, BitVec.getLsbD_or, BitVec.getLsbD_and, bitMask_getLsbD_copy, j.isLt]

