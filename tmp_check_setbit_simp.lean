import WOWII217Closure
open WOWII217FiniteBase

lemma test {w : Nat} (x : BitVec w) (i j : Nat) (b : Bool) :
    (setBit x j b).getLsbD i =
      (x.getLsbD i || (b && decide (j = i))) := by
  by_cases h : j = i
  · subst h
    simp [setBit, Bool.and_eq_true]
  · simp [setBit, h]

