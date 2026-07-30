import WOWII217FiniteBase
import WOWII217Closure
import WOWII217Connected10
open WOWII217FiniteBase WOWII217Closure WOWII217Connected10

lemma setBit_getLsbD_fin_copy {w i : Nat} (x : BitVec w) (j : Fin w) (b : Bool) :
    (setBit x i b).getLsbD j = (x.getLsbD j || ((i = j) && b)) := by
  by_cases h' : i = j
  · subst h'
    simp [setBit, BitVec.getLsbD_or, BitVec.getLsbD_and, WOWII217Connected10.bitMask_getLsbD, j.isLt]
  · simp [setBit, BitVec.getLsbD_or, BitVec.getLsbD_and, WOWII217Connected10.bitMask_getLsbD, j.isLt, h']

lemma setBit_eq_copy {w : Nat} {i : Nat} (x : BitVec w) {j : Fin w} (hij : i ≠ j) (b : Bool) :
    (setBit x i b).getLsbD j = x.getLsbD j := by
  cases b <;> simp [setBit_getLsbD_fin_copy, hij]

lemma foldl_setBit_pair_eq_zero {w : Nat} (es : List (Nat × Nat)) (target : Fin w)
    (f : (Nat × Nat) → Bool) :
    (es.foldl (fun current p => setBit current (upperIndex p.1 p.2) (f p)) (BitVec.zero w)).getLsbD target = true ↔
      (∃ p ∈ es, (target : Nat) = upperIndex p.1 p.2 ∧ f p = true) := by
  induction es with
  | nil => simp
  | cons p es ih =>
      rcases p with ⟨pu, pv⟩
      by_cases hidx : upperIndex pu pv = (target : Nat)
      · by_cases hleg : f (pu, pv) = true
        · simp [List.foldl_cons, hidx, hleg, ih, setBit_getLsbD_fin_copy, List.mem_cons,
            and_left_comm, and_assoc, or_left_comm]
        · simp [List.foldl_cons, hidx, hleg, ih, setBit_getLsbD_fin_copy, List.mem_cons,
            and_left_comm, and_assoc, or_left_comm]
      · simp [List.foldl_cons, hidx, ih, setBit_getLsbD_fin_copy, List.mem_cons,
          and_left_comm, and_assoc, or_left_comm]

