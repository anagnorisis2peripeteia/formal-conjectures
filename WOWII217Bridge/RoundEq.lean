import WOWII217Bridge.Mask
import WOWII217BondyChvatal
import WOWII217Bridge.Degrees
import WOWII217Bridge.RoundChar

namespace RoundEq

open SimpleGraph Finset WOWII217FiniteBase WOWII217Closure WOWII217ClosureSemantics
open WOWII217Chvatal WOWII217BondyChvatal L7 L145 RoundChar

/-- The mask's adjacency, in either vertex order. -/
theorem adjUpper_mask {n : Nat} (g : BitVec (edgeCount n)) (x y : Fin n) (hne : x ≠ y) :
    adjUpper (n := n) (pathClosureParallelMask (n := n) g) x y
      = (!adjUpper (n := n) g x y &&
          (BitVec.ofNat 5 (n - 1) ≤ degreeUpperBv5 (n := n) g x + degreeUpperBv5 (n := n) g y)) := by
  rcases lt_trichotomy x.val y.val with h | h | h
  · have hm := getLsbD_mask g x.val y.val h y.isLt (upperIndex_lt h y.isLt)
    have hleft : adjUpper (n := n) (pathClosureParallelMask (n := n) g) x y
        = (pathClosureParallelMask (n := n) g).getLsbD (upperIndex x.val y.val) := by
      unfold adjUpper upperIndex; rw [if_pos h]
    rw [hleft, hm]
  · exact absurd (Fin.ext h) hne
  · have hm := getLsbD_mask g y.val x.val h x.isLt (upperIndex_lt h x.isLt)
    rw [adjUpper_comm g y.val x.val] at hm
    have hleft : adjUpper (n := n) (pathClosureParallelMask (n := n) g) x y
        = (pathClosureParallelMask (n := n) g).getLsbD (upperIndex y.val x.val) := by
      unfold adjUpper upperIndex; rw [if_neg (by omega), if_pos h]
    rw [hleft, hm]
    have hcomm : degreeUpperBv5 (n := n) g y.val + degreeUpperBv5 (n := n) g x.val
        = degreeUpperBv5 (n := n) g x.val + degreeUpperBv5 (n := n) g y.val := by
      simp [BitVec.add_comm]
    rw [hcomm]


/-- STEP 2: the bitvector closure round IS the graph closure round. -/
theorem graphOfUpper_parallelRound {n : Nat} (hn : n < 16) (g : BitVec (edgeCount n)) :
    graphOfUpper (n := n) (pathClosureParallelRound (n := n) g)
      = pathClosureRound (graphOfUpper (n := n) g) := by
  classical
  ext x y
  rw [adj_pathClosureRound_iff]
  show adjUpper (n := n) (pathClosureParallelRound (n := n) g) x y = true ↔ _
  unfold pathClosureParallelRound
  rw [adjUpper_or]
  by_cases hxy : x = y
  · subst hxy
    have h1 : adjUpper (n := n) g x x = false := by simp [adjUpper]
    have h2 : adjUpper (n := n) (pathClosureParallelMask (n := n) g) x x = false := by
      simp [adjUpper]
    simp [h1, h2, graphOfUpper]
  · rw [adjUpper_mask g x y hxy]
    have hdx : (graphOfUpper (n := n) g).degree x = degreeUpperNat (n := n) g x :=
      WOWII217ClosureSemantics.degree_graphOfUpper_eq g x
    have hdy : (graphOfUpper (n := n) g).degree y = degreeUpperNat (n := n) g y :=
      WOWII217ClosureSemantics.degree_graphOfUpper_eq g y
    have hcard : Fintype.card (Fin n) = n := Fintype.card_fin n
    rw [hdx, hdy, hcard]
    have hthr := bv5_threshold_iff hn g x.val y.val
    constructor
    · rintro h
      rcases Bool.or_eq_true_iff.mp h with h | h
      · exact Or.inl h
      · rw [Bool.and_eq_true] at h
        exact Or.inr ⟨hxy, hthr.mp (by simpa using h.2)⟩
    · rintro (h | ⟨-, h⟩)
      · exact Bool.or_eq_true_iff.mpr (Or.inl h)
      · by_cases hadj : adjUpper (n := n) g x y = true
        · exact Bool.or_eq_true_iff.mpr (Or.inl hadj)
        · refine Bool.or_eq_true_iff.mpr (Or.inr ?_)
          rw [Bool.and_eq_true]
          exact ⟨by simpa using hadj, by simpa using hthr.mpr h⟩


/-- STEP 3: iterate. -/
theorem graphOfUpper_parallelRounds {n : Nat} (hn : n < 16) :
    ∀ (k : Nat) (g : BitVec (edgeCount n)),
      graphOfUpper (n := n) (pathClosureParallelRounds (n := n) k g)
        = pathClosureIter (graphOfUpper (n := n) g) k := by
  intro k
  induction k with
  | zero => intro g; simp [pathClosureParallelRounds, pathClosureIter]
  | succ k ih =>
      intro g
      have hunfold : pathClosureParallelRounds (n := n) (k + 1) g
          = pathClosureParallelRound (n := n) (pathClosureParallelRounds (n := n) k g) := by
        unfold pathClosureParallelRounds
        rw [List.range_succ, List.foldl_append]
        simp
      rw [hunfold, graphOfUpper_parallelRound hn, ih, pathClosureIter]

/-- THE BRIDGE. -/
theorem traceable_graphOfUpper_pathClosureParallelRounds_iff
    {n : Nat} (hn : n < 16) [Nontrivial (Fin n)] {rounds : Nat} {g : BitVec (edgeCount n)} :
    Traceable (graphOfUpper (n := n) (pathClosureParallelRounds (n := n) rounds g)) ↔
      Traceable (graphOfUpper (n := n) g) := by
  rw [graphOfUpper_parallelRounds hn]
  exact traceable_pathClosureIter_iff _ _

end RoundEq


