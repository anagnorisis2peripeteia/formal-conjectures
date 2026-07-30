import WOWII217Encoding9

/-! Semantic soundness of the concrete breadth-first connectivity test at order 9. -/

namespace WOWII217Connected9

open SimpleGraph
open WOWII217FiniteBase WOWII217ClosureSemantics

def reachStep9 (g : BitVec 36) (seen : BitVec 9) : BitVec 9 :=
  (List.range 9).foldl (fun next v =>
    let discovered := (List.range 9).any fun u =>
      seen.getLsbD u && adjUpper (n := 9) g u v
    setBit next v discovered) seen

def reachIter9 (g : BitVec 36) : Nat → BitVec 9 → BitVec 9
  | 0, seen => seen
  | rounds + 1, seen => reachIter9 g rounds (reachStep9 g seen)

theorem setBit_preserves {w : Nat} (x : BitVec w) (i : Nat) (b : Bool)
    (v : Nat) (marked : x.getLsbD v = true) :
    (setBit x i b).getLsbD v = true := by
  simp only [setBit, BitVec.getLsbD_or, marked, Bool.true_or]

theorem bitMask_getLsbD {w : Nat} (b : Bool) (v : Fin w) :
    (bitMask (w := w) b).getLsbD v = b := by
  simp only [bitMask, BitVec.getLsbD_cast, BitVec.getLsbD_replicate,
    Nat.one_mul, v.isLt, decide_true, Bool.true_and, Nat.mod_one,
    BitVec.getLsbD_ofBool]

theorem setBit_self_true {w : Nat} (x : BitVec w) (v : Fin w) :
    (setBit x v true).getLsbD v = true := by
  simp only [setBit, BitVec.getLsbD_or, BitVec.getLsbD_and,
    bitMask_getLsbD, Bool.true_and]
  rw [BitVec.getLsbD_twoPow]
  simp [v.isLt]

theorem foldl_setBit_preserves {w : Nat} (xs : List Nat)
    (f : Nat → Bool) (seen : BitVec w) (v : Nat)
    (marked : seen.getLsbD v = true) :
    (xs.foldl (fun current i => setBit current i (f i)) seen).getLsbD v = true := by
  induction xs generalizing seen with
  | nil => exact marked
  | cons i xs ih =>
      simp only [List.foldl_cons]
      exact ih (setBit seen i (f i)) (setBit_preserves seen i (f i) v marked)

theorem foldl_setBit_sets_of_mem {w : Nat} (xs : List Nat)
    (f : Nat → Bool) (seen : BitVec w) (v : Fin w)
    (enabled : f v = true) (mem : (v : Nat) ∈ xs) :
    (xs.foldl (fun current i => setBit current i (f i)) seen).getLsbD v = true := by
  induction xs generalizing seen with
  | nil => simp at mem
  | cons i xs ih =>
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp mem with head | tail
      · subst i
        apply foldl_setBit_preserves
        rw [enabled]
        exact setBit_self_true seen v
      · exact ih (setBit seen i (f i)) tail

theorem reachStep9_preserves (g : BitVec 36) (seen : BitVec 9)
    (v : Fin 9) (marked : seen.getLsbD v = true) :
    (reachStep9 g seen).getLsbD v = true := by
  unfold reachStep9
  exact foldl_setBit_preserves (List.range 9) _ seen v marked

theorem reachStep9_of_adj (g : BitVec 36) (seen : BitVec 9)
    (u v : Fin 9) (marked : seen.getLsbD u = true)
    (adjacent : adjUpper (n := 9) g u v = true) :
    (reachStep9 g seen).getLsbD v = true := by
  let discovered : Nat → Bool := fun w =>
    (List.range 9).any fun x =>
      seen.getLsbD x && adjUpper (n := 9) g x w
  have discoveredV : discovered v = true := by
    apply List.any_eq_true.mpr
    refine ⟨(u : Nat), List.mem_range.mpr u.isLt, ?_⟩
    simp only [marked, adjacent, Bool.true_and]
  unfold reachStep9
  change ((List.range 9).foldl
      (fun next w => setBit next w (discovered w)) seen).getLsbD v = true
  have mem : (v : Nat) ∈ List.range 9 := List.mem_range.mpr v.isLt
  exact foldl_setBit_sets_of_mem (List.range 9) discovered seen v
    discoveredV mem

theorem reachIter9_preserves (g : BitVec 36) (rounds : Nat)
    (seen : BitVec 9) (v : Fin 9) (marked : seen.getLsbD v = true) :
    (reachIter9 g rounds seen).getLsbD v = true := by
  induction rounds generalizing seen with
  | zero => exact marked
  | succ rounds ih =>
      exact ih (reachStep9 g seen) (reachStep9_preserves g seen v marked)

theorem walk_seen_by_reachIter9 (g : BitVec 36) {u v : Fin 9}
    (p : (graphOfUpper (n := 9) g).Walk u v) (seen : BitVec 9)
    (startMarked : seen.getLsbD u = true) :
    (reachIter9 g p.length seen).getLsbD v = true := by
  induction p generalizing seen with
  | nil => exact startMarked
  | @cons u v w adjacent p ih =>
      apply ih (reachStep9 g seen)
      apply reachStep9_of_adj g seen u v startMarked
      exact adjacent

theorem reachStep9_reachIter9 (g : BitVec 36) (rounds : Nat)
    (seen : BitVec 9) :
    reachStep9 g (reachIter9 g rounds seen) =
      reachIter9 g rounds (reachStep9 g seen) := by
  induction rounds generalizing seen with
  | zero => rfl
  | succ rounds ih =>
      simp only [reachIter9]
      exact ih (reachStep9 g seen)

theorem foldl_range_reachStep9 (g : BitVec 36) (rounds : Nat)
    (seen : BitVec 9) :
    (List.range rounds).foldl (fun current _ => reachStep9 g current) seen =
      reachIter9 g rounds seen := by
  induction rounds generalizing seen with
  | zero => rfl
  | succ rounds ih =>
      rw [List.range_succ, List.foldl_append, ih]
      simp only [List.foldl_cons, List.foldl_nil, reachIter9]
      exact reachStep9_reachIter9 g rounds seen

theorem reachIter9_add (g : BitVec 36) (a b : Nat) (seen : BitVec 9) :
    reachIter9 g (a + b) seen =
      reachIter9 g b (reachIter9 g a seen) := by
  induction a generalizing seen with
  | zero => simp only [Nat.zero_add, reachIter9]
  | succ a ih =>
      rw [Nat.succ_add]
      simp only [reachIter9]
      exact ih (reachStep9 g seen)

theorem reachableFromZeroUpper_eq_reachIter9 (g : BitVec 36) :
    reachableFromZeroUpper (n := 9) g =
      reachIter9 g 9 (BitVec.twoPow 9 0) := by
  unfold reachableFromZeroUpper
  change (List.range 9).foldl (fun current _ => reachStep9 g current)
      (BitVec.twoPow 9 0) = _
  exact foldl_range_reachStep9 g 9 (BitVec.twoPow 9 0)

theorem zero_marked9 :
    (BitVec.twoPow 9 0).getLsbD (0 : Fin 9) = true := by
  native_decide

theorem connectedUpper_of_connected_graphOfUpper9 (g : BitVec 36)
    (connected : (graphOfUpper (n := 9) g).Connected) :
    connectedUpper (n := 9) g = true := by
  unfold connectedUpper
  apply List.all_eq_true.mpr
  intro v hv
  let vFin : Fin 9 := ⟨v, List.mem_range.mp hv⟩
  obtain ⟨p, path⟩ := connected.exists_isPath (0 : Fin 9) vFin
  have reachedAtLength := walk_seen_by_reachIter9 g p
    (BitVec.twoPow 9 0) zero_marked9
  have pathBound : p.length ≤ 9 := Nat.le_of_lt path.length_lt
  obtain ⟨extra, lengthEq⟩ := Nat.exists_eq_add_of_le pathBound
  have reachedAtTwelve :
      (reachIter9 g 9 (BitVec.twoPow 9 0)).getLsbD vFin = true := by
    have iterEq :
        reachIter9 g 9 (BitVec.twoPow 9 0) =
          reachIter9 g (p.length + extra) (BitVec.twoPow 9 0) :=
      congrArg (fun rounds => reachIter9 g rounds (BitVec.twoPow 9 0)) lengthEq
    rw [iterEq]
    rw [reachIter9_add]
    exact reachIter9_preserves g extra _ vFin reachedAtLength
  rw [reachableFromZeroUpper_eq_reachIter9]
  exact reachedAtTwelve

end WOWII217Connected9
