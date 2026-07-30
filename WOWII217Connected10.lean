import WOWII217Encoding10

/-! Semantic soundness of the concrete breadth-first connectivity test at order 10. -/

namespace WOWII217Connected10

open SimpleGraph
open WOWII217FiniteBase WOWII217ClosureSemantics

def reachStep10 (g : BitVec 45) (seen : BitVec 10) : BitVec 10 :=
  (List.range 10).foldl (fun next v =>
    let discovered := (List.range 10).any fun u =>
      seen.getLsbD u && adjUpper (n := 10) g u v
    setBit next v discovered) seen

def reachIter10 (g : BitVec 45) : Nat → BitVec 10 → BitVec 10
  | 0, seen => seen
  | rounds + 1, seen => reachIter10 g rounds (reachStep10 g seen)

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

theorem reachStep10_preserves (g : BitVec 45) (seen : BitVec 10)
    (v : Fin 10) (marked : seen.getLsbD v = true) :
    (reachStep10 g seen).getLsbD v = true := by
  unfold reachStep10
  exact foldl_setBit_preserves (List.range 10) _ seen v marked

theorem reachStep10_of_adj (g : BitVec 45) (seen : BitVec 10)
    (u v : Fin 10) (marked : seen.getLsbD u = true)
    (adjacent : adjUpper (n := 10) g u v = true) :
    (reachStep10 g seen).getLsbD v = true := by
  let discovered : Nat → Bool := fun w =>
    (List.range 10).any fun x =>
      seen.getLsbD x && adjUpper (n := 10) g x w
  have discoveredV : discovered v = true := by
    apply List.any_eq_true.mpr
    refine ⟨(u : Nat), List.mem_range.mpr u.isLt, ?_⟩
    simp only [marked, adjacent, Bool.true_and]
  unfold reachStep10
  change ((List.range 10).foldl
      (fun next w => setBit next w (discovered w)) seen).getLsbD v = true
  have mem : (v : Nat) ∈ List.range 10 := List.mem_range.mpr v.isLt
  exact foldl_setBit_sets_of_mem (List.range 10) discovered seen v
    discoveredV mem

theorem reachIter10_preserves (g : BitVec 45) (rounds : Nat)
    (seen : BitVec 10) (v : Fin 10) (marked : seen.getLsbD v = true) :
    (reachIter10 g rounds seen).getLsbD v = true := by
  induction rounds generalizing seen with
  | zero => exact marked
  | succ rounds ih =>
      exact ih (reachStep10 g seen) (reachStep10_preserves g seen v marked)

theorem walk_seen_by_reachIter10 (g : BitVec 45) {u v : Fin 10}
    (p : (graphOfUpper (n := 10) g).Walk u v) (seen : BitVec 10)
    (startMarked : seen.getLsbD u = true) :
    (reachIter10 g p.length seen).getLsbD v = true := by
  induction p generalizing seen with
  | nil => exact startMarked
  | @cons u v w adjacent p ih =>
      apply ih (reachStep10 g seen)
      apply reachStep10_of_adj g seen u v startMarked
      exact adjacent

theorem reachStep10_reachIter10 (g : BitVec 45) (rounds : Nat)
    (seen : BitVec 10) :
    reachStep10 g (reachIter10 g rounds seen) =
      reachIter10 g rounds (reachStep10 g seen) := by
  induction rounds generalizing seen with
  | zero => rfl
  | succ rounds ih =>
      simp only [reachIter10]
      exact ih (reachStep10 g seen)

theorem foldl_range_reachStep10 (g : BitVec 45) (rounds : Nat)
    (seen : BitVec 10) :
    (List.range rounds).foldl (fun current _ => reachStep10 g current) seen =
      reachIter10 g rounds seen := by
  induction rounds generalizing seen with
  | zero => rfl
  | succ rounds ih =>
      rw [List.range_succ, List.foldl_append, ih]
      simp only [List.foldl_cons, List.foldl_nil, reachIter10]
      exact reachStep10_reachIter10 g rounds seen

theorem reachIter10_add (g : BitVec 45) (a b : Nat) (seen : BitVec 10) :
    reachIter10 g (a + b) seen =
      reachIter10 g b (reachIter10 g a seen) := by
  induction a generalizing seen with
  | zero => simp only [Nat.zero_add, reachIter10]
  | succ a ih =>
      rw [Nat.succ_add]
      simp only [reachIter10]
      exact ih (reachStep10 g seen)

theorem reachableFromZeroUpper_eq_reachIter10 (g : BitVec 45) :
    reachableFromZeroUpper (n := 10) g =
      reachIter10 g 10 (BitVec.twoPow 10 0) := by
  unfold reachableFromZeroUpper
  change (List.range 10).foldl (fun current _ => reachStep10 g current)
      (BitVec.twoPow 10 0) = _
  exact foldl_range_reachStep10 g 10 (BitVec.twoPow 10 0)

theorem zero_marked10 :
    (BitVec.twoPow 10 0).getLsbD (0 : Fin 10) = true := by
  native_decide

theorem connectedUpper_of_connected_graphOfUpper10 (g : BitVec 45)
    (connected : (graphOfUpper (n := 10) g).Connected) :
    connectedUpper (n := 10) g = true := by
  unfold connectedUpper
  apply List.all_eq_true.mpr
  intro v hv
  let vFin : Fin 10 := ⟨v, List.mem_range.mp hv⟩
  obtain ⟨p, path⟩ := connected.exists_isPath (0 : Fin 10) vFin
  have reachedAtLength := walk_seen_by_reachIter10 g p
    (BitVec.twoPow 10 0) zero_marked10
  have pathBound : p.length ≤ 10 := Nat.le_of_lt path.length_lt
  obtain ⟨extra, lengthEq⟩ := Nat.exists_eq_add_of_le pathBound
  have reachedAtFourteen :
      (reachIter10 g 10 (BitVec.twoPow 10 0)).getLsbD vFin = true := by
    have iterEq :
        reachIter10 g 10 (BitVec.twoPow 10 0) =
          reachIter10 g (p.length + extra) (BitVec.twoPow 10 0) :=
      congrArg (fun rounds => reachIter10 g rounds (BitVec.twoPow 10 0)) lengthEq
    rw [iterEq]
    rw [reachIter10_add]
    exact reachIter10_preserves g extra _ vFin reachedAtLength
  rw [reachableFromZeroUpper_eq_reachIter10]
  exact reachedAtFourteen

end WOWII217Connected10
