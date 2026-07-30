import WOWII217Encoding5

/-! Semantic soundness of the concrete breadth-first connectivity test at order 5. -/

namespace WOWII217Connected5

open SimpleGraph
open WOWII217FiniteBase WOWII217ClosureSemantics

def reachStep5 (g : BitVec 10) (seen : BitVec 5) : BitVec 5 :=
  (List.range 5).foldl (fun next v =>
    let discovered := (List.range 5).any fun u =>
      seen.getLsbD u && adjUpper (n := 5) g u v
    setBit next v discovered) seen

def reachIter5 (g : BitVec 10) : Nat → BitVec 5 → BitVec 5
  | 0, seen => seen
  | rounds + 1, seen => reachIter5 g rounds (reachStep5 g seen)

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

theorem reachStep5_preserves (g : BitVec 10) (seen : BitVec 5)
    (v : Fin 5) (marked : seen.getLsbD v = true) :
    (reachStep5 g seen).getLsbD v = true := by
  unfold reachStep5
  exact foldl_setBit_preserves (List.range 5) _ seen v marked

theorem reachStep5_of_adj (g : BitVec 10) (seen : BitVec 5)
    (u v : Fin 5) (marked : seen.getLsbD u = true)
    (adjacent : adjUpper (n := 5) g u v = true) :
    (reachStep5 g seen).getLsbD v = true := by
  let discovered : Nat → Bool := fun w =>
    (List.range 5).any fun x =>
      seen.getLsbD x && adjUpper (n := 5) g x w
  have discoveredV : discovered v = true := by
    apply List.any_eq_true.mpr
    refine ⟨(u : Nat), List.mem_range.mpr u.isLt, ?_⟩
    simp only [marked, adjacent, Bool.true_and]
  unfold reachStep5
  change ((List.range 5).foldl
      (fun next w => setBit next w (discovered w)) seen).getLsbD v = true
  have mem : (v : Nat) ∈ List.range 5 := List.mem_range.mpr v.isLt
  exact foldl_setBit_sets_of_mem (List.range 5) discovered seen v
    discoveredV mem

theorem reachIter5_preserves (g : BitVec 10) (rounds : Nat)
    (seen : BitVec 5) (v : Fin 5) (marked : seen.getLsbD v = true) :
    (reachIter5 g rounds seen).getLsbD v = true := by
  induction rounds generalizing seen with
  | zero => exact marked
  | succ rounds ih =>
      exact ih (reachStep5 g seen) (reachStep5_preserves g seen v marked)

theorem walk_seen_by_reachIter5 (g : BitVec 10) {u v : Fin 5}
    (p : (graphOfUpper (n := 5) g).Walk u v) (seen : BitVec 5)
    (startMarked : seen.getLsbD u = true) :
    (reachIter5 g p.length seen).getLsbD v = true := by
  induction p generalizing seen with
  | nil => exact startMarked
  | @cons u v w adjacent p ih =>
      apply ih (reachStep5 g seen)
      apply reachStep5_of_adj g seen u v startMarked
      exact adjacent

theorem reachStep5_reachIter5 (g : BitVec 10) (rounds : Nat)
    (seen : BitVec 5) :
    reachStep5 g (reachIter5 g rounds seen) =
      reachIter5 g rounds (reachStep5 g seen) := by
  induction rounds generalizing seen with
  | zero => rfl
  | succ rounds ih =>
      simp only [reachIter5]
      exact ih (reachStep5 g seen)

theorem foldl_range_reachStep5 (g : BitVec 10) (rounds : Nat)
    (seen : BitVec 5) :
    (List.range rounds).foldl (fun current _ => reachStep5 g current) seen =
      reachIter5 g rounds seen := by
  induction rounds generalizing seen with
  | zero => rfl
  | succ rounds ih =>
      rw [List.range_succ, List.foldl_append, ih]
      simp only [List.foldl_cons, List.foldl_nil, reachIter5]
      exact reachStep5_reachIter5 g rounds seen

theorem reachIter5_add (g : BitVec 10) (a b : Nat) (seen : BitVec 5) :
    reachIter5 g (a + b) seen =
      reachIter5 g b (reachIter5 g a seen) := by
  induction a generalizing seen with
  | zero => simp only [Nat.zero_add, reachIter5]
  | succ a ih =>
      rw [Nat.succ_add]
      simp only [reachIter5]
      exact ih (reachStep5 g seen)

theorem reachableFromZeroUpper_eq_reachIter5 (g : BitVec 10) :
    reachableFromZeroUpper (n := 5) g =
      reachIter5 g 5 (BitVec.twoPow 5 0) := by
  unfold reachableFromZeroUpper
  change (List.range 5).foldl (fun current _ => reachStep5 g current)
      (BitVec.twoPow 5 0) = _
  exact foldl_range_reachStep5 g 5 (BitVec.twoPow 5 0)

theorem zero_marked5 :
    (BitVec.twoPow 5 0).getLsbD (0 : Fin 5) = true := by
  native_decide

theorem connectedUpper_of_connected_graphOfUpper5 (g : BitVec 10)
    (connected : (graphOfUpper (n := 5) g).Connected) :
    connectedUpper (n := 5) g = true := by
  unfold connectedUpper
  apply List.all_eq_true.mpr
  intro v hv
  let vFin : Fin 5 := ⟨v, List.mem_range.mp hv⟩
  obtain ⟨p, path⟩ := connected.exists_isPath (0 : Fin 5) vFin
  have reachedAtLength := walk_seen_by_reachIter5 g p
    (BitVec.twoPow 5 0) zero_marked5
  have pathBound : p.length ≤ 5 := Nat.le_of_lt path.length_lt
  obtain ⟨extra, lengthEq⟩ := Nat.exists_eq_add_of_le pathBound
  have reachedAtTwelve :
      (reachIter5 g 5 (BitVec.twoPow 5 0)).getLsbD vFin = true := by
    have iterEq :
        reachIter5 g 5 (BitVec.twoPow 5 0) =
          reachIter5 g (p.length + extra) (BitVec.twoPow 5 0) :=
      congrArg (fun rounds => reachIter5 g rounds (BitVec.twoPow 5 0)) lengthEq
    rw [iterEq]
    rw [reachIter5_add]
    exact reachIter5_preserves g extra _ vFin reachedAtLength
  rw [reachableFromZeroUpper_eq_reachIter5]
  exact reachedAtTwelve

end WOWII217Connected5
