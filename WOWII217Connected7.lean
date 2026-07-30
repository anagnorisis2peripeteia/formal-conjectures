import WOWII217Encoding7

/-! Semantic soundness of the concrete breadth-first connectivity test at order 7. -/

namespace WOWII217Connected7

open SimpleGraph
open WOWII217FiniteBase WOWII217ClosureSemantics

def reachStep7 (g : BitVec 21) (seen : BitVec 7) : BitVec 7 :=
  (List.range 7).foldl (fun next v =>
    let discovered := (List.range 7).any fun u =>
      seen.getLsbD u && adjUpper (n := 7) g u v
    setBit next v discovered) seen

def reachIter7 (g : BitVec 21) : Nat → BitVec 7 → BitVec 7
  | 0, seen => seen
  | rounds + 1, seen => reachIter7 g rounds (reachStep7 g seen)

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

theorem reachStep7_preserves (g : BitVec 21) (seen : BitVec 7)
    (v : Fin 7) (marked : seen.getLsbD v = true) :
    (reachStep7 g seen).getLsbD v = true := by
  unfold reachStep7
  exact foldl_setBit_preserves (List.range 7) _ seen v marked

theorem reachStep7_of_adj (g : BitVec 21) (seen : BitVec 7)
    (u v : Fin 7) (marked : seen.getLsbD u = true)
    (adjacent : adjUpper (n := 7) g u v = true) :
    (reachStep7 g seen).getLsbD v = true := by
  let discovered : Nat → Bool := fun w =>
    (List.range 7).any fun x =>
      seen.getLsbD x && adjUpper (n := 7) g x w
  have discoveredV : discovered v = true := by
    apply List.any_eq_true.mpr
    refine ⟨(u : Nat), List.mem_range.mpr u.isLt, ?_⟩
    simp only [marked, adjacent, Bool.true_and]
  unfold reachStep7
  change ((List.range 7).foldl
      (fun next w => setBit next w (discovered w)) seen).getLsbD v = true
  have mem : (v : Nat) ∈ List.range 7 := List.mem_range.mpr v.isLt
  exact foldl_setBit_sets_of_mem (List.range 7) discovered seen v
    discoveredV mem

theorem reachIter7_preserves (g : BitVec 21) (rounds : Nat)
    (seen : BitVec 7) (v : Fin 7) (marked : seen.getLsbD v = true) :
    (reachIter7 g rounds seen).getLsbD v = true := by
  induction rounds generalizing seen with
  | zero => exact marked
  | succ rounds ih =>
      exact ih (reachStep7 g seen) (reachStep7_preserves g seen v marked)

theorem walk_seen_by_reachIter7 (g : BitVec 21) {u v : Fin 7}
    (p : (graphOfUpper (n := 7) g).Walk u v) (seen : BitVec 7)
    (startMarked : seen.getLsbD u = true) :
    (reachIter7 g p.length seen).getLsbD v = true := by
  induction p generalizing seen with
  | nil => exact startMarked
  | @cons u v w adjacent p ih =>
      apply ih (reachStep7 g seen)
      apply reachStep7_of_adj g seen u v startMarked
      exact adjacent

theorem reachStep7_reachIter7 (g : BitVec 21) (rounds : Nat)
    (seen : BitVec 7) :
    reachStep7 g (reachIter7 g rounds seen) =
      reachIter7 g rounds (reachStep7 g seen) := by
  induction rounds generalizing seen with
  | zero => rfl
  | succ rounds ih =>
      simp only [reachIter7]
      exact ih (reachStep7 g seen)

theorem foldl_range_reachStep7 (g : BitVec 21) (rounds : Nat)
    (seen : BitVec 7) :
    (List.range rounds).foldl (fun current _ => reachStep7 g current) seen =
      reachIter7 g rounds seen := by
  induction rounds generalizing seen with
  | zero => rfl
  | succ rounds ih =>
      rw [List.range_succ, List.foldl_append, ih]
      simp only [List.foldl_cons, List.foldl_nil, reachIter7]
      exact reachStep7_reachIter7 g rounds seen

theorem reachIter7_add (g : BitVec 21) (a b : Nat) (seen : BitVec 7) :
    reachIter7 g (a + b) seen =
      reachIter7 g b (reachIter7 g a seen) := by
  induction a generalizing seen with
  | zero => simp only [Nat.zero_add, reachIter7]
  | succ a ih =>
      rw [Nat.succ_add]
      simp only [reachIter7]
      exact ih (reachStep7 g seen)

theorem reachableFromZeroUpper_eq_reachIter7 (g : BitVec 21) :
    reachableFromZeroUpper (n := 7) g =
      reachIter7 g 7 (BitVec.twoPow 7 0) := by
  unfold reachableFromZeroUpper
  change (List.range 7).foldl (fun current _ => reachStep7 g current)
      (BitVec.twoPow 7 0) = _
  exact foldl_range_reachStep7 g 7 (BitVec.twoPow 7 0)

theorem zero_marked7 :
    (BitVec.twoPow 7 0).getLsbD (0 : Fin 7) = true := by
  native_decide

theorem connectedUpper_of_connected_graphOfUpper7 (g : BitVec 21)
    (connected : (graphOfUpper (n := 7) g).Connected) :
    connectedUpper (n := 7) g = true := by
  unfold connectedUpper
  apply List.all_eq_true.mpr
  intro v hv
  let vFin : Fin 7 := ⟨v, List.mem_range.mp hv⟩
  obtain ⟨p, path⟩ := connected.exists_isPath (0 : Fin 7) vFin
  have reachedAtLength := walk_seen_by_reachIter7 g p
    (BitVec.twoPow 7 0) zero_marked7
  have pathBound : p.length ≤ 7 := Nat.le_of_lt path.length_lt
  obtain ⟨extra, lengthEq⟩ := Nat.exists_eq_add_of_le pathBound
  have reachedAtTwelve :
      (reachIter7 g 7 (BitVec.twoPow 7 0)).getLsbD vFin = true := by
    have iterEq :
        reachIter7 g 7 (BitVec.twoPow 7 0) =
          reachIter7 g (p.length + extra) (BitVec.twoPow 7 0) :=
      congrArg (fun rounds => reachIter7 g rounds (BitVec.twoPow 7 0)) lengthEq
    rw [iterEq]
    rw [reachIter7_add]
    exact reachIter7_preserves g extra _ vFin reachedAtLength
  rw [reachableFromZeroUpper_eq_reachIter7]
  exact reachedAtTwelve

end WOWII217Connected7
