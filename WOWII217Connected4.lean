import WOWII217Encoding4

/-! Semantic soundness of the concrete breadth-first connectivity test at order 4. -/

namespace WOWII217Connected4

open SimpleGraph
open WOWII217FiniteBase WOWII217ClosureSemantics

def reachStep4 (g : BitVec 6) (seen : BitVec 4) : BitVec 4 :=
  (List.range 4).foldl (fun next v =>
    let discovered := (List.range 4).any fun u =>
      seen.getLsbD u && adjUpper (n := 4) g u v
    setBit next v discovered) seen

def reachIter4 (g : BitVec 6) : Nat → BitVec 4 → BitVec 4
  | 0, seen => seen
  | rounds + 1, seen => reachIter4 g rounds (reachStep4 g seen)

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

theorem reachStep4_preserves (g : BitVec 6) (seen : BitVec 4)
    (v : Fin 4) (marked : seen.getLsbD v = true) :
    (reachStep4 g seen).getLsbD v = true := by
  unfold reachStep4
  exact foldl_setBit_preserves (List.range 4) _ seen v marked

theorem reachStep4_of_adj (g : BitVec 6) (seen : BitVec 4)
    (u v : Fin 4) (marked : seen.getLsbD u = true)
    (adjacent : adjUpper (n := 4) g u v = true) :
    (reachStep4 g seen).getLsbD v = true := by
  let discovered : Nat → Bool := fun w =>
    (List.range 4).any fun x =>
      seen.getLsbD x && adjUpper (n := 4) g x w
  have discoveredV : discovered v = true := by
    apply List.any_eq_true.mpr
    refine ⟨(u : Nat), List.mem_range.mpr u.isLt, ?_⟩
    simp only [marked, adjacent, Bool.true_and]
  unfold reachStep4
  change ((List.range 4).foldl
      (fun next w => setBit next w (discovered w)) seen).getLsbD v = true
  have mem : (v : Nat) ∈ List.range 4 := List.mem_range.mpr v.isLt
  exact foldl_setBit_sets_of_mem (List.range 4) discovered seen v
    discoveredV mem

theorem reachIter4_preserves (g : BitVec 6) (rounds : Nat)
    (seen : BitVec 4) (v : Fin 4) (marked : seen.getLsbD v = true) :
    (reachIter4 g rounds seen).getLsbD v = true := by
  induction rounds generalizing seen with
  | zero => exact marked
  | succ rounds ih =>
      exact ih (reachStep4 g seen) (reachStep4_preserves g seen v marked)

theorem walk_seen_by_reachIter4 (g : BitVec 6) {u v : Fin 4}
    (p : (graphOfUpper (n := 4) g).Walk u v) (seen : BitVec 4)
    (startMarked : seen.getLsbD u = true) :
    (reachIter4 g p.length seen).getLsbD v = true := by
  induction p generalizing seen with
  | nil => exact startMarked
  | @cons u v w adjacent p ih =>
      apply ih (reachStep4 g seen)
      apply reachStep4_of_adj g seen u v startMarked
      exact adjacent

theorem reachStep4_reachIter4 (g : BitVec 6) (rounds : Nat)
    (seen : BitVec 4) :
    reachStep4 g (reachIter4 g rounds seen) =
      reachIter4 g rounds (reachStep4 g seen) := by
  induction rounds generalizing seen with
  | zero => rfl
  | succ rounds ih =>
      simp only [reachIter4]
      exact ih (reachStep4 g seen)

theorem foldl_range_reachStep4 (g : BitVec 6) (rounds : Nat)
    (seen : BitVec 4) :
    (List.range rounds).foldl (fun current _ => reachStep4 g current) seen =
      reachIter4 g rounds seen := by
  induction rounds generalizing seen with
  | zero => rfl
  | succ rounds ih =>
      rw [List.range_succ, List.foldl_append, ih]
      simp only [List.foldl_cons, List.foldl_nil, reachIter4]
      exact reachStep4_reachIter4 g rounds seen

theorem reachIter4_add (g : BitVec 6) (a b : Nat) (seen : BitVec 4) :
    reachIter4 g (a + b) seen =
      reachIter4 g b (reachIter4 g a seen) := by
  induction a generalizing seen with
  | zero => simp only [Nat.zero_add, reachIter4]
  | succ a ih =>
      rw [Nat.succ_add]
      simp only [reachIter4]
      exact ih (reachStep4 g seen)

theorem reachableFromZeroUpper_eq_reachIter4 (g : BitVec 6) :
    reachableFromZeroUpper (n := 4) g =
      reachIter4 g 4 (BitVec.twoPow 4 0) := by
  unfold reachableFromZeroUpper
  change (List.range 4).foldl (fun current _ => reachStep4 g current)
      (BitVec.twoPow 4 0) = _
  exact foldl_range_reachStep4 g 4 (BitVec.twoPow 4 0)

theorem zero_marked4 :
    (BitVec.twoPow 4 0).getLsbD (0 : Fin 4) = true := by
  native_decide

theorem connectedUpper_of_connected_graphOfUpper4 (g : BitVec 6)
    (connected : (graphOfUpper (n := 4) g).Connected) :
    connectedUpper (n := 4) g = true := by
  unfold connectedUpper
  apply List.all_eq_true.mpr
  intro v hv
  let vFin : Fin 4 := ⟨v, List.mem_range.mp hv⟩
  obtain ⟨p, path⟩ := connected.exists_isPath (0 : Fin 4) vFin
  have reachedAtLength := walk_seen_by_reachIter4 g p
    (BitVec.twoPow 4 0) zero_marked4
  have pathBound : p.length ≤ 4 := Nat.le_of_lt path.length_lt
  obtain ⟨extra, lengthEq⟩ := Nat.exists_eq_add_of_le pathBound
  have reachedAtTwelve :
      (reachIter4 g 4 (BitVec.twoPow 4 0)).getLsbD vFin = true := by
    have iterEq :
        reachIter4 g 4 (BitVec.twoPow 4 0) =
          reachIter4 g (p.length + extra) (BitVec.twoPow 4 0) :=
      congrArg (fun rounds => reachIter4 g rounds (BitVec.twoPow 4 0)) lengthEq
    rw [iterEq]
    rw [reachIter4_add]
    exact reachIter4_preserves g extra _ vFin reachedAtLength
  rw [reachableFromZeroUpper_eq_reachIter4]
  exact reachedAtTwelve

end WOWII217Connected4
