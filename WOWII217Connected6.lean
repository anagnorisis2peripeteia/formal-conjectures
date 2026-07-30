import WOWII217Encoding6

/-! Semantic soundness of the concrete breadth-first connectivity test at order 6. -/

namespace WOWII217Connected6

open SimpleGraph
open WOWII217FiniteBase WOWII217ClosureSemantics

def reachStep6 (g : BitVec 15) (seen : BitVec 6) : BitVec 6 :=
  (List.range 6).foldl (fun next v =>
    let discovered := (List.range 6).any fun u =>
      seen.getLsbD u && adjUpper (n := 6) g u v
    setBit next v discovered) seen

def reachIter6 (g : BitVec 15) : Nat → BitVec 6 → BitVec 6
  | 0, seen => seen
  | rounds + 1, seen => reachIter6 g rounds (reachStep6 g seen)

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

theorem reachStep6_preserves (g : BitVec 15) (seen : BitVec 6)
    (v : Fin 6) (marked : seen.getLsbD v = true) :
    (reachStep6 g seen).getLsbD v = true := by
  unfold reachStep6
  exact foldl_setBit_preserves (List.range 6) _ seen v marked

theorem reachStep6_of_adj (g : BitVec 15) (seen : BitVec 6)
    (u v : Fin 6) (marked : seen.getLsbD u = true)
    (adjacent : adjUpper (n := 6) g u v = true) :
    (reachStep6 g seen).getLsbD v = true := by
  let discovered : Nat → Bool := fun w =>
    (List.range 6).any fun x =>
      seen.getLsbD x && adjUpper (n := 6) g x w
  have discoveredV : discovered v = true := by
    apply List.any_eq_true.mpr
    refine ⟨(u : Nat), List.mem_range.mpr u.isLt, ?_⟩
    simp only [marked, adjacent, Bool.true_and]
  unfold reachStep6
  change ((List.range 6).foldl
      (fun next w => setBit next w (discovered w)) seen).getLsbD v = true
  have mem : (v : Nat) ∈ List.range 6 := List.mem_range.mpr v.isLt
  exact foldl_setBit_sets_of_mem (List.range 6) discovered seen v
    discoveredV mem

theorem reachIter6_preserves (g : BitVec 15) (rounds : Nat)
    (seen : BitVec 6) (v : Fin 6) (marked : seen.getLsbD v = true) :
    (reachIter6 g rounds seen).getLsbD v = true := by
  induction rounds generalizing seen with
  | zero => exact marked
  | succ rounds ih =>
      exact ih (reachStep6 g seen) (reachStep6_preserves g seen v marked)

theorem walk_seen_by_reachIter6 (g : BitVec 15) {u v : Fin 6}
    (p : (graphOfUpper (n := 6) g).Walk u v) (seen : BitVec 6)
    (startMarked : seen.getLsbD u = true) :
    (reachIter6 g p.length seen).getLsbD v = true := by
  induction p generalizing seen with
  | nil => exact startMarked
  | @cons u v w adjacent p ih =>
      apply ih (reachStep6 g seen)
      apply reachStep6_of_adj g seen u v startMarked
      exact adjacent

theorem reachStep6_reachIter6 (g : BitVec 15) (rounds : Nat)
    (seen : BitVec 6) :
    reachStep6 g (reachIter6 g rounds seen) =
      reachIter6 g rounds (reachStep6 g seen) := by
  induction rounds generalizing seen with
  | zero => rfl
  | succ rounds ih =>
      simp only [reachIter6]
      exact ih (reachStep6 g seen)

theorem foldl_range_reachStep6 (g : BitVec 15) (rounds : Nat)
    (seen : BitVec 6) :
    (List.range rounds).foldl (fun current _ => reachStep6 g current) seen =
      reachIter6 g rounds seen := by
  induction rounds generalizing seen with
  | zero => rfl
  | succ rounds ih =>
      rw [List.range_succ, List.foldl_append, ih]
      simp only [List.foldl_cons, List.foldl_nil, reachIter6]
      exact reachStep6_reachIter6 g rounds seen

theorem reachIter6_add (g : BitVec 15) (a b : Nat) (seen : BitVec 6) :
    reachIter6 g (a + b) seen =
      reachIter6 g b (reachIter6 g a seen) := by
  induction a generalizing seen with
  | zero => simp only [Nat.zero_add, reachIter6]
  | succ a ih =>
      rw [Nat.succ_add]
      simp only [reachIter6]
      exact ih (reachStep6 g seen)

theorem reachableFromZeroUpper_eq_reachIter6 (g : BitVec 15) :
    reachableFromZeroUpper (n := 6) g =
      reachIter6 g 6 (BitVec.twoPow 6 0) := by
  unfold reachableFromZeroUpper
  change (List.range 6).foldl (fun current _ => reachStep6 g current)
      (BitVec.twoPow 6 0) = _
  exact foldl_range_reachStep6 g 6 (BitVec.twoPow 6 0)

theorem zero_marked6 :
    (BitVec.twoPow 6 0).getLsbD (0 : Fin 6) = true := by
  native_decide

theorem connectedUpper_of_connected_graphOfUpper6 (g : BitVec 15)
    (connected : (graphOfUpper (n := 6) g).Connected) :
    connectedUpper (n := 6) g = true := by
  unfold connectedUpper
  apply List.all_eq_true.mpr
  intro v hv
  let vFin : Fin 6 := ⟨v, List.mem_range.mp hv⟩
  obtain ⟨p, path⟩ := connected.exists_isPath (0 : Fin 6) vFin
  have reachedAtLength := walk_seen_by_reachIter6 g p
    (BitVec.twoPow 6 0) zero_marked6
  have pathBound : p.length ≤ 6 := Nat.le_of_lt path.length_lt
  obtain ⟨extra, lengthEq⟩ := Nat.exists_eq_add_of_le pathBound
  have reachedAtTwelve :
      (reachIter6 g 6 (BitVec.twoPow 6 0)).getLsbD vFin = true := by
    have iterEq :
        reachIter6 g 6 (BitVec.twoPow 6 0) =
          reachIter6 g (p.length + extra) (BitVec.twoPow 6 0) :=
      congrArg (fun rounds => reachIter6 g rounds (BitVec.twoPow 6 0)) lengthEq
    rw [iterEq]
    rw [reachIter6_add]
    exact reachIter6_preserves g extra _ vFin reachedAtLength
  rw [reachableFromZeroUpper_eq_reachIter6]
  exact reachedAtTwelve

end WOWII217Connected6
