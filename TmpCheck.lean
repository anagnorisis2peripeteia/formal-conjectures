import WOWII217ClosureSemantics
import WOWII217BondyChvatal
import WOWII217FiniteBase

open SimpleGraph
open WOWII217FiniteBase WOWII217ClosureSemantics WOWII217BondyChvatal

namespace Tmp

def reachStep13 (g : BitVec 78) (seen : BitVec 13) : BitVec 13 :=
  (List.range 13).foldl (fun next v =>
    let discovered := (List.range 13).any fun u =>
      seen.getLsbD u && adjUpper (n := 13) g u v
    setBit next v discovered) seen

def reachIter13 (g : BitVec 78) : Nat → BitVec 13 → BitVec 13
  | 0, seen => seen
  | rounds + 1, seen => reachIter13 g rounds (reachStep13 g seen)

theorem setBit_preserves {w : Nat} (x : BitVec w) (i : Nat) (b : Bool)
    (v : Nat) (marked : x.getLsbD v = true) :
    (setBit x i b).getLsbD v = true := by
  simp only [setBit, BitVec.getLsbD_or, marked, Bool.true_or]

theorem setBit_self_true {w : Nat} (x : BitVec w) (v : Fin w) :
    (setBit x v true).getLsbD v = true := by
  simp only [setBit, BitVec.getLsbD_or, BitVec.getLsbD_and,
    WOWII217FiniteBase.bitMask, BitVec.getLsbD_replicate, Bool.true_and]
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

theorem reachStep13_preserves (g : BitVec 78) (seen : BitVec 13)
    (v : Fin 13) (marked : seen.getLsbD v = true) :
    (reachStep13 g seen).getLsbD v = true := by
  unfold reachStep13
  exact foldl_setBit_preserves (List.range 13) _ seen v marked

theorem reachStep13_of_adj (g : BitVec 78) (seen : BitVec 13)
    (u v : Fin 13) (marked : seen.getLsbD u = true)
    (adjacent : adjUpper (n := 13) g u v = true) :
    (reachStep13 g seen).getLsbD v = true := by
  let discovered : Nat → Bool := fun w =>
    (List.range 13).any fun x => seen.getLsbD x && adjUpper (n := 13) g x w
  have discoveredV : discovered v = true := by
    apply List.any_eq_true.mpr
    refine ⟨(u : Nat), List.mem_range.mpr u.isLt, ?_⟩
    simp only [marked, adjacent, Bool.true_and]
  unfold reachStep13
  change ((List.range 13).foldl (fun next w => setBit next w (discovered w)) seen).getLsbD v = true
  have mem : (v : Nat) ∈ List.range 13 := List.mem_range.mpr v.isLt
  exact foldl_setBit_sets_of_mem (List.range 13) discovered seen v
    discoveredV mem

theorem reachIter13_preserves (g : BitVec 78) (rounds : Nat)
    (seen : BitVec 13) (v : Fin 13) (marked : seen.getLsbD v = true) :
    (reachIter13 g rounds seen).getLsbD v = true := by
  induction rounds generalizing seen with
  | zero => exact marked
  | succ rounds ih =>
      exact ih (reachStep13 g seen) (reachStep13_preserves g seen v marked)

theorem walk_seen_by_reachIter13 (g : BitVec 78) {u v : Fin 13}
    (p : (graphOfUpper (n := 13) g).Walk u v) (seen : BitVec 13)
    (startMarked : seen.getLsbD u = true) :
    (reachIter13 g p.length seen).getLsbD v = true := by
  induction p generalizing seen with
  | nil => exact startMarked
  | @cons u v w adjacent p ih =>
      apply ih (reachStep13 g seen)
      exact reachStep13_of_adj g seen u v startMarked adjacent

theorem reachStep13_reachIter13 (g : BitVec 78) (rounds : Nat)
    (seen : BitVec 13) :
    reachStep13 g (reachIter13 g rounds seen) =
      reachIter13 g rounds (reachStep13 g seen) := by
  induction rounds generalizing seen with
  | zero => rfl
  | succ rounds ih =>
      simp [reachIter13]
      exact ih (reachStep13 g seen)

theorem foldl_range_reachStep13 (g : BitVec 78) (rounds : Nat)
    (seen : BitVec 13) :
    (List.range rounds).foldl (fun current _ => reachStep13 g current) seen =
      reachIter13 g rounds seen := by
  induction rounds generalizing seen with
  | zero => rfl
  | succ rounds ih =>
      rw [List.range_succ, List.foldl_append, ih]
      simp only [List.foldl_cons, List.foldl_nil, reachIter13]
      exact reachStep13_reachIter13 g rounds seen

theorem reachIter13_add (g : BitVec 78) (a b : Nat) (seen : BitVec 13) :
    reachIter13 g (a + b) seen =
      reachIter13 g b (reachIter13 g a seen) := by
  induction a generalizing seen with
  | zero => simp only [Nat.zero_add, reachIter13]
  | succ a ih =>
      rw [Nat.succ_add]
      simp only [reachIter13]
      exact ih (reachStep13 g seen)

theorem reachableFromZeroUpper_eq_reachIter13 (g : BitVec 78) :
    reachableFromZeroUpper (n := 13) g =
      reachIter13 g 13 (BitVec.twoPow 13 0) := by
  unfold reachableFromZeroUpper
  change (List.range 13).foldl (fun current _ => reachStep13 g current)
      (BitVec.twoPow 13 0) = _
  exact foldl_range_reachStep13 g 13 (BitVec.twoPow 13 0)

theorem zero_marked13 :
    (BitVec.twoPow 13 0).getLsbD (0 : Fin 13) = true := by
  native_decide

theorem connectedUpper_of_connected_graphOfUpper13 (g : BitVec 78)
    (connected : (graphOfUpper (n := 13) g).Connected) :
    connectedUpper (n := 13) g = true := by
  unfold connectedUpper
  apply List.all_eq_true.mpr
  intro v hv
  let vFin : Fin 13 := ⟨v, List.mem_range.mp hv⟩
  obtain ⟨p, path⟩ := connected.exists_isPath (0 : Fin 13) vFin
  have reachedAtLength := walk_seen_by_reachIter13 g p (BitVec.twoPow 13 0) zero_marked13
  have pathBound : p.length ≤ 13 := Nat.le_of_lt path.length_lt
  obtain ⟨extra, lengthEq⟩ := Nat.exists_eq_add_of_le pathBound
  have reachedAtThirteen :
      (reachIter13 g 13 (BitVec.twoPow 13 0)).getLsbD vFin = true := by
    have iterEq :
        reachIter13 g 13 (BitVec.twoPow 13 0) =
          reachIter13 g (p.length + extra) (BitVec.twoPow 13 0) :=
      congrArg (fun rounds => reachIter13 g rounds (BitVec.twoPow 13 0)) lengthEq
    rw [iterEq]
    rw [reachIter13_add]
    exact reachIter13_preserves g extra _ vFin reachedAtLength
  rw [reachableFromZeroUpper_eq_reachIter13]
  exact reachedAtThirteen

end Tmp
