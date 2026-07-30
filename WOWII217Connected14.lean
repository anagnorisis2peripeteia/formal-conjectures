import WOWII217Encoding
import WOWII217DP
import WOWII217Semantics

/-! Semantic soundness of the concrete breadth-first connectivity test at order 14. -/

namespace WOWII217Connected14

open SimpleGraph
open WOWII217DP
open WOWII217Encoding
open WOWII217Semantics (graphOfUpper14)

/-- Local graph view matching `graphOfUpper14` but using `WOWII217DP.adjUpper`. -/
def graphOfUpper14DP (g : BitVec 91) : SimpleGraph (Fin 14) where
  Adj u v := adjUpper (n := 14) g u v = true
  symm := by
    intro u v h
    have : adjUpper (n := 14) g v u = adjUpper (n := 14) g u v := by
      -- same formula as Semantics.adjUpper_comm
      by_cases huv : (u : Nat) < v
      · have hvu : ¬ (v : Nat) < u := Nat.not_lt_of_ge (Nat.le_of_lt huv)
        simp [adjUpper, huv, hvu]
      · by_cases hvu : (v : Nat) < u
        · simp [adjUpper, huv, hvu]
        · have : (u : Nat) = v :=
            Nat.le_antisymm (Nat.le_of_not_gt hvu) (Nat.le_of_not_gt huv)
          cases Fin.ext this
          simp [adjUpper] at h
    simpa [this] using h
  loopless := by
    intro u
    simp [adjUpper]

theorem graphOfUpper14DP_eq (g : BitVec 91) :
    graphOfUpper14DP g = graphOfUpper14 g := by
  ext u v
  change adjUpper (n := 14) g u v = true ↔
      WOWII217Semantics.adjUpper (n := 14) g u v = true
  have : adjUpper (n := 14) g u v =
      WOWII217Semantics.adjUpper (n := 14) g u v := rfl
  simp [this]

def reachStep14 (g : BitVec 91) (seen : BitVec 14) : BitVec 14 :=
  (List.range 14).foldl (fun next v =>
    let discovered := (List.range 14).any fun u =>
      seen.getLsbD u && adjUpper (n := 14) g u v
    setBit next v discovered) seen

def reachIter14 (g : BitVec 91) : Nat → BitVec 14 → BitVec 14
  | 0, seen => seen
  | rounds + 1, seen => reachIter14 g rounds (reachStep14 g seen)

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

theorem reachStep14_preserves (g : BitVec 91) (seen : BitVec 14)
    (v : Fin 14) (marked : seen.getLsbD v = true) :
    (reachStep14 g seen).getLsbD v = true := by
  unfold reachStep14
  exact foldl_setBit_preserves (List.range 14) _ seen v marked

theorem reachStep14_of_adj (g : BitVec 91) (seen : BitVec 14)
    (u v : Fin 14) (marked : seen.getLsbD u = true)
    (adjacent : adjUpper (n := 14) g u v = true) :
    (reachStep14 g seen).getLsbD v = true := by
  let discovered : Nat → Bool := fun w =>
    (List.range 14).any fun x =>
      seen.getLsbD x && adjUpper (n := 14) g x w
  have discoveredV : discovered v = true := by
    apply List.any_eq_true.mpr
    refine ⟨(u : Nat), List.mem_range.mpr u.isLt, ?_⟩
    simp only [marked, adjacent, Bool.true_and]
  unfold reachStep14
  change ((List.range 14).foldl
      (fun next w => setBit next w (discovered w)) seen).getLsbD v = true
  have mem : (v : Nat) ∈ List.range 14 := List.mem_range.mpr v.isLt
  exact foldl_setBit_sets_of_mem (List.range 14) discovered seen v
    discoveredV mem

theorem reachIter14_preserves (g : BitVec 91) (rounds : Nat)
    (seen : BitVec 14) (v : Fin 14) (marked : seen.getLsbD v = true) :
    (reachIter14 g rounds seen).getLsbD v = true := by
  induction rounds generalizing seen with
  | zero => exact marked
  | succ rounds ih =>
      exact ih (reachStep14 g seen) (reachStep14_preserves g seen v marked)

theorem walk_seen_by_reachIter14 (g : BitVec 91) {u v : Fin 14}
    (p : (graphOfUpper14DP g).Walk u v) (seen : BitVec 14)
    (startMarked : seen.getLsbD u = true) :
    (reachIter14 g p.length seen).getLsbD v = true := by
  induction p generalizing seen with
  | nil => exact startMarked
  | @cons u v w adjacent p ih =>
      apply ih (reachStep14 g seen)
      apply reachStep14_of_adj g seen u v startMarked
      exact adjacent

theorem reachStep14_reachIter14 (g : BitVec 91) (rounds : Nat)
    (seen : BitVec 14) :
    reachStep14 g (reachIter14 g rounds seen) =
      reachIter14 g rounds (reachStep14 g seen) := by
  induction rounds generalizing seen with
  | zero => rfl
  | succ rounds ih =>
      simp only [reachIter14]
      exact ih (reachStep14 g seen)

theorem foldl_range_reachStep14 (g : BitVec 91) (rounds : Nat)
    (seen : BitVec 14) :
    (List.range rounds).foldl (fun current _ => reachStep14 g current) seen =
      reachIter14 g rounds seen := by
  induction rounds generalizing seen with
  | zero => rfl
  | succ rounds ih =>
      rw [List.range_succ, List.foldl_append, ih]
      simp only [List.foldl_cons, List.foldl_nil, reachIter14]
      exact reachStep14_reachIter14 g rounds seen

theorem reachIter14_add (g : BitVec 91) (a b : Nat) (seen : BitVec 14) :
    reachIter14 g (a + b) seen =
      reachIter14 g b (reachIter14 g a seen) := by
  induction a generalizing seen with
  | zero => simp only [Nat.zero_add, reachIter14]
  | succ a ih =>
      rw [Nat.succ_add]
      simp only [reachIter14]
      exact ih (reachStep14 g seen)

set_option maxHeartbeats 400000 in
theorem reachableFromZeroUpper_eq_reachIter14 (g : BitVec 91) :
    reachableFromZeroUpper (n := 14) g =
      reachIter14 g 14 (BitVec.twoPow 14 0) := by
  unfold reachableFromZeroUpper
  change (List.range 14).foldl (fun current _ => reachStep14 g current)
      (BitVec.twoPow 14 0) = _
  exact foldl_range_reachStep14 g 14 (BitVec.twoPow 14 0)

theorem zero_marked14 :
    (BitVec.twoPow 14 0).getLsbD (0 : Fin 14) = true := by
  native_decide

theorem connectedUpper_of_connected_graphOfUpper14DP (g : BitVec 91)
    (connected : (graphOfUpper14DP g).Connected) :
    connectedUpper (n := 14) g = true := by
  unfold connectedUpper
  apply List.all_eq_true.mpr
  intro v hv
  let vFin : Fin 14 := ⟨v, List.mem_range.mp hv⟩
  obtain ⟨p, path⟩ := connected.exists_isPath (0 : Fin 14) vFin
  have reachedAtLength := walk_seen_by_reachIter14 g p
    (BitVec.twoPow 14 0) zero_marked14
  have pathBound : p.length ≤ 14 := Nat.le_of_lt path.length_lt
  obtain ⟨extra, lengthEq⟩ := Nat.exists_eq_add_of_le pathBound
  have reachedAtFourteen :
      (reachIter14 g 14 (BitVec.twoPow 14 0)).getLsbD vFin = true := by
    have iterEq :
        reachIter14 g 14 (BitVec.twoPow 14 0) =
          reachIter14 g (p.length + extra) (BitVec.twoPow 14 0) :=
      congrArg (fun rounds => reachIter14 g rounds (BitVec.twoPow 14 0)) lengthEq
    rw [iterEq]
    rw [reachIter14_add]
    exact reachIter14_preserves g extra _ vFin reachedAtLength
  rw [reachableFromZeroUpper_eq_reachIter14]
  exact reachedAtFourteen

/-- Connectivity of the encoded `SimpleGraph` implies the Bool certificate. -/
theorem connectedUpper_encodeUpper14_of_connected
    (G : SimpleGraph (Fin 14)) [DecidableRel G.Adj]
    (connected : G.Connected) :
    connectedUpper (n := 14) (encodeUpper14 G) = true := by
  have hgraph : graphOfUpper14DP (encodeUpper14 G) = G := by
    rw [graphOfUpper14DP_eq, graphOfUpper14_encodeUpper14]
  have connected' : (graphOfUpper14DP (encodeUpper14 G)).Connected := by
    rw [hgraph]
    exact connected
  exact connectedUpper_of_connected_graphOfUpper14DP _ connected'

end WOWII217Connected14
