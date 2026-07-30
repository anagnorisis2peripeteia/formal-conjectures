import WOWII217Closure13Fast
import WOWII217Finite13

open WOWII217FiniteBase WOWII217Closure

namespace Tmp

def highOnly (seen : BitVec 13) : Prop :=
  ∀ v : Nat, seen.getLsbD v = true → v < 7

def reachStep13 (g : BitVec 78) (seen : BitVec 13) : BitVec 13 :=
  (List.range 13).foldl (fun next v =>
    let discovered : Nat → Bool := fun w =>
      (List.range 13).any fun u => seen.getLsbD u && adjUpper (n := 13) g u w
    setBit next v (discovered v)) seen

def reachIter13 (g : BitVec 78) : Nat → BitVec 13 → BitVec 13
  | 0, seen => seen
  | rounds + 1, seen => reachIter13 g rounds (reachStep13 g seen)

theorem setBit_preserves {w : Nat} (x : BitVec w) (i : Nat) (b : Bool)
    (v : Nat) (marked : x.getLsbD v = true) :
    (setBit x i b).getLsbD v = true := by
  simp only [setBit, BitVec.getLsbD_or, marked, Bool.true_or]

 theorem foldl_setBit_preserves {w : Nat} (xs : List Nat)
    (f : Nat → Bool) (seen : BitVec w) (v : Nat)
    (marked : seen.getLsbD v = true) :
    (xs.foldl (fun current i => setBit current i (f i)) seen).getLsbD v = true := by
  induction xs generalizing seen with
  | nil => simpa using marked
  | cons i xs ih =>
      simp only [List.foldl_cons]
      exact ih (setBit seen i (f i)) (setBit_preserves seen i (f i) v marked)

theorem reachStep13_preserves (g : BitVec 78) (seen : BitVec 13)
    (hNoCross : ¬∃ u < 7, ∃ offset < 6, adjUpper (n := 13) g u (offset + 7) = true)
    (hHigh : highOnly seen) :
    highOnly (reachStep13 g seen) := by
  intro v hv
  have hvlt : v < 13 := by
    sorry
  have hdiscovered :
      ((List.range 13).any fun u => seen.getLsbD u && adjUpper (n := 13) g u v) = true := by
    simpa [reachStep13, Bool.or_eq_true] using hv
  sorry

end Tmp
