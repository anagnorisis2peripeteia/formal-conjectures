import WOWII217Bridge.ChvBridge
import WOWII217ResidueBound
namespace WOWII217OneFact
open SimpleGraph WOWII217ResidueBound ChvBridge

/-- ONE decidable fact replacing the whole 47-way case split for n=4:
any nonincreasing residue-2 list of length 4, max ≤ 6, with no zero entry, all entries < 4,
and not one of the two guarded sequences, satisfies the Chvatal condition. -/
def chvOrGuarded4 : Bool :=
  forallNoninc 4 6 [] fun s =>
    !decide (residueAux s = 2) || decide (0 ∈ s) || decide (s.any (fun d => decide (4 ≤ d)))
      || decide (s = [2,2,1,1]) || decide (s = [3,2,2,1])
      || decide (s.sum % 2 = 1)
      || decide (s.headD 0 < 2)
      || decide (¬ ((s.filter (fun d => decide (d = 3))).length ≤ s.getLastD 0))
      || chvatalPathList 4 s

theorem chvOrGuarded4_eq_true : chvOrGuarded4 = true := by native_decide
