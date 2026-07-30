import WOWII217ClosureSemantics
import WOWII217Closure
open WOWII217Closure WOWII217FiniteBase WOWII217ClosureSemantics

example {n : Nat} (g : BitVec (edgeCount n)) (u : Nat) :
    degreeUpperNat (n := n) g u ≤ n := by
  have h := foldl_bool_count (fun v => adjUpper g u v)
  -- use
  sorry
