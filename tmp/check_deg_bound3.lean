import WOWII217ClosureSemantics
import WOWII217Closure
import WOWII217FiniteBase
open WOWII217Closure WOWII217FiniteBase WOWII217ClosureSemantics
open Finset

example {n : Nat} (g : BitVec (edgeCount n)) (u : Nat) :
    degreeUpperNat (n := n) g u ≤ n := by
  rw [degreeUpperNat]
  have hfilter := foldl_bool_count (fun v => adjUpper g u v) (List.range n) List.nodup_range 0
  have hcard : ({x ∈ (Finset.range n) | adjUpper g u x = true}.card : Nat) ≤ (Finset.range n).card :=
    Finset.card_filter_le (Finset.range n) (fun x => adjUpper g u x = true)
  rw [← hfilter]
  simpa using hcard
