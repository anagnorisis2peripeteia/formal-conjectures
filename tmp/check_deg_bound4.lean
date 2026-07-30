import WOWII217ClosureSemantics
import WOWII217Closure
import WOWII217FiniteBase
open WOWII217Closure WOWII217FiniteBase

example {n : Nat} (g : BitVec (edgeCount n)) (u : Nat) :
    degreeUpperNat (n := n) g u ≤ n := by
  unfold degreeUpperNat
  have hbound : ∀ (l : List Nat) (m : Nat),
      l.foldl (fun d v => d + (if adjUpper g u v then 1 else 0)) m ≤ m + l.length := by
    intro l
    induction l with
    | nil =>
        intro m
        simp
    | cons v l ih =>
        intro m
        by_cases hv : adjUpper g u v = true
        · have h := ih (m + 1)
          simpa [List.foldl_cons, hv, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h
        · have h := ih m
          have h' : m + l.length ≤ m + (l.length + 1) := by omega
          calc
            List.foldl (fun d v => d + (if adjUpper g u v = true then 1 else 0)) m (v :: l)
                ≤ m + l.length := by simpa [List.foldl_cons, hv] using h
            _ ≤ m + (l.length + 1) := h'
  have := hbound (List.range n) 0
  simpa using this
