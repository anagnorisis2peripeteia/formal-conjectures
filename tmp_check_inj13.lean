import WOWII217Closure13Fast
import WOWII217Finite13

open WOWII217Closure
example {u1 v1 u2 v2 : Nat}
    (hu1 : u1 < v1) (hv1 : v1 < 13)
    (hu2 : u2 < v2) (hv2 : v2 < 13)
    (h : upperIndex u1 v1 = upperIndex u2 v2) :
    u1 = u2 ∧ v1 = v2 := by
  omega
