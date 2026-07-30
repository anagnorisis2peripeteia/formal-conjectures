import WOWII217Finite13ClosureSharedDeg

open WOWII217Finite13ClosureSharedDeg WOWII217FiniteBase WOWII217Closure

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in

example (g : BitVec 78)
    (hDeg : fixedDegreeSequenceUpper (n := 13) g
      [6, 6, 6, 6, 6, 6, 6, 5, 5, 5, 5, 5, 5] = true) :
    (degreeBitsUpper (n := 13) g 0).same (BoolFour.ofNat 6) = true := by
  have hmatches :
      matchesDegreesFromUpper (n := 13) g 0 [6, 6, 6, 6, 6, 6, 6, 5, 5, 5, 5, 5, 5] = true := by
    simpa [fixedDegreeSequenceUpper] using hDeg
  exact (Bool.and_eq_true.mp hmatches).1
