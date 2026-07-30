import WOWII217ClosureSemantics

open WOWII217FiniteBase WOWII217ClosureSemantics

example (g : BitVec 78) (hDeg : fixedDegreeSequenceUpper (n := 13) g [6,6,6,6,6,6,6,5,5,5,5,5,5] = true)
    : (degreeUpperNat (n := 13) g 0) = 6 := by
  have hDeg' : matchesDegreesFromUpper (n := 13) g 0 [6,6,6,6,6,6,6,5,5,5,5,5,5] = true := by
    simpa [fixedDegreeSequenceUpper] using hDeg
  have h0 : (degreeBitsUpper (n := 13) g 0).same (BoolFour.ofNat 6) = true :=
    by exact (List.all_eq_true.mp hDeg').1
  have h0' := (boolFourSame_eq_true_iff _ _).1 h0
  rw [h0']
  exact boolFourValue_degreeBitsUpper_eq (n := 13) (by decide)
