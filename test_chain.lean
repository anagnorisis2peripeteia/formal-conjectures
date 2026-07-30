import WOWII217FiniteBase

open WOWII217FiniteBase

example (g : BitVec 78)
  (hdeg : fixedDegreeSequenceUpper (n := 13) g [6,6,6,6,6,6,6,5,5,5,5,5,5] = true) :
    degreeUpperNat (n := 13) g 0 = 6 := by
  have hlen : (List.length [6, 6, 6, 6, 6, 6, 6, 5, 5, 5, 5, 5, 5] : Nat) = 13 := by decide
  have hmatch : matchesDegreesFromUpper (n := 13) g 0 [6,6,6,6,6,6,6,5,5,5,5,5,5] = true := by
    exact (Bool.and_eq_true.mp hdeg).2
  have hfirst : (degreeBitsUpper (n := 13) g 0).same (BoolFour.ofNat 6) = true := by
    simpa [matchesDegreesFromUpper] using hmatch
  -- convert
  have hnf : boolFourValue (degreeBitsUpper (n := 13) g 0) = 6 := by
    have hbits := (BoolFourSame_eq_true_iff _ _).1 hfirst
    simpa [BoolFour.ofNat] using congrArg boolFourValue hbits
  --
  exact by
    have hb := (boolFourValue_degreeBitsUpper_eq (n := 13) g 0 (by decide))
    omega
