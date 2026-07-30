import WOWII217FiniteBase

open WOWII217FiniteBase

example (g : BitVec 78) (h : fixedDegreeSequenceUpper (n := 13) g [6,6,6,6,6,6,6,5,5,5,5,5,5] = true)
    : degreeUpperNat (n := 13) g 0 = 6 := by
  have h' : matchesDegreesFromUpper (n := 13) g 0 [6,6,6,6,6,6,6,5,5,5,5,5,5] = true := by
    exact (Bool.and_eq_true.mp h).2
  simp [matchesDegreesFromUpper] at h'
  omega
