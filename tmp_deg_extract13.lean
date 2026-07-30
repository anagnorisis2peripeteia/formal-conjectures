import WOWII217FiniteBase

open WOWII217FiniteBase

example (g : BitVec 78) (hDeg : fixedDegreeSequenceUpper (n := 13) g [6,6,6,6,6,6,6,5,5,5,5,5,5] = true) : True := by
  have hDeg' := hDeg
  simp [fixedDegreeSequenceUpper, matchesDegreesFromUpper] at hDeg'
  guard_hyp hDeg' : True
  trivial

