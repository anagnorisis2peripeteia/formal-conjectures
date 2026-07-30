import WOWII217Finite13ClosureSharedDeg

example (g : BitVec 78) (u v : Nat)
    (hsum :
      boolFiveValue (degreePairBits13 g u v) =
        degreeUpperNat (n := 13) g u + degreeUpperNat (n := 13) g v) :
    degreePairAtLeast12Upper13 g u v =
      decide (12 ≤ degreeUpperNat (n := 13) g u + degreeUpperNat (n := 13) g v) := by
  apply Bool.eq_iff_iff
  constructor
  · intro h
    have h' : 12 ≤ boolFiveValue (degreePairBits13 g u v) := (boolFiveAtLeast12_iff _).1 h
    simpa [hsum] using h'
  · intro h
    have h' : 12 ≤ boolFiveValue (degreePairBits13 g u v) := by
      simpa [hsum] using h
    exact (boolFiveAtLeast12_iff _).2 h'
