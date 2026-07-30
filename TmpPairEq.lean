import WOWII217Closure13Fast
import WOWII217Finite13
import WOWII217Closure

open WOWII217Closure13Fast WOWII217Finite13 WOWII217FiniteBase WOWII217Closure

-- need BoolFour and degree values

theorem test_degreePairAtLeast12Upper13_eq (g : BitVec 78) (u v : Nat) :
    degreePairAtLeast12Upper13 g u v =
      decide (12 ≤ degreeUpperNat (n := 13) g u + degreeUpperNat (n := 13) g v) := by
  have hsum :
      boolFiveValue (degreePairBits13 g u v) =
        degreeUpperNat (n := 13) g u + degreeUpperNat (n := 13) g v := by
    sorry
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro h
    have h' : 12 ≤ boolFiveValue (degreePairBits13 g u v) := (by
      --
      sorry)
    simpa [hsum] using h'
  · intro h
    have h' : 12 ≤ boolFiveValue (degreePairBits13 g u v) := by
      simpa [hsum] using h
    exact (boolFiveAtLeast12_iff _).2 h'
