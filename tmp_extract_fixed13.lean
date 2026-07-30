import Mathlib
import WOWII217Finite13
import WOWII217FiniteBase
import WOWII217Closure13Fast
import WOWII217ClosureCertificateSemantics

open WOWII217FiniteBase WOWII217ClosureSemantics WOWII217Closure13Fast WOWII217Finite13

example (g : BitVec 78)
    (hDeg : fixedDegreeSequenceUpper g
      [6, 6, 6, 6, 6, 6, 6, 5, 5, 5, 5, 5, 5] = true)
    (v : Nat) (hv : v < 13) :
    degreeUpperNat (n := 13) g v = (if v < 7 then 6 else 5) := by
  let vf : Fin 13 := ⟨v, hv⟩
  fin_cases vf <;> simp at hv
  · cases hDeg
