import WOWII217Finite13
import WOWII217FiniteBase

open WOWII217FiniteBase

set_option maxRecDepth 100000 in
example (g : BitVec 78) (u v : Fin 13) :
    adjUpper (n := 13) g u v = adjUpper (n := 13) g v u := by
  cases' lt_or_ge u.1 v.1 with huv huvge
  · have hvu : ¬ v.1 < u.1 := Nat.not_lt_of_ge huvge
    simp [adjUpper, huv, hvu]
  · have huvle : v.1 ≤ u.1 := huvge
    have hvu : v.1 < u.1 ∨ v.1 = u.1 := lt_or_eq_of_le huvge
    cases' hvu with hvu1 hvuEq
    · have huv : ¬ u.1 < v.1 := Nat.not_lt_of_ge (Nat.le_of_lt hvu1)
      simp [adjUpper, huv, hvu1]
    · subst hvuEq
      simp [adjUpper]

