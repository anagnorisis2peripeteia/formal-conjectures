import WOWII217Finite13
import WOWII217Encoding13
import WOWII217Closure13Fast

open WOWII217Finite13 WOWII217FiniteBase WOWII217Closure13Fast WOWII217Closure


def counterG : SimpleGraph (Fin 13) :=
  { Adj := by
      intro u v
      by_cases h : u = v
      · subst h
        exact False
      · have hu : u.1 = 0 ∨ u.1 = 1 ∨ u.1 = 2 ∨ u.1 = 3 ∨ u.1 = 4 ∨ u.1 = 5 ∨ u.1 = 7 ∨
          u.1 = 6 ∨ u.1 = 8 ∨ u.1 = 9 ∨ u.1 = 10 ∨ u.1 = 11 ∨ u.1 = 12 := by
          sorry
        sorry }



-- temporary
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
example : True := by
  trivial
