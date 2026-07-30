import Mathlib

#check Set.toFinset_diff

example (s : Set (Fin 13)) [Fintype s] (v : Fin 13) :
    ((Set.diff s ({v} : Set (Fin 13))).toFinset) = s.toFinset.erase v := by
  classical
  simpa using (Set.toFinset_diff (s := s) (t := ({v} : Set (Fin 13))) )

