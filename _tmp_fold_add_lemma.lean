import WOWII217Closure13Fast

open WOWII217Closure13Fast

lemma boolFoldl_add_eq_demo (f : Nat → Bool) (a : Nat) :
    ∀ (xs : List Nat),
      xs.foldl (fun count x => count + if f x then 1 else 0) a =
        a + xs.foldl (fun count x => count + if f x then 1 else 0) 0 := by
  intro xs
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp [List.foldl_cons, ih, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

#check boolFoldl_add_eq_demo
