import Mathlib

theorem test_foldl_add {α : Type*} (p : α → Bool) (xs : List α) :
    List.foldl (fun count x => count + (if p x then 1 else 0)) 1 xs =
      1 + List.foldl (fun count x => count + (if p x then 1 else 0)) 0 xs := by
  have hhom : ∀ (a : Nat) (y : α),
      (fun count x => count + (if p x then 1 else 0)) (1 + a) y =
        1 + (fun count x => count + (if p x then 1 else 0)) a y := by
    intro a y
    simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  simpa using (List.foldl_hom (f := fun n : Nat => 1 + n)
    (g₁ := fun (a : Nat) (y : α) => a + (if p y then 1 else 0))
    (g₂ := fun (a : Nat) (y : α) => a + (if p y then 1 else 0))
    (l := xs) (init := 0) hhom)
