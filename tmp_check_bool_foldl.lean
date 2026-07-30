import WOWII217Finite13ClosureSharedDeg

namespace Test

-- trying helper lemmas for bool fold

theorem list_foldl_add_eq {α : Type*} (f : α → Bool) (a : Nat) :
    ∀ (xs : List α),
      List.foldl (fun count x => count + if f x then 1 else 0) a xs =
        a + List.foldl (fun count x => count + if f x then 1 else 0) 0 xs := by
  intro xs
  induction xs with
  | nil => simp
  | cons x xs ih =>
      calc
        List.foldl (fun count x_1 => count + (if f x_1 then 1 else 0)) a (x :: xs) =
            List.foldl (fun count x_1 => count + (if f x_1 then 1 else 0)) (a + if f x then 1 else 0) xs := by
              simp
        _ = (a + if f x then 1 else 0) + List.foldl (fun count x_1 => count + (if f x_1 then 1 else 0)) 0 xs := by
              simpa using ih (a + if f x then 1 else 0)
        _ = a + ((if f x then 1 else 0) + List.foldl (fun count x_1 => count + (if f x_1 then 1 else 0)) 0 xs) := by
              omega
        _ = a + (List.foldl (fun count x_1 => count + (if f x_1 then 1 else 0)) (if f x then 1 else 0) 0 xs) := by
              simp
        _ = a + (List.foldl (fun count x_1 => count + (if f x_1 then 1 else 0)) 0 (x :: xs)) := by
              simp

-- second step: shifted fold equals head-then-tail

theorem foldl_tail_cons {α : Type*} (f : α → Bool) (x : α) (xs : List α) :
    (x :: xs).foldl (fun count x => count + if f x then 1 else 0) 0 =
      (if f x then 1 else 0) + (xs.foldl (fun count x => count + if f x then 1 else 0) 0) := by
  simp [List.foldl]
  simpa [Nat.zero_add, add_assoc] using (list_foldl_add_eq (f := f) (a := if f x then 1 else 0) xs)

-- testing bound lemma

theorem bool_sum_le_length {α : Type*} (f : α → Bool) :
    ∀ (xs : List α) (a : Nat),
      List.foldl (fun c x => c + if f x then 1 else 0) a xs ≤ a + xs.length := by
  intro xs
  induction xs with
  | nil => intro a; simp
  | cons x xs ih =>
      intro a
      by_cases h : f x
      · simp [h, ih]
      · simp [h, ih]

end Test
