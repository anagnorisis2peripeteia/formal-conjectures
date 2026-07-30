import WOWII217Closure13Fast

open WOWII217Closure13Fast

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in

def boolFiveValue (x : BoolFive) : Nat :=
  (if x.b0 then 1 else 0) +
  2 * (if x.b1 then 1 else 0) +
  4 * (if x.b2 then 1 else 0) +
  8 * (if x.b3 then 1 else 0) +
  16 * (if x.b4 then 1 else 0)

theorem boolFiveValue_increment_of_lt_thirtyOne (x : BoolFive) (b : Bool)
    (hx : boolFiveValue x < 31) :
    boolFiveValue (x.increment b) = boolFiveValue x + if b then 1 else 0 := by
  rcases x with ⟨x0, x1, x2, x3, x4⟩
  fin_cases x0 <;> fin_cases x1 <;> fin_cases x2 <;> fin_cases x3 <;> fin_cases x4 <;>
    fin_cases b <;> simp [boolFiveValue, BoolFive.increment] at hx ⊢

theorem boolFiveValue_foldl_increment (f : α → Bool) (xs : List α) (initial : BoolFive)
    (hbound : boolFiveValue initial + xs.length < 31) :
    boolFiveValue (xs.foldl (fun bits x => bits.increment (f x)) initial) =
      boolFiveValue initial + (xs.foldl (fun count x => count + if f x then 1 else 0) 0) := by
  induction xs generalizing initial with
  | nil => simp at hbound
  | cons x xs ih =>
      have hcons : boolFiveValue initial + (xs.length + 1) < 31 := by
        simpa [List.length, Nat.add_assoc] using hbound
      have hinitial : boolFiveValue initial < 31 := by omega
      by_cases hx : f x = true
      · have hnext : boolFiveValue (initial.increment true) + xs.length < 31 := by
          rw [boolFiveValue_increment_of_lt_thirtyOne initial true hinitial]
          simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hcons
        have htail := ih (initial.increment true) hnext
        rw [List.foldl_cons, hx]
        calc
          boolFiveValue (List.foldl (fun bits y => bits.increment (f y)) (initial.increment true) xs) =
              boolFiveValue (initial.increment true) +
                List.foldl (fun count y => count + if f y then 1 else 0) 0 xs := htail
          _ = boolFiveValue initial + 1 + List.foldl (fun count y => count + if f y then 1 else 0) 0 xs := by
              rw [boolFiveValue_increment_of_lt_thirtyOne initial true hinitial]
          _ = boolFiveValue initial + List.foldl (fun count y => count + if f y then 1 else 0) 1 xs := by
              simp [List.foldl_cons, hx, Nat.add_assoc]
      · have hnext : boolFiveValue (initial.increment false) + xs.length < 31 := by
          rw [boolFiveValue_increment_of_lt_thirtyOne initial false hinitial]
          simpa [hx, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hcons
        have htail := ih (initial.increment false) hnext
        rw [List.foldl_cons, hx]
        calc
          boolFiveValue (List.foldl (fun bits y => bits.increment (f y)) (initial.increment false) xs) =
              boolFiveValue (initial.increment false) +
                List.foldl (fun count y => count + if f y then 1 else 0) 0 xs := htail
          _ = boolFiveValue initial + List.foldl (fun count y => count + if f y then 1 else 0) 0 xs := by
                rw [boolFiveValue_increment_of_lt_thirtyOne initial false hinitial]
          _ = boolFiveValue initial + List.foldl (fun count y => count + if f y then 1 else 0) 0 xs := rfl
