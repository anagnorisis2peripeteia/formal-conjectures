import WOWII217Closure13Fast

open WOWII217Closure13Fast

example (x : BoolFive) : True := by
  rcases x with ⟨b0,b1,b2,b3,b4⟩
  simp

#check (fun x : BoolFive => x.b0)

