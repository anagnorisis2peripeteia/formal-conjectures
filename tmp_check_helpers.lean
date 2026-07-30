import WOWII217Finite13ClosureSharedDeg

open WOWII217Finite13ClosureSharedDeg WOWII217FiniteBase

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in

/-- Local copies to avoid importing semantic file. -/
def boolFourValue (x : BoolFour) : Nat :=
  (if x.b0 then 1 else 0) +
  2 * (if x.b1 then 1 else 0) +
  4 * (if x.b2 then 1 else 0) +
  8 * (if x.b3 then 1 else 0)

theorem boolFourSame_eq_true_iff (x y : BoolFour) :
    x.same y = true ↔ x = y := by
  rcases x with ⟨x0, x1, x2, x3⟩
  rcases y with ⟨y0, y1, y2, y3⟩
  fin_cases x0 <;> fin_cases x1 <;> fin_cases x2 <;> fin_cases x3 <;>
    fin_cases y0 <;> fin_cases y1 <;> fin_cases y2 <;> fin_cases y3 <;>
    decide

theorem boolFourValue_ofNat_of_lt_sixteen (d : Nat) (hd : d < 16) :
    boolFourValue (BoolFour.ofNat d) = d := by
  interval_cases d <;> native_decide

theorem boolFourValue_degreeBitsUpper_eq (g : BitVec 78) (u : Nat) :
    boolFourValue (degreeBitsUpper (n := 13) g u) = degreeUpperNat (n := 13) g u := by
  unfold degreeUpperNat degreeBitsUpper
  have folded := (WOWII217ClosureSemantics.boolFourValue_foldl_increment
    (fun v => adjUpper (n := 13) g u) (List.range 13)
      { b0 := false, b1 := false, b2 := false, b3 := false })
  simpa [boolFourValue] using folded (by decide)

-- prove one extracted fixed degree fact converts to nat degree
example (g : BitVec 78)
    (h : fixedDegreeSequenceUpper (n := 13) g
      [6, 6, 6, 6, 6, 6, 6, 5, 5, 5, 5, 5, 5] = true) :
    degreeUpperNat (n := 13) g 0 = 6 := by
  have h' := h
  norm_num [fixedDegreeSequenceUpper, matchesDegreesFromUpper] at h'
  have h0 : (degreeBitsUpper (n := 13) g 0).same (BoolFour.ofNat 6) = true := h'.1
  have hEq : degreeBitsUpper (n := 13) g 0 = BoolFour.ofNat 6 := (boolFourSame_eq_true_iff _ _).1 h0
  have hbits : boolFourValue (degreeBitsUpper (n := 13) g 0) = 6 := by
    simpa [hEq, boolFourValue_ofNat_of_lt_sixteen 6 (by decide)] using congrArg boolFourValue hEq
  simpa [boolFourValue_degreeBitsUpper_eq (g := g) (u := 0)] using hbits

