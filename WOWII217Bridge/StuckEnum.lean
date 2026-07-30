import WOWII217ResidueBound

namespace StuckEnum

open SimpleGraph WOWII217ResidueBound List

/-! # `hStuck` admits only the regular sequences

`hStuck : 2 * maxDegree < card V - 1` together with `residue = 2` pins the degree
sequence to the single `k`-regular one for even `n`, and is unsatisfiable for odd `n`.

For a nonincreasing list `s`, `s.headD 0` is the maximum degree, so `hStuck` reads
`2 * s.headD 0 < n - 1`.  Note this already forces `maxDegree ≤ 5` for `n ≤ 12`,
so the `max ≤ 6` enumeration below is not an extra assumption. -/

/-- n = 12: the only stuck residue-2 sequence is `[5]^12`. -/
def stuckLen12 : Bool :=
  forallNoninc 12 6 [] fun s =>
    !decide (residueAux s = 2) || !decide (2 * s.headD 0 < 11) || decide (0 ∈ s) || decide (s.sum % 2 = 1) ||
      decide (s = [5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5])

theorem stuckLen12_eq_true : stuckLen12 = true := by native_decide

/-- n = 11: no stuck residue-2 sequence at all. -/
def stuckLen11 : Bool :=
  forallNoninc 11 6 [] fun s =>
    !decide (residueAux s = 2) || !decide (2 * s.headD 0 < 10) || decide (0 ∈ s) || decide (s.sum % 2 = 1)

theorem stuckLen11_eq_true : stuckLen11 = true := by native_decide

/-- n = 10: only `[4]^10`, which `hNot4` excludes. -/
def stuckLen10 : Bool :=
  forallNoninc 10 6 [] fun s =>
    !decide (residueAux s = 2) || !decide (2 * s.headD 0 < 9) || decide (0 ∈ s) || decide (s.sum % 2 = 1) ||
      decide (s = [4, 4, 4, 4, 4, 4, 4, 4, 4, 4])

theorem stuckLen10_eq_true : stuckLen10 = true := by native_decide

/-- n = 9: none. -/
def stuckLen9 : Bool :=
  forallNoninc 9 6 [] fun s =>
    !decide (residueAux s = 2) || !decide (2 * s.headD 0 < 8) || decide (0 ∈ s) || decide (s.sum % 2 = 1)

theorem stuckLen9_eq_true : stuckLen9 = true := by native_decide

/-- n = 8: only `[3]^8`, which `hNot3` excludes. -/
def stuckLen8 : Bool :=
  forallNoninc 8 6 [] fun s =>
    !decide (residueAux s = 2) || !decide (2 * s.headD 0 < 7) || decide (0 ∈ s) || decide (s.sum % 2 = 1) ||
      decide (s = [3, 3, 3, 3, 3, 3, 3, 3])

theorem stuckLen8_eq_true : stuckLen8 = true := by native_decide

/-- n = 7: none. -/
def stuckLen7 : Bool :=
  forallNoninc 7 6 [] fun s =>
    !decide (residueAux s = 2) || !decide (2 * s.headD 0 < 6) || decide (0 ∈ s) || decide (s.sum % 2 = 1)

theorem stuckLen7_eq_true : stuckLen7 = true := by native_decide

/-- n = 6: only `[2]^6`, which `hNot2` excludes. -/
def stuckLen6 : Bool :=
  forallNoninc 6 6 [] fun s =>
    !decide (residueAux s = 2) || !decide (2 * s.headD 0 < 5) || decide (0 ∈ s) || decide (s.sum % 2 = 1) ||
      decide (s = [2, 2, 2, 2, 2, 2])

theorem stuckLen6_eq_true : stuckLen6 = true := by native_decide

/-- n = 5: none. -/
def stuckLen5 : Bool :=
  forallNoninc 5 6 [] fun s =>
    !decide (residueAux s = 2) || !decide (2 * s.headD 0 < 4) || decide (0 ∈ s) || decide (s.sum % 2 = 1)

theorem stuckLen5_eq_true : stuckLen5 = true := by native_decide

/-- n = 4: only `[1]^4`, a perfect matching, which connectivity excludes. -/
def stuckLen4 : Bool :=
  forallNoninc 4 6 [] fun s =>
    !decide (residueAux s = 2) || !decide (2 * s.headD 0 < 3) || decide (0 ∈ s) || decide (s.sum % 2 = 1) ||
      decide (s = [1, 1, 1, 1])

theorem stuckLen4_eq_true : stuckLen4 = true := by native_decide

end StuckEnum
