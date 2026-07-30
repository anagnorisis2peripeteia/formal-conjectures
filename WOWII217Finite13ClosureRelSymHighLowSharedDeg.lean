import WOWII217Closure13Fast
import WOWII217Finite13
import WOWII217Finite13ClosureRel
import WOWII217Finite13ClosureRelSymHighLow
import WOWII217DegreePairBridge

/-!
Shared-degree bridge → relational residual certificate.
-/

namespace WOWII217Finite13ClosureRelSymHighLowSharedDeg

open WOWII217FiniteBase WOWII217Closure WOWII217Closure13Fast WOWII217Finite13
open WOWII217Finite13ClosureRel
open WOWII217DegreePairBridge

def degreeTableAt13 (degrees : BitVec 52) (v : Nat) : BoolFour :=
  { b0 := degrees.getLsbD (4 * v),
    b1 := degrees.getLsbD (4 * v + 1),
    b2 := degrees.getLsbD (4 * v + 2),
    b3 := degrees.getLsbD (4 * v + 3) }

def degreeTableConsistent13 (g : BitVec 78) (degrees : BitVec 52) : Bool :=
  (List.range 13).all fun v =>
    (degreeBitsUpper (n := 13) g v).same (degreeTableAt13 degrees v)

def majority (a b c : Bool) : Bool :=
  (a && b) || (a && c) || (b && c)

def boolFourSumAtLeast12 (x y : BoolFour) : Bool :=
  let c1 := x.b0 && y.b0
  let c2 := majority x.b1 y.b1 c1
  let s2 := x.b2 ^^ y.b2 ^^ c2
  let c3 := majority x.b2 y.b2 c2
  let s3 := x.b3 ^^ y.b3 ^^ c3
  let c4 := majority x.b3 y.b3 c3
  c4 || (s3 && s2)

def boolFourValue (x : BoolFour) : Nat :=
  (if x.b0 then 1 else 0) +
    2 * (if x.b1 then 1 else 0) +
    4 * (if x.b2 then 1 else 0) +
    8 * (if x.b3 then 1 else 0)

abbrev hasHighLowEdge13 := WOWII217Finite13ClosureRel.hasHighLowEdge13
abbrev pathClosureParallelRel13_relational :=
  WOWII217Finite13ClosureRel.pathClosureParallelRel13

def pathClosureParallelRel13 (g next : BitVec 78) (degrees : BitVec 52) : Bool :=
  (upperPairs 13).all fun edge =>
    let u := edge.1
    let v := edge.2
    !(adjUpper (n := 13) next u v ^^
      (adjUpper (n := 13) g u v ||
        boolFourSumAtLeast12 (degreeTableAt13 degrees u)
          (degreeTableAt13 degrees v)))

theorem boolFourSumAtLeast12_iff (x y : BoolFour) :
    boolFourSumAtLeast12 x y = true ↔
      12 ≤ boolFourValue x + boolFourValue y := by
  rcases x with ⟨x0, x1, x2, x3⟩
  rcases y with ⟨y0, y1, y2, y3⟩
  fin_cases x0 <;> fin_cases x1 <;> fin_cases x2 <;> fin_cases x3 <;>
    fin_cases y0 <;> fin_cases y1 <;> fin_cases y2 <;> fin_cases y3 <;>
    decide

theorem boolFour_same_eq_true_iff (x y : BoolFour) :
    x.same y = true ↔ x = y := by
  rcases x with ⟨x0, x1, x2, x3⟩
  rcases y with ⟨y0, y1, y2, y3⟩
  fin_cases x0 <;> fin_cases x1 <;> fin_cases x2 <;> fin_cases x3 <;>
    fin_cases y0 <;> fin_cases y1 <;> fin_cases y2 <;> fin_cases y3 <;>
    simp [BoolFour.same]

theorem degreeTableAt13_eq_of_consistent (g : BitVec 78) (degrees : BitVec 52)
    (consistent : degreeTableConsistent13 g degrees = true) (v : Nat) (hv : v < 13) :
    degreeTableAt13 degrees v = degreeBitsUpper (n := 13) g v := by
  have hAll :
      ∀ w ∈ List.range 13,
        (degreeBitsUpper (n := 13) g w).same (degreeTableAt13 degrees w) = true := by
    exact (List.all_eq_true.mp consistent)
  exact
    ((boolFour_same_eq_true_iff
        (degreeBitsUpper (n := 13) g v) (degreeTableAt13 degrees v)).1
      (hAll v (List.mem_range.mpr hv))).symm

theorem boolFourValue_increment_of_lt_fifteen (x : BoolFour) (b : Bool)
    (hx : boolFourValue x < 15) :
    boolFourValue (x.increment b) =
      boolFourValue x + if b then 1 else 0 := by
  rcases x with ⟨b0, b1, b2, b3⟩
  fin_cases b0 <;> fin_cases b1 <;> fin_cases b2 <;> fin_cases b3 <;>
    fin_cases b <;> simp [boolFourValue, BoolFour.increment] at hx ⊢

theorem boolFourValue_foldl_increment {α : Type*} (f : α → Bool) :
    ∀ (xs : List α) (initial : BoolFour),
      boolFourValue initial + xs.length < 16 →
      boolFourValue (xs.foldl (fun bits x => bits.increment (f x)) initial) =
        xs.foldl (fun count x => count + if f x then 1 else 0)
          (boolFourValue initial) := by
  intro xs
  induction xs with
  | nil => intro initial _; simp
  | cons x xs ih =>
      intro initial bound
      have hlen : (x :: xs).length = xs.length + 1 := rfl
      have hlt : boolFourValue initial < 15 := by
        have hb : boolFourValue initial + (xs.length + 1) < 16 := by
          simpa [hlen] using bound
        omega
      have hinc := boolFourValue_increment_of_lt_fifteen initial (f x) hlt
      have hnext_bound :
          boolFourValue (initial.increment (f x)) + xs.length < 16 := by
        have hb : boolFourValue initial + (xs.length + 1) < 16 := by
          simpa [hlen] using bound
        have hbit : (if f x then 1 else 0) ≤ 1 := by split <;> simp
        omega
      have hnext := ih (initial.increment (f x)) hnext_bound
      simp only [List.foldl_cons]
      rw [hnext, hinc]

theorem boolFourValue_degreeBitsUpper_eq {n : Nat} (hn : n < 16)
    (g : BitVec (edgeCount n)) (u : Nat) :
    boolFourValue (degreeBitsUpper g u) = degreeUpperNat g u := by
  unfold degreeBitsUpper degreeUpperNat
  have folded := boolFourValue_foldl_increment
    (fun v => adjUpper g u v) (List.range n)
      { b0 := false, b1 := false, b2 := false, b3 := false }
  simpa [boolFourValue] using folded (by
    have : boolFourValue ⟨false, false, false, false⟩ = 0 := by native_decide
    simpa [this, List.length_range] using hn)

theorem bool_eq_decide {b : Bool} {P : Prop} [Decidable P] :
    (b = true ↔ P) → b = decide P := by
  intro hiff
  by_cases h : decide P = true
  · have hP : P := by simpa [decide_eq_true_eq] using h
    have hb : b = true := hiff.mpr hP
    simp [h, hb]
  · have hP : ¬ P := by
      intro hPt
      exact h (by simpa [decide_eq_true_eq] using hPt)
    have hbne : b ≠ true := by
      intro hb
      exact hP (hiff.mp hb)
    have hb : b = false := by
      cases b <;> simp at hbne ⊢
    simp [h, hb]

theorem boolFourSumAtLeast12_eq_decide (x y : BoolFour) :
    boolFourSumAtLeast12 x y =
      decide (12 ≤ boolFourValue x + boolFourValue y) := by
  exact bool_eq_decide (b := boolFourSumAtLeast12 x y)
    (P := 12 ≤ boolFourValue x + boolFourValue y)
    (boolFourSumAtLeast12_iff x y)

theorem mem_upperPairs_iff {n u v : Nat} :
    (u, v) ∈ upperPairs n ↔ v < n ∧ u < v := by
  simp [upperPairs]

theorem pathClosureParallelRel13_to_relational
    (g next : BitVec 78) (d : BitVec 52) (hConsistent : degreeTableConsistent13 g d = true) :
    pathClosureParallelRel13 g next d = true →
    pathClosureParallelRel13_relational g next = true := by
  intro h
  dsimp only [pathClosureParallelRel13, pathClosureParallelRel13_relational] at h ⊢
  refine (List.all_eq_true).2 ?_
  intro edge hEdge
  have hAll := (List.all_eq_true).1 h
  have hEdge' : edge.2 < 13 ∧ edge.1 < edge.2 := (mem_upperPairs_iff.mp hEdge)
  have hU : degreeTableAt13 d edge.1 = degreeBitsUpper (n := 13) g edge.1 :=
    degreeTableAt13_eq_of_consistent g d hConsistent edge.1
      (Nat.lt_trans hEdge'.2 hEdge'.1)
  have hV : degreeTableAt13 d edge.2 = degreeBitsUpper (n := 13) g edge.2 :=
    degreeTableAt13_eq_of_consistent g d hConsistent edge.2 hEdge'.1
  have hThresh :
      boolFourSumAtLeast12 (degreeTableAt13 d edge.1) (degreeTableAt13 d edge.2) =
        degreePairAtLeast12Upper13 g edge.1 edge.2 := by
    rw [hU, hV]
    have h1 := boolFourSumAtLeast12_eq_decide
      (degreeBitsUpper (n := 13) g edge.1) (degreeBitsUpper (n := 13) g edge.2)
    have h2 := degreePairAtLeast12Upper13_eq_decide g edge.1 edge.2
    have hVu := boolFourValue_degreeBitsUpper_eq (n := 13) (by decide) g edge.1
    have hVv := boolFourValue_degreeBitsUpper_eq (n := 13) (by decide) g edge.2
    simp [h1, h2, hVu, hVv]
  simpa [hThresh] using hAll edge hEdge

theorem crossEdge_degreeSequence_6666666555555_relational_closure_sym
    (g g1 g2 g3 g4 : BitVec 78) :
    hasHighLowEdge13 g = true →
    fixedDegreeSequenceUpper (n := 13) g
      [6, 6, 6, 6, 6, 6, 6, 5, 5, 5, 5, 5, 5] = true →
    pathClosureParallelRel13_relational g g1 = true →
    pathClosureParallelRel13_relational g1 g2 = true →
    pathClosureParallelRel13_relational g2 g3 = true →
    pathClosureParallelRel13_relational g3 g4 = true →
    completeUpper (n := 13) g4 = true :=
  WOWII217Finite13ClosureRelSymHighLow.crossEdge_degreeSequence_6666666555555_relational_closure_sym
    g g1 g2 g3 g4

theorem crossEdge_degreeSequence_6666666555555_relational_closure_sym_shared :
    ∀ (g g1 g2 g3 g4 : BitVec 78) (d d1 d2 d3 : BitVec 52),
      hasHighLowEdge13 g = true →
      fixedDegreeSequenceUpper (n := 13) g
        [6, 6, 6, 6, 6, 6, 6, 5, 5, 5, 5, 5, 5] = true →
      degreeTableConsistent13 g d = true →
      pathClosureParallelRel13 g g1 d = true →
      degreeTableConsistent13 g1 d1 = true →
      pathClosureParallelRel13 g1 g2 d1 = true →
      degreeTableConsistent13 g2 d2 = true →
      pathClosureParallelRel13 g2 g3 d2 = true →
      degreeTableConsistent13 g3 d3 = true →
      pathClosureParallelRel13 g3 g4 d3 = true →
      completeUpper (n := 13) g4 = true := by
  intro g g1 g2 g3 g4 d d1 d2 d3 hHigh hDegree hCons0 hRel0 hCons1 hRel1 hCons2 hRel2 hCons3 hRel3
  exact
    crossEdge_degreeSequence_6666666555555_relational_closure_sym
      g g1 g2 g3 g4 hHigh hDegree
      (pathClosureParallelRel13_to_relational g g1 d hCons0 hRel0)
      (pathClosureParallelRel13_to_relational g1 g2 d1 hCons1 hRel1)
      (pathClosureParallelRel13_to_relational g2 g3 d2 hCons2 hRel2)
      (pathClosureParallelRel13_to_relational g3 g4 d3 hCons3 hRel3)

end WOWII217Finite13ClosureRelSymHighLowSharedDeg
