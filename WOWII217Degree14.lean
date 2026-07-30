import WOWII217Encoding
import WOWII217DP
import WOWII217Semantics
import WOWII217Closure
import WOWII217ClosureSemantics
import WOWII217FiniteBase

/-! Degree-sequence semantics for the 91-bit encoding at order 14.

Proves the `WOWII217DP.fixedDegreeSequenceUpper` certificate (the predicate
consumed by `WOWII217Relabel`) for six-regular `Fin 14` graphs.
-/

namespace WOWII217Degree14

open SimpleGraph Finset
open WOWII217Encoding
open WOWII217ClosureSemantics
open WOWII217FiniteBase (BoolFour degreeBitsUpper fixedDegreeSequenceUpper
  matchesDegreesFromUpper maskHas)

theorem degree_graphOfUpper_eq14_current (g : BitVec 91) (u : Fin 14) :
    (WOWII217Semantics.graphOfUpper14 g).degree u =
      WOWII217Closure.degreeUpperNat (n := 14) g u := by
  let valEmbedding : Fin 14 ↪ Nat := ⟨Fin.val, Fin.val_injective⟩
  have neighborMap :
      ((WOWII217Semantics.graphOfUpper14 g).neighborFinset u).map valEmbedding =
        (Finset.range 14).filter fun v =>
          WOWII217Semantics.adjUpper (n := 14) g u v = true := by
    ext v
    simp [valEmbedding, WOWII217Semantics.graphOfUpper14]
    constructor
    · rintro ⟨a, adjacent, rfl⟩
      exact ⟨a.isLt, adjacent⟩
    · rintro ⟨hv, adjacent⟩
      exact ⟨⟨v, hv⟩, adjacent, rfl⟩
  have countRange := foldl_bool_count
    (fun v => WOWII217Semantics.adjUpper (n := 14) g u v)
    (List.range 14) (List.nodup_range : (List.range 14).Nodup) 0
  rw [Nat.zero_add] at countRange
  have rangeToFinset : (List.range 14).toFinset = Finset.range 14 := by
    ext v
    simp
  rw [rangeToFinset] at countRange
  have countRange' :
      (List.range 14).foldl
          (fun count v =>
            count + if WOWII217Semantics.adjUpper (n := 14) g u v then 1 else 0) 0 =
        #((Finset.range 14).filter fun v =>
          WOWII217Semantics.adjUpper (n := 14) g u v = true) := by
    simpa using countRange
  have hadj (v : Nat) :
      WOWII217Semantics.adjUpper (n := 14) g u v =
        WOWII217FiniteBase.adjUpper (n := 14) g u v := rfl
  calc
    (WOWII217Semantics.graphOfUpper14 g).degree u =
        #((WOWII217Semantics.graphOfUpper14 g).neighborFinset u) := rfl
    _ = #(((WOWII217Semantics.graphOfUpper14 g).neighborFinset u).map
          valEmbedding) := by simp
    _ = #((Finset.range 14).filter fun v =>
          WOWII217Semantics.adjUpper (n := 14) g u v = true) :=
      congrArg Finset.card neighborMap
    _ = WOWII217Closure.degreeUpperNat (n := 14) g u := by
      rw [← countRange']
      simp only [WOWII217Closure.degreeUpperNat, hadj]

theorem boolFourValue_injective14 : Function.Injective boolFourValue := by
  intro x y valueEq
  rcases x with ⟨x0, x1, x2, x3⟩
  rcases y with ⟨y0, y1, y2, y3⟩
  fin_cases x0 <;> fin_cases x1 <;> fin_cases x2 <;> fin_cases x3 <;>
    fin_cases y0 <;> fin_cases y1 <;> fin_cases y2 <;> fin_cases y3 <;>
    simp [boolFourValue] at valueEq ⊢ <;> omega

theorem boolFourValue_ofNat_of_lt_sixteen14 (d : Nat) (hd : d < 16) :
    boolFourValue (BoolFour.ofNat d) = d := by
  interval_cases d <;> decide

theorem degreeBitsUpper_same_of_degree_eq14 (g : BitVec 91) (u d : Nat)
    (hd : d < 16)
    (degreeEq : WOWII217Closure.degreeUpperNat (n := 14) g u = d) :
    (degreeBitsUpper (n := 14) g u).same (BoolFour.ofNat d) = true := by
  apply (boolFourSame_eq_true_iff _ _).mpr
  apply boolFourValue_injective14
  rw [boolFourValue_degreeBitsUpper_eq (n := 14) (by decide), degreeEq,
    boolFourValue_ofNat_of_lt_sixteen14 d hd]

theorem degreeUpperNat_encodeUpper14_eq (G : SimpleGraph (Fin 14))
    [DecidableRel G.Adj] (u : Fin 14) :
    WOWII217Closure.degreeUpperNat (n := 14) (encodeUpper14 G) u =
      G.degree u := by
  let iso : WOWII217Semantics.graphOfUpper14 (encodeUpper14 G) ≃g G :=
    { toEquiv := Equiv.refl _
      map_rel_iff' := by
        intro x y
        rw [graphOfUpper14_encodeUpper14]
        simp }
  calc
    WOWII217Closure.degreeUpperNat (n := 14) (encodeUpper14 G) u =
        (WOWII217Semantics.graphOfUpper14 (encodeUpper14 G)).degree u :=
      (degree_graphOfUpper_eq14_current (encodeUpper14 G) u).symm
    _ = G.degree u := (iso.degree_eq u).symm

theorem degreeBitsUpper_encodeUpper14_same (G : SimpleGraph (Fin 14))
    [DecidableRel G.Adj] (u : Fin 14) (d : Nat) (hd : d < 16)
    (degreeEq : G.degree u = d) :
    (degreeBitsUpper (n := 14) (encodeUpper14 G) u).same
      (BoolFour.ofNat d) = true := by
  apply degreeBitsUpper_same_of_degree_eq14 (encodeUpper14 G) u d hd
  rw [degreeUpperNat_encodeUpper14_eq, degreeEq]

/-- FiniteBase form (proved); equal to the DP certificate by `rfl`. -/
theorem fixedDegreeSequenceUpper_encodeUpper14_of_sixRegular_finiteBase
    (G : SimpleGraph (Fin 14)) [DecidableRel G.Adj]
    (sixRegular : ∀ v : Fin 14, G.degree v = 6) :
    fixedDegreeSequenceUpper (n := 14) (encodeUpper14 G)
      [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] = true := by
  have match0 := degreeBitsUpper_encodeUpper14_same G 0 6 (by decide) (sixRegular 0)
  have match1 := degreeBitsUpper_encodeUpper14_same G 1 6 (by decide) (sixRegular 1)
  have match2 := degreeBitsUpper_encodeUpper14_same G 2 6 (by decide) (sixRegular 2)
  have match3 := degreeBitsUpper_encodeUpper14_same G 3 6 (by decide) (sixRegular 3)
  have match4 := degreeBitsUpper_encodeUpper14_same G 4 6 (by decide) (sixRegular 4)
  have match5 := degreeBitsUpper_encodeUpper14_same G 5 6 (by decide) (sixRegular 5)
  have match6 := degreeBitsUpper_encodeUpper14_same G 6 6 (by decide) (sixRegular 6)
  have match7 := degreeBitsUpper_encodeUpper14_same G 7 6 (by decide) (sixRegular 7)
  have match8 := degreeBitsUpper_encodeUpper14_same G 8 6 (by decide) (sixRegular 8)
  have match9 := degreeBitsUpper_encodeUpper14_same G 9 6 (by decide) (sixRegular 9)
  have match10 := degreeBitsUpper_encodeUpper14_same G 10 6 (by decide) (sixRegular 10)
  have match11 := degreeBitsUpper_encodeUpper14_same G 11 6 (by decide) (sixRegular 11)
  have match12 := degreeBitsUpper_encodeUpper14_same G 12 6 (by decide) (sixRegular 12)
  have match13 := degreeBitsUpper_encodeUpper14_same G 13 6 (by decide) (sixRegular 13)
  norm_num [fixedDegreeSequenceUpper, matchesDegreesFromUpper]
  refine And.intro ?_ (And.intro ?_ (And.intro ?_ (And.intro ?_
    (And.intro ?_ (And.intro ?_ (And.intro ?_ (And.intro ?_
    (And.intro ?_ (And.intro ?_ (And.intro ?_ (And.intro ?_
    (And.intro ?_ ?_))))))))))))
  · simpa using match0
  · simpa using match1
  · simpa using match2
  · simpa using match3
  · simpa using match4
  · simpa using match5
  · simpa using match6
  · simpa using match7
  · simpa using match8
  · simpa using match9
  · simpa using match10
  · simpa using match11
  · simpa using match12
  · simpa using match13

/-- DP certificate form required by `WOWII217Relabel`. -/
theorem fixedDegreeSequenceUpper_encodeUpper14_of_sixRegular
    (G : SimpleGraph (Fin 14)) [DecidableRel G.Adj]
    (sixRegular : ∀ v : Fin 14, G.degree v = 6) :
    WOWII217DP.fixedDegreeSequenceUpper (n := 14) (encodeUpper14 G)
      [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] = true := by
  have h :=
    fixedDegreeSequenceUpper_encodeUpper14_of_sixRegular_finiteBase G sixRegular
  -- DP and FiniteBase implement the same Boolean predicate.
  have hEq :
      WOWII217DP.fixedDegreeSequenceUpper (n := 14) (encodeUpper14 G)
          [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] =
        fixedDegreeSequenceUpper (n := 14) (encodeUpper14 G)
          [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] :=
    rfl
  rwa [hEq]


theorem fixedDegreeSequenceUpper_encodeUpper14_of_degreeSequence
    (G : SimpleGraph (Fin 14)) [DecidableRel G.Adj] (s : List Nat)
    (hSeq : List.ofFn (fun v : Fin 14 => G.degree v) = s) :
    fixedDegreeSequenceUpper (n := 14) (encodeUpper14 G) s = true := by
  subst hSeq
  simp [fixedDegreeSequenceUpper, matchesDegreesFromUpper]
  have hlt16 : ∀ v : Fin 14, G.degree v < 16 := by
    intro v
    have hdeg := G.degree_lt_card_verts v
    exact lt_of_lt_of_le hdeg (by decide)
  refine ⟨
    degreeBitsUpper_encodeUpper14_same G 0 (G.degree 0) (hlt16 0) rfl,
    degreeBitsUpper_encodeUpper14_same G 1 (G.degree 1) (hlt16 1) rfl,
    degreeBitsUpper_encodeUpper14_same G 2 (G.degree 2) (hlt16 2) rfl,
    degreeBitsUpper_encodeUpper14_same G 3 (G.degree 3) (hlt16 3) rfl,
    degreeBitsUpper_encodeUpper14_same G 4 (G.degree 4) (hlt16 4) rfl,
    degreeBitsUpper_encodeUpper14_same G 5 (G.degree 5) (hlt16 5) rfl,
    degreeBitsUpper_encodeUpper14_same G 6 (G.degree 6) (hlt16 6) rfl,
    degreeBitsUpper_encodeUpper14_same G 7 (G.degree 7) (hlt16 7) rfl,
    degreeBitsUpper_encodeUpper14_same G 8 (G.degree 8) (hlt16 8) rfl,
    degreeBitsUpper_encodeUpper14_same G 9 (G.degree 9) (hlt16 9) rfl,
    degreeBitsUpper_encodeUpper14_same G 10 (G.degree 10) (hlt16 10) rfl,
    degreeBitsUpper_encodeUpper14_same G 11 (G.degree 11) (hlt16 11) rfl,
    degreeBitsUpper_encodeUpper14_same G 12 (G.degree 12) (hlt16 12) rfl,
    degreeBitsUpper_encodeUpper14_same G 13 (G.degree 13) (hlt16 13) rfl
  ⟩

end WOWII217Degree14
