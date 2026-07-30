import WOWII217Encoding8

/-! Degree-sequence semantics for the 28-bit encoding at order 8. -/

namespace WOWII217Degree8

open SimpleGraph
open Finset
open WOWII217FiniteBase WOWII217Closure WOWII217ClosureSemantics
open WOWII217Encoding8

theorem degree_graphOfUpper_eq8 (g : BitVec 28) (u : Fin 8) :
    (graphOfUpper (n := 8) g).degree u = degreeUpperNat (n := 8) g u := by
  let valEmbedding : Fin 8 ↪ Nat := ⟨Fin.val, Fin.val_injective⟩
  have neighborMap :
      ((graphOfUpper (n := 8) g).neighborFinset u).map valEmbedding =
        (Finset.range 8).filter fun v => adjUpper (n := 8) g u v = true := by
    ext v
    simp [valEmbedding, graphOfUpper]
    constructor
    · rintro ⟨a, adjacent, rfl⟩
      exact ⟨a.isLt, adjacent⟩
    · rintro ⟨hv, adjacent⟩
      exact ⟨⟨v, hv⟩, adjacent, rfl⟩
  have countRange := foldl_bool_count
    (fun v => adjUpper (n := 8) g u v)
    (List.range 8) (List.nodup_range : (List.range 8).Nodup) 0
  rw [Nat.zero_add] at countRange
  have rangeToFinset : (List.range 8).toFinset = Finset.range 8 := by
    ext v; simp
  rw [rangeToFinset] at countRange
  have countRange' :
      (List.range 8).foldl
          (fun count v => count + if adjUpper (n := 8) g u v then 1 else 0) 0 =
        #((Finset.range 8).filter fun v => adjUpper (n := 8) g u v = true) := by
    simpa using countRange
  calc
    (graphOfUpper (n := 8) g).degree u =
        #((graphOfUpper (n := 8) g).neighborFinset u) := rfl
    _ = #(((graphOfUpper (n := 8) g).neighborFinset u).map valEmbedding) := by simp
    _ = #((Finset.range 8).filter fun v => adjUpper (n := 8) g u v = true) :=
      congrArg Finset.card neighborMap
    _ = degreeUpperNat (n := 8) g u := by
      rw [← countRange']
      rfl

theorem boolFourValue_injective8 : Function.Injective boolFourValue := by
  intro x y valueEq
  rcases x with ⟨x0, x1, x2, x3⟩
  rcases y with ⟨y0, y1, y2, y3⟩
  fin_cases x0 <;> fin_cases x1 <;> fin_cases x2 <;> fin_cases x3 <;>
    fin_cases y0 <;> fin_cases y1 <;> fin_cases y2 <;> fin_cases y3 <;>
    simp [boolFourValue] at valueEq ⊢ <;> omega

theorem boolFourValue_ofNat_of_lt_sixteen8 (d : Nat) (hd : d < 16) :
    boolFourValue (BoolFour.ofNat d) = d := by
  interval_cases d <;> decide

theorem degreeBitsUpper_same_of_degree_eq8 (g : BitVec 28) (u d : Nat)
    (hd : d < 16) (degreeEq : degreeUpperNat (n := 8) g u = d) :
    (degreeBitsUpper (n := 8) g u).same (BoolFour.ofNat d) = true := by
  apply (boolFourSame_eq_true_iff _ _).mpr
  apply boolFourValue_injective8
  rw [boolFourValue_degreeBitsUpper_eq (n := 8) (by decide), degreeEq,
    boolFourValue_ofNat_of_lt_sixteen8 d hd]

theorem degreeUpperNat_encodeUpper8_eq (G : SimpleGraph (Fin 8))
    [DecidableRel G.Adj] (u : Fin 8) :
    degreeUpperNat (n := 8) (encodeUpper8 G) u = G.degree u := by
  let iso : graphOfUpper (n := 8) (encodeUpper8 G) ≃g G :=
    { toEquiv := Equiv.refl _
      map_rel_iff' := by
        intro x y
        rw [graphOfUpper_encodeUpper8]
        simp }
  calc
    degreeUpperNat (n := 8) (encodeUpper8 G) u =
        (graphOfUpper (n := 8) (encodeUpper8 G)).degree u :=
      (degree_graphOfUpper_eq8 (encodeUpper8 G) u).symm
    _ = G.degree u := (iso.degree_eq u).symm

theorem degreeBitsUpper_encodeUpper8_same (G : SimpleGraph (Fin 8))
    [DecidableRel G.Adj] (u : Fin 8) (d : Nat) (hd : d < 16)
    (degreeEq : G.degree u = d) :
    (degreeBitsUpper (n := 8) (encodeUpper8 G) u).same
      (BoolFour.ofNat d) = true := by
  apply degreeBitsUpper_same_of_degree_eq8 (encodeUpper8 G) u d hd
  rw [degreeUpperNat_encodeUpper8_eq, degreeEq]

theorem fixedDegreeSequenceUpper_encodeUpper8_of_threeRegular
    (G : SimpleGraph (Fin 8)) [DecidableRel G.Adj]
    (threeRegular : ∀ v : Fin 8, G.degree v = 3) :
    fixedDegreeSequenceUpper (n := 8) (encodeUpper8 G)
      [3, 3, 3, 3, 3, 3, 3, 3] = true := by
  have match0 := degreeBitsUpper_encodeUpper8_same G 0 3 (by decide) (threeRegular 0)
  have match1 := degreeBitsUpper_encodeUpper8_same G 1 3 (by decide) (threeRegular 1)
  have match2 := degreeBitsUpper_encodeUpper8_same G 2 3 (by decide) (threeRegular 2)
  have match3 := degreeBitsUpper_encodeUpper8_same G 3 3 (by decide) (threeRegular 3)
  have match4 := degreeBitsUpper_encodeUpper8_same G 4 3 (by decide) (threeRegular 4)
  have match5 := degreeBitsUpper_encodeUpper8_same G 5 3 (by decide) (threeRegular 5)
  have match6 := degreeBitsUpper_encodeUpper8_same G 6 3 (by decide) (threeRegular 6)
  have match7 := degreeBitsUpper_encodeUpper8_same G 7 3 (by decide) (threeRegular 7)
  norm_num [fixedDegreeSequenceUpper, matchesDegreesFromUpper]
  exact ⟨match0, match1, match2, match3, match4, match5, match6, match7⟩


theorem fixedDegreeSequenceUpper_encodeUpper8_of_degreeSequence
    (G : SimpleGraph (Fin 8)) [DecidableRel G.Adj] (s : List Nat)
    (hSeq : List.ofFn (fun v : Fin 8 => G.degree v) = s) :
    fixedDegreeSequenceUpper (n := 8) (encodeUpper8 G) s = true := by
  subst hSeq
  simp [fixedDegreeSequenceUpper, matchesDegreesFromUpper]
  have hlt16 : ∀ v : Fin 8, G.degree v < 16 := by
    intro v
    have hdeg := G.degree_lt_card_verts v
    exact lt_of_lt_of_le hdeg (by decide)
  refine ⟨
    degreeBitsUpper_encodeUpper8_same G 0 (G.degree 0) (hlt16 0) rfl,
    degreeBitsUpper_encodeUpper8_same G 1 (G.degree 1) (hlt16 1) rfl,
    degreeBitsUpper_encodeUpper8_same G 2 (G.degree 2) (hlt16 2) rfl,
    degreeBitsUpper_encodeUpper8_same G 3 (G.degree 3) (hlt16 3) rfl,
    degreeBitsUpper_encodeUpper8_same G 4 (G.degree 4) (hlt16 4) rfl,
    degreeBitsUpper_encodeUpper8_same G 5 (G.degree 5) (hlt16 5) rfl,
    degreeBitsUpper_encodeUpper8_same G 6 (G.degree 6) (hlt16 6) rfl,
    degreeBitsUpper_encodeUpper8_same G 7 (G.degree 7) (hlt16 7) rfl
  ⟩

end WOWII217Degree8
