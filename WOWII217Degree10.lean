import WOWII217Encoding10

/-! Degree-sequence semantics for the 210-bit encoding at order 10. -/

namespace WOWII217Degree10

open SimpleGraph
open Finset
open WOWII217FiniteBase WOWII217Closure WOWII217ClosureSemantics
open WOWII217Encoding10

theorem degree_graphOfUpper_eq10 (g : BitVec 45) (u : Fin 10) :
    (graphOfUpper (n := 10) g).degree u = degreeUpperNat (n := 10) g u := by
  let valEmbedding : Fin 10 ↪ Nat := ⟨Fin.val, Fin.val_injective⟩
  have neighborMap :
      ((graphOfUpper (n := 10) g).neighborFinset u).map valEmbedding =
        (Finset.range 10).filter fun v => adjUpper (n := 10) g u v = true := by
    ext v
    simp [valEmbedding, graphOfUpper]
    constructor
    · rintro ⟨a, adjacent, rfl⟩
      exact ⟨a.isLt, adjacent⟩
    · rintro ⟨hv, adjacent⟩
      exact ⟨⟨v, hv⟩, adjacent, rfl⟩
  have countRange := foldl_bool_count
    (fun v => adjUpper (n := 10) g u v)
    (List.range 10) (List.nodup_range : (List.range 10).Nodup) 0
  rw [Nat.zero_add] at countRange
  have rangeToFinset : (List.range 10).toFinset = Finset.range 10 := by
    ext v; simp
  rw [rangeToFinset] at countRange
  have countRange' :
      (List.range 10).foldl
          (fun count v => count + if adjUpper (n := 10) g u v then 1 else 0) 0 =
        #((Finset.range 10).filter fun v => adjUpper (n := 10) g u v = true) := by
    simpa using countRange
  calc
    (graphOfUpper (n := 10) g).degree u =
        #((graphOfUpper (n := 10) g).neighborFinset u) := rfl
    _ = #(((graphOfUpper (n := 10) g).neighborFinset u).map valEmbedding) := by simp
    _ = #((Finset.range 10).filter fun v => adjUpper (n := 10) g u v = true) :=
      congrArg Finset.card neighborMap
    _ = degreeUpperNat (n := 10) g u := by
      rw [← countRange']
      rfl

theorem boolFourValue_injective10 : Function.Injective boolFourValue := by
  intro x y valueEq
  rcases x with ⟨x0, x1, x2, x3⟩
  rcases y with ⟨y0, y1, y2, y3⟩
  fin_cases x0 <;> fin_cases x1 <;> fin_cases x2 <;> fin_cases x3 <;>
    fin_cases y0 <;> fin_cases y1 <;> fin_cases y2 <;> fin_cases y3 <;>
    simp [boolFourValue] at valueEq ⊢ <;> omega

theorem boolFourValue_ofNat_of_lt_sixteen10 (d : Nat) (hd : d < 16) :
    boolFourValue (BoolFour.ofNat d) = d := by
  interval_cases d <;> native_decide

theorem degreeBitsUpper_same_of_degree_eq10 (g : BitVec 45) (u d : Nat)
    (hd : d < 16) (degreeEq : degreeUpperNat (n := 10) g u = d) :
    (degreeBitsUpper (n := 10) g u).same (BoolFour.ofNat d) = true := by
  apply (boolFourSame_eq_true_iff _ _).mpr
  apply boolFourValue_injective10
  rw [boolFourValue_degreeBitsUpper_eq (n := 10) (by decide), degreeEq,
    boolFourValue_ofNat_of_lt_sixteen10 d hd]

theorem degreeUpperNat_encodeUpper10_eq (G : SimpleGraph (Fin 10))
    [DecidableRel G.Adj] (u : Fin 10) :
    degreeUpperNat (n := 10) (encodeUpper10 G) u = G.degree u := by
  let iso : graphOfUpper (n := 10) (encodeUpper10 G) ≃g G :=
    { toEquiv := Equiv.refl _
      map_rel_iff' := by
        intro x y
        rw [graphOfUpper_encodeUpper10]
        simp }
  calc
    degreeUpperNat (n := 10) (encodeUpper10 G) u =
        (graphOfUpper (n := 10) (encodeUpper10 G)).degree u :=
      (degree_graphOfUpper_eq10 (encodeUpper10 G) u).symm
    _ = G.degree u := (iso.degree_eq u).symm

theorem degreeBitsUpper_encodeUpper10_same (G : SimpleGraph (Fin 10))
    [DecidableRel G.Adj] (u : Fin 10) (d : Nat) (hd : d < 16)
    (degreeEq : G.degree u = d) :
    (degreeBitsUpper (n := 10) (encodeUpper10 G) u).same
      (BoolFour.ofNat d) = true := by
  apply degreeBitsUpper_same_of_degree_eq10 (encodeUpper10 G) u d hd
  rw [degreeUpperNat_encodeUpper10_eq, degreeEq]

theorem fixedDegreeSequenceUpper_encodeUpper10_of_fourRegular
    (G : SimpleGraph (Fin 10)) [DecidableRel G.Adj]
    (fourRegular : ∀ v : Fin 10, G.degree v = 4) :
    fixedDegreeSequenceUpper (n := 10) (encodeUpper10 G)
      [4, 4, 4, 4, 4, 4, 4, 4, 4, 4] = true := by
  have match0 := degreeBitsUpper_encodeUpper10_same G 0 4 (by decide) (fourRegular 0)
  have match1 := degreeBitsUpper_encodeUpper10_same G 1 4 (by decide) (fourRegular 1)
  have match2 := degreeBitsUpper_encodeUpper10_same G 2 4 (by decide) (fourRegular 2)
  have match3 := degreeBitsUpper_encodeUpper10_same G 3 4 (by decide) (fourRegular 3)
  have match4 := degreeBitsUpper_encodeUpper10_same G 4 4 (by decide) (fourRegular 4)
  have match5 := degreeBitsUpper_encodeUpper10_same G 5 4 (by decide) (fourRegular 5)
  have match6 := degreeBitsUpper_encodeUpper10_same G 6 4 (by decide) (fourRegular 6)
  have match7 := degreeBitsUpper_encodeUpper10_same G 7 4 (by decide) (fourRegular 7)
  have match8 := degreeBitsUpper_encodeUpper10_same G 8 4 (by decide) (fourRegular 8)
  have match9 := degreeBitsUpper_encodeUpper10_same G 9 4 (by decide) (fourRegular 9)
  norm_num [fixedDegreeSequenceUpper, matchesDegreesFromUpper]
  exact ⟨match0, match1, match2, match3, match4, match5, match6, match7, match8, match9⟩

end WOWII217Degree10
