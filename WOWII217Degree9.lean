import WOWII217Encoding9

/-! Degree-sequence semantics for the 36-bit encoding at order 9. -/

namespace WOWII217Degree9

open SimpleGraph
open Finset
open WOWII217FiniteBase WOWII217Closure WOWII217ClosureSemantics
open WOWII217Encoding9

theorem degree_graphOfUpper_eq9 (g : BitVec 36) (u : Fin 9) :
    (graphOfUpper (n := 9) g).degree u = degreeUpperNat (n := 9) g u := by
  let valEmbedding : Fin 9 ↪ Nat := ⟨Fin.val, Fin.val_injective⟩
  have neighborMap :
      ((graphOfUpper (n := 9) g).neighborFinset u).map valEmbedding =
        (Finset.range 9).filter fun v => adjUpper (n := 9) g u v = true := by
    ext v
    simp [valEmbedding, graphOfUpper]
    constructor
    · rintro ⟨a, adjacent, rfl⟩
      exact ⟨a.isLt, adjacent⟩
    · rintro ⟨hv, adjacent⟩
      exact ⟨⟨v, hv⟩, adjacent, rfl⟩
  have countRange := foldl_bool_count
    (fun v => adjUpper (n := 9) g u v)
    (List.range 9) (List.nodup_range : (List.range 9).Nodup) 0
  rw [Nat.zero_add] at countRange
  have rangeToFinset : (List.range 9).toFinset = Finset.range 9 := by
    ext v; simp
  rw [rangeToFinset] at countRange
  have countRange' :
      (List.range 9).foldl
          (fun count v => count + if adjUpper (n := 9) g u v then 1 else 0) 0 =
        #((Finset.range 9).filter fun v => adjUpper (n := 9) g u v = true) := by
    simpa using countRange
  calc
    (graphOfUpper (n := 9) g).degree u =
        #((graphOfUpper (n := 9) g).neighborFinset u) := rfl
    _ = #(((graphOfUpper (n := 9) g).neighborFinset u).map valEmbedding) := by simp
    _ = #((Finset.range 9).filter fun v => adjUpper (n := 9) g u v = true) :=
      congrArg Finset.card neighborMap
    _ = degreeUpperNat (n := 9) g u := by
      rw [← countRange']
      rfl

theorem boolFourValue_injective9 : Function.Injective boolFourValue := by
  intro x y valueEq
  rcases x with ⟨x0, x1, x2, x3⟩
  rcases y with ⟨y0, y1, y2, y3⟩
  fin_cases x0 <;> fin_cases x1 <;> fin_cases x2 <;> fin_cases x3 <;>
    fin_cases y0 <;> fin_cases y1 <;> fin_cases y2 <;> fin_cases y3 <;>
    simp [boolFourValue] at valueEq ⊢ <;> omega

theorem boolFourValue_ofNat_of_lt_sixteen9 (d : Nat) (hd : d < 16) :
    boolFourValue (BoolFour.ofNat d) = d := by
  interval_cases d <;> decide

theorem degreeBitsUpper_same_of_degree_eq9 (g : BitVec 36) (u d : Nat)
    (hd : d < 16) (degreeEq : degreeUpperNat (n := 9) g u = d) :
    (degreeBitsUpper (n := 9) g u).same (BoolFour.ofNat d) = true := by
  apply (boolFourSame_eq_true_iff _ _).mpr
  apply boolFourValue_injective9
  rw [boolFourValue_degreeBitsUpper_eq (n := 9) (by decide), degreeEq,
    boolFourValue_ofNat_of_lt_sixteen9 d hd]

theorem degreeUpperNat_encodeUpper9_eq (G : SimpleGraph (Fin 9))
    [DecidableRel G.Adj] (u : Fin 9) :
    degreeUpperNat (n := 9) (encodeUpper9 G) u = G.degree u := by
  let iso : graphOfUpper (n := 9) (encodeUpper9 G) ≃g G :=
    { toEquiv := Equiv.refl _
      map_rel_iff' := by
        intro x y
        rw [graphOfUpper_encodeUpper9]
        simp }
  calc
    degreeUpperNat (n := 9) (encodeUpper9 G) u =
        (graphOfUpper (n := 9) (encodeUpper9 G)).degree u :=
      (degree_graphOfUpper_eq9 (encodeUpper9 G) u).symm
    _ = G.degree u := (iso.degree_eq u).symm

theorem degreeBitsUpper_encodeUpper9_same (G : SimpleGraph (Fin 9))
    [DecidableRel G.Adj] (u : Fin 9) (d : Nat) (hd : d < 16)
    (degreeEq : G.degree u = d) :
    (degreeBitsUpper (n := 9) (encodeUpper9 G) u).same
      (BoolFour.ofNat d) = true := by
  apply degreeBitsUpper_same_of_degree_eq9 (encodeUpper9 G) u d hd
  rw [degreeUpperNat_encodeUpper9_eq, degreeEq]


theorem fixedDegreeSequenceUpper_encodeUpper9_of_degreeSequence
    (G : SimpleGraph (Fin 9)) [DecidableRel G.Adj] (s : List Nat)
    (hSeq : List.ofFn (fun v : Fin 9 => G.degree v) = s) :
    fixedDegreeSequenceUpper (n := 9) (encodeUpper9 G) s = true := by
  subst hSeq
  simp [fixedDegreeSequenceUpper, matchesDegreesFromUpper]
  have hlt16 : ∀ v : Fin 9, G.degree v < 16 := by
    intro v
    exact lt_of_lt_of_le (G.degree_lt_card_verts v) (by decide)
  refine ⟨
    degreeBitsUpper_encodeUpper9_same G 0 (G.degree 0) (hlt16 0) rfl,
    degreeBitsUpper_encodeUpper9_same G 1 (G.degree 1) (hlt16 1) rfl,
    degreeBitsUpper_encodeUpper9_same G 2 (G.degree 2) (hlt16 2) rfl,
    degreeBitsUpper_encodeUpper9_same G 3 (G.degree 3) (hlt16 3) rfl,
    degreeBitsUpper_encodeUpper9_same G 4 (G.degree 4) (hlt16 4) rfl,
    degreeBitsUpper_encodeUpper9_same G 5 (G.degree 5) (hlt16 5) rfl,
    degreeBitsUpper_encodeUpper9_same G 6 (G.degree 6) (hlt16 6) rfl,
    degreeBitsUpper_encodeUpper9_same G 7 (G.degree 7) (hlt16 7) rfl,
    degreeBitsUpper_encodeUpper9_same G 8 (G.degree 8) (hlt16 8) rfl
  ⟩

end WOWII217Degree9
