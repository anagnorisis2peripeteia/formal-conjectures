import WOWII217Encoding7

/-! Degree-sequence semantics for the 21-bit encoding at order 7. -/

namespace WOWII217Degree7

open SimpleGraph
open Finset
open WOWII217FiniteBase WOWII217Closure WOWII217ClosureSemantics
open WOWII217Encoding7

theorem degree_graphOfUpper_eq7 (g : BitVec 21) (u : Fin 7) :
    (graphOfUpper (n := 7) g).degree u = degreeUpperNat (n := 7) g u := by
  let valEmbedding : Fin 7 ↪ Nat := ⟨Fin.val, Fin.val_injective⟩
  have neighborMap :
      ((graphOfUpper (n := 7) g).neighborFinset u).map valEmbedding =
        (Finset.range 7).filter fun v => adjUpper (n := 7) g u v = true := by
    ext v
    simp [valEmbedding, graphOfUpper]
    constructor
    · rintro ⟨a, adjacent, rfl⟩
      exact ⟨a.isLt, adjacent⟩
    · rintro ⟨hv, adjacent⟩
      exact ⟨⟨v, hv⟩, adjacent, rfl⟩
  have countRange := foldl_bool_count
    (fun v => adjUpper (n := 7) g u v)
    (List.range 7) (List.nodup_range : (List.range 7).Nodup) 0
  rw [Nat.zero_add] at countRange
  have rangeToFinset : (List.range 7).toFinset = Finset.range 7 := by
    ext v; simp
  rw [rangeToFinset] at countRange
  have countRange' :
      (List.range 7).foldl
          (fun count v => count + if adjUpper (n := 7) g u v then 1 else 0) 0 =
        #((Finset.range 7).filter fun v => adjUpper (n := 7) g u v = true) := by
    simpa using countRange
  calc
    (graphOfUpper (n := 7) g).degree u =
        #((graphOfUpper (n := 7) g).neighborFinset u) := rfl
    _ = #(((graphOfUpper (n := 7) g).neighborFinset u).map valEmbedding) := by simp
    _ = #((Finset.range 7).filter fun v => adjUpper (n := 7) g u v = true) :=
      congrArg Finset.card neighborMap
    _ = degreeUpperNat (n := 7) g u := by
      rw [← countRange']
      rfl

theorem boolFourValue_injective7 : Function.Injective boolFourValue := by
  intro x y valueEq
  rcases x with ⟨x0, x1, x2, x3⟩
  rcases y with ⟨y0, y1, y2, y3⟩
  fin_cases x0 <;> fin_cases x1 <;> fin_cases x2 <;> fin_cases x3 <;>
    fin_cases y0 <;> fin_cases y1 <;> fin_cases y2 <;> fin_cases y3 <;>
    simp [boolFourValue] at valueEq ⊢ <;> omega

theorem boolFourValue_ofNat_of_lt_sixteen7 (d : Nat) (hd : d < 16) :
    boolFourValue (BoolFour.ofNat d) = d := by
  interval_cases d <;> native_decide

theorem degreeBitsUpper_same_of_degree_eq7 (g : BitVec 21) (u d : Nat)
    (hd : d < 16) (degreeEq : degreeUpperNat (n := 7) g u = d) :
    (degreeBitsUpper (n := 7) g u).same (BoolFour.ofNat d) = true := by
  apply (boolFourSame_eq_true_iff _ _).mpr
  apply boolFourValue_injective7
  rw [boolFourValue_degreeBitsUpper_eq (n := 7) (by decide), degreeEq,
    boolFourValue_ofNat_of_lt_sixteen7 d hd]

theorem degreeUpperNat_encodeUpper7_eq (G : SimpleGraph (Fin 7))
    [DecidableRel G.Adj] (u : Fin 7) :
    degreeUpperNat (n := 7) (encodeUpper7 G) u = G.degree u := by
  let iso : graphOfUpper (n := 7) (encodeUpper7 G) ≃g G :=
    { toEquiv := Equiv.refl _
      map_rel_iff' := by
        intro x y
        rw [graphOfUpper_encodeUpper7]
        simp }
  calc
    degreeUpperNat (n := 7) (encodeUpper7 G) u =
        (graphOfUpper (n := 7) (encodeUpper7 G)).degree u :=
      (degree_graphOfUpper_eq7 (encodeUpper7 G) u).symm
    _ = G.degree u := (iso.degree_eq u).symm

theorem degreeBitsUpper_encodeUpper7_same (G : SimpleGraph (Fin 7))
    [DecidableRel G.Adj] (u : Fin 7) (d : Nat) (hd : d < 16)
    (degreeEq : G.degree u = d) :
    (degreeBitsUpper (n := 7) (encodeUpper7 G) u).same
      (BoolFour.ofNat d) = true := by
  apply degreeBitsUpper_same_of_degree_eq7 (encodeUpper7 G) u d hd
  rw [degreeUpperNat_encodeUpper7_eq, degreeEq]


theorem fixedDegreeSequenceUpper_encodeUpper7_of_degreeSequence
    (G : SimpleGraph (Fin 7)) [DecidableRel G.Adj] (s : List Nat)
    (hSeq : List.ofFn (fun v : Fin 7 => G.degree v) = s) :
    fixedDegreeSequenceUpper (n := 7) (encodeUpper7 G) s = true := by
  sorry

end WOWII217Degree7
