import WOWII217Encoding6

/-! Degree-sequence semantics for the 15-bit encoding at order 6. -/

namespace WOWII217Degree6

open SimpleGraph
open Finset
open WOWII217FiniteBase WOWII217Closure WOWII217ClosureSemantics
open WOWII217Encoding6

theorem degree_graphOfUpper_eq6 (g : BitVec 15) (u : Fin 6) :
    (graphOfUpper (n := 6) g).degree u = degreeUpperNat (n := 6) g u := by
  let valEmbedding : Fin 6 ↪ Nat := ⟨Fin.val, Fin.val_injective⟩
  have neighborMap :
      ((graphOfUpper (n := 6) g).neighborFinset u).map valEmbedding =
        (Finset.range 6).filter fun v => adjUpper (n := 6) g u v = true := by
    ext v
    simp [valEmbedding, graphOfUpper]
    constructor
    · rintro ⟨a, adjacent, rfl⟩
      exact ⟨a.isLt, adjacent⟩
    · rintro ⟨hv, adjacent⟩
      exact ⟨⟨v, hv⟩, adjacent, rfl⟩
  have countRange := foldl_bool_count
    (fun v => adjUpper (n := 6) g u v)
    (List.range 6) (List.nodup_range : (List.range 6).Nodup) 0
  rw [Nat.zero_add] at countRange
  have rangeToFinset : (List.range 6).toFinset = Finset.range 6 := by
    ext v; simp
  rw [rangeToFinset] at countRange
  have countRange' :
      (List.range 6).foldl
          (fun count v => count + if adjUpper (n := 6) g u v then 1 else 0) 0 =
        #((Finset.range 6).filter fun v => adjUpper (n := 6) g u v = true) := by
    simpa using countRange
  calc
    (graphOfUpper (n := 6) g).degree u =
        #((graphOfUpper (n := 6) g).neighborFinset u) := rfl
    _ = #(((graphOfUpper (n := 6) g).neighborFinset u).map valEmbedding) := by simp
    _ = #((Finset.range 6).filter fun v => adjUpper (n := 6) g u v = true) :=
      congrArg Finset.card neighborMap
    _ = degreeUpperNat (n := 6) g u := by
      rw [← countRange']
      rfl

theorem boolFourValue_injective6 : Function.Injective boolFourValue := by
  intro x y valueEq
  rcases x with ⟨x0, x1, x2, x3⟩
  rcases y with ⟨y0, y1, y2, y3⟩
  fin_cases x0 <;> fin_cases x1 <;> fin_cases x2 <;> fin_cases x3 <;>
    fin_cases y0 <;> fin_cases y1 <;> fin_cases y2 <;> fin_cases y3 <;>
    simp [boolFourValue] at valueEq ⊢ <;> omega

theorem boolFourValue_ofNat_of_lt_sixteen6 (d : Nat) (hd : d < 16) :
    boolFourValue (BoolFour.ofNat d) = d := by
  interval_cases d <;> native_decide

theorem degreeBitsUpper_same_of_degree_eq6 (g : BitVec 15) (u d : Nat)
    (hd : d < 16) (degreeEq : degreeUpperNat (n := 6) g u = d) :
    (degreeBitsUpper (n := 6) g u).same (BoolFour.ofNat d) = true := by
  apply (boolFourSame_eq_true_iff _ _).mpr
  apply boolFourValue_injective6
  rw [boolFourValue_degreeBitsUpper_eq (n := 6) (by decide), degreeEq,
    boolFourValue_ofNat_of_lt_sixteen6 d hd]

theorem degreeUpperNat_encodeUpper6_eq (G : SimpleGraph (Fin 6))
    [DecidableRel G.Adj] (u : Fin 6) :
    degreeUpperNat (n := 6) (encodeUpper6 G) u = G.degree u := by
  let iso : graphOfUpper (n := 6) (encodeUpper6 G) ≃g G :=
    { toEquiv := Equiv.refl _
      map_rel_iff' := by
        intro x y
        rw [graphOfUpper_encodeUpper6]
        simp }
  calc
    degreeUpperNat (n := 6) (encodeUpper6 G) u =
        (graphOfUpper (n := 6) (encodeUpper6 G)).degree u :=
      (degree_graphOfUpper_eq6 (encodeUpper6 G) u).symm
    _ = G.degree u := (iso.degree_eq u).symm

theorem degreeBitsUpper_encodeUpper6_same (G : SimpleGraph (Fin 6))
    [DecidableRel G.Adj] (u : Fin 6) (d : Nat) (hd : d < 16)
    (degreeEq : G.degree u = d) :
    (degreeBitsUpper (n := 6) (encodeUpper6 G) u).same
      (BoolFour.ofNat d) = true := by
  apply degreeBitsUpper_same_of_degree_eq6 (encodeUpper6 G) u d hd
  rw [degreeUpperNat_encodeUpper6_eq, degreeEq]


theorem fixedDegreeSequenceUpper_encodeUpper6_of_degreeSequence
    (G : SimpleGraph (Fin 6)) [DecidableRel G.Adj] (s : List Nat)
    (hSeq : List.ofFn (fun v : Fin 6 => G.degree v) = s) :
    fixedDegreeSequenceUpper (n := 6) (encodeUpper6 G) s = true := by
  sorry

end WOWII217Degree6
