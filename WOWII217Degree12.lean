import WOWII217Encoding12

/-! Degree-sequence semantics for the 66-bit encoding at order 12. -/

namespace WOWII217Degree12

open SimpleGraph
open Finset
open WOWII217FiniteBase WOWII217Closure WOWII217ClosureSemantics
open WOWII217Encoding12

theorem degree_graphOfUpper_eq12_current (g : BitVec 66) (u : Fin 12) :
    (graphOfUpper (n := 12) g).degree u = degreeUpperNat (n := 12) g u := by
  let valEmbedding : Fin 12 ↪ Nat := ⟨Fin.val, Fin.val_injective⟩
  have neighborMap :
      ((graphOfUpper (n := 12) g).neighborFinset u).map valEmbedding =
        (Finset.range 12).filter fun v => adjUpper (n := 12) g u v = true := by
    ext v
    simp [valEmbedding, graphOfUpper]
    constructor
    · rintro ⟨a, adjacent, rfl⟩
      exact ⟨a.isLt, adjacent⟩
    · rintro ⟨hv, adjacent⟩
      exact ⟨⟨v, hv⟩, adjacent, rfl⟩
  have countRange := foldl_bool_count
    (fun v => adjUpper (n := 12) g u v)
    (List.range 12) (List.nodup_range : (List.range 12).Nodup) 0
  rw [Nat.zero_add] at countRange
  have rangeToFinset : (List.range 12).toFinset = Finset.range 12 := by
    ext v
    simp
  rw [rangeToFinset] at countRange
  have countRange' :
      (List.range 12).foldl
          (fun count v => count + if adjUpper (n := 12) g u v then 1 else 0) 0 =
        #((Finset.range 12).filter fun v => adjUpper (n := 12) g u v = true) := by
    simpa using countRange
  calc
    (graphOfUpper (n := 12) g).degree u =
        #((graphOfUpper (n := 12) g).neighborFinset u) := rfl
    _ = #(((graphOfUpper (n := 12) g).neighborFinset u).map valEmbedding) := by simp
    _ = #((Finset.range 12).filter fun v => adjUpper (n := 12) g u v = true) :=
      congrArg Finset.card neighborMap
    _ = degreeUpperNat (n := 12) g u := by
      rw [← countRange']
      rfl

theorem boolFourValue_injective12 : Function.Injective boolFourValue := by
  intro x y valueEq
  rcases x with ⟨x0, x1, x2, x3⟩
  rcases y with ⟨y0, y1, y2, y3⟩
  fin_cases x0 <;> fin_cases x1 <;> fin_cases x2 <;> fin_cases x3 <;>
    fin_cases y0 <;> fin_cases y1 <;> fin_cases y2 <;> fin_cases y3 <;>
    simp [boolFourValue] at valueEq ⊢ <;> omega

theorem boolFourValue_ofNat_of_lt_sixteen12 (d : Nat) (hd : d < 16) :
    boolFourValue (BoolFour.ofNat d) = d := by
  interval_cases d <;> native_decide

theorem degreeBitsUpper_same_of_degree_eq12 (g : BitVec 66) (u d : Nat)
    (hd : d < 16) (degreeEq : degreeUpperNat (n := 12) g u = d) :
    (degreeBitsUpper (n := 12) g u).same (BoolFour.ofNat d) = true := by
  apply (boolFourSame_eq_true_iff _ _).mpr
  apply boolFourValue_injective12
  rw [boolFourValue_degreeBitsUpper_eq (n := 12) (by decide), degreeEq,
    boolFourValue_ofNat_of_lt_sixteen12 d hd]

theorem degreeUpperNat_encodeUpper12_eq (G : SimpleGraph (Fin 12))
    [DecidableRel G.Adj] (u : Fin 12) :
    degreeUpperNat (n := 12) (encodeUpper12 G) u = G.degree u := by
  let iso : graphOfUpper (n := 12) (encodeUpper12 G) ≃g G :=
    { toEquiv := Equiv.refl _
      map_rel_iff' := by
        intro x y
        rw [graphOfUpper_encodeUpper12]
        simp }
  calc
    degreeUpperNat (n := 12) (encodeUpper12 G) u =
        (graphOfUpper (n := 12) (encodeUpper12 G)).degree u :=
      (degree_graphOfUpper_eq12_current (encodeUpper12 G) u).symm
    _ = G.degree u := (iso.degree_eq u).symm

theorem degreeBitsUpper_encodeUpper12_same (G : SimpleGraph (Fin 12))
    [DecidableRel G.Adj] (u : Fin 12) (d : Nat) (hd : d < 16)
    (degreeEq : G.degree u = d) :
    (degreeBitsUpper (n := 12) (encodeUpper12 G) u).same
      (BoolFour.ofNat d) = true := by
  apply degreeBitsUpper_same_of_degree_eq12 (encodeUpper12 G) u d hd
  rw [degreeUpperNat_encodeUpper12_eq, degreeEq]

theorem fixedDegreeSequenceUpper_encodeUpper12_of_fiveRegular
    (G : SimpleGraph (Fin 12)) [DecidableRel G.Adj]
    (fiveRegular : ∀ v : Fin 12, G.degree v = 5) :
    fixedDegreeSequenceUpper (n := 12) (encodeUpper12 G)
      [5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5] = true := by
  have match0 := degreeBitsUpper_encodeUpper12_same G 0 5 (by decide) (fiveRegular 0)
  have match1 := degreeBitsUpper_encodeUpper12_same G 1 5 (by decide) (fiveRegular 1)
  have match2 := degreeBitsUpper_encodeUpper12_same G 2 5 (by decide) (fiveRegular 2)
  have match3 := degreeBitsUpper_encodeUpper12_same G 3 5 (by decide) (fiveRegular 3)
  have match4 := degreeBitsUpper_encodeUpper12_same G 4 5 (by decide) (fiveRegular 4)
  have match5 := degreeBitsUpper_encodeUpper12_same G 5 5 (by decide) (fiveRegular 5)
  have match6 := degreeBitsUpper_encodeUpper12_same G 6 5 (by decide) (fiveRegular 6)
  have match7 := degreeBitsUpper_encodeUpper12_same G 7 5 (by decide) (fiveRegular 7)
  have match8 := degreeBitsUpper_encodeUpper12_same G 8 5 (by decide) (fiveRegular 8)
  have match9 := degreeBitsUpper_encodeUpper12_same G 9 5 (by decide) (fiveRegular 9)
  have match10 := degreeBitsUpper_encodeUpper12_same G 10 5 (by decide) (fiveRegular 10)
  have match11 := degreeBitsUpper_encodeUpper12_same G 11 5 (by decide) (fiveRegular 11)
  norm_num [fixedDegreeSequenceUpper, matchesDegreesFromUpper]
  constructor
  · simpa using match0
  constructor
  · simpa using match1
  constructor
  · simpa using match2
  constructor
  · simpa using match3
  constructor
  · simpa using match4
  constructor
  · simpa using match5
  constructor
  · simpa using match6
  constructor
  · simpa using match7
  constructor
  · simpa using match8
  constructor
  · simpa using match9
  constructor
  · simpa using match10
  · simpa using match11

theorem degreeUpperNat_eq_five_of_same (g : BitVec 66) (u : Nat)
    (same : (degreeBitsUpper (n := 12) g u).same (BoolFour.ofNat 5) = true) :
    degreeUpperNat (n := 12) g u = 5 := by
  have bitsEq := (boolFourSame_eq_true_iff _ _).mp same
  have valueEq := congrArg boolFourValue bitsEq
  rw [boolFourValue_degreeBitsUpper_eq (n := 12) (by decide)] at valueEq
  norm_num [BoolFour.ofNat, maskHas, boolFourValue] at valueEq
  exact valueEq

theorem fiveRegular_graphOfUpper_of_fixed (g : BitVec 66)
    (fixed : fixedDegreeSequenceUpper (n := 12) g
      [5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5] = true) :
    ∀ v : Fin 12, (graphOfUpper (n := 12) g).degree v = 5 := by
  intro v
  have upperDegree : degreeUpperNat (n := 12) g v = 5 := by
    fin_cases v <;>
      norm_num [fixedDegreeSequenceUpper, matchesDegreesFromUpper] at fixed ⊢ <;>
      apply degreeUpperNat_eq_five_of_same <;>
      aesop
  calc
    (graphOfUpper (n := 12) g).degree v = degreeUpperNat (n := 12) g v :=
      degree_graphOfUpper_eq12_current g v
    _ = 5 := upperDegree

end WOWII217Degree12
