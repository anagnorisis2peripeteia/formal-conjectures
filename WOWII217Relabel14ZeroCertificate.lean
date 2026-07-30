import WOWII217Relabel14Core
import WOWII217Degree14
import WOWII217Closure
import WOWII217ClosureSemantics

/-! Finite certificate for the zero-neighbourhood part of the order-14 relabelling. -/

namespace WOWII217Relabel

open WOWII217DP
open WOWII217Encoding
open WOWII217Closure
open WOWII217ClosureSemantics
open WOWII217Degree14

theorem foldl_count_eq_countP14 {α : Type*} (p : α → Bool) :
    ∀ (xs : List α) (initial : Nat),
      xs.foldl (fun count x => count + if p x then 1 else 0) initial =
        initial + xs.countP p := by
  intro xs
  induction xs with
  | nil => simp
  | cons x xs ih =>
      intro initial
      simp only [List.foldl_cons, List.countP_cons]
      rw [ih]
      by_cases hx : p x <;> simp [hx] <;> omega

theorem degreeUpperNat_eq_six_of_same (g : BitVec 91) (u : Nat)
    (same : (WOWII217FiniteBase.degreeBitsUpper (n := 14) g u).same
      (WOWII217FiniteBase.BoolFour.ofNat 6) = true) :
    degreeUpperNat (n := 14) g u = 6 := by
  have bitsEq := (boolFourSame_eq_true_iff _ _).mp same
  have valueEq := congrArg boolFourValue bitsEq
  rw [boolFourValue_degreeBitsUpper_eq (n := 14) (by decide)] at valueEq
  norm_num [WOWII217FiniteBase.BoolFour.ofNat, WOWII217FiniteBase.maskHas,
    boolFourValue] at valueEq
  exact valueEq

/-- DP and FiniteBase implement the same degree-bits predicate. -/
theorem degreeBitsUpper_dp_eq_finiteBase (g : BitVec 91) (u : Nat) :
    (degreeBitsUpper (n := 14) g u).same (BoolFour.ofNat 6) =
      (WOWII217FiniteBase.degreeBitsUpper (n := 14) g u).same
        (WOWII217FiniteBase.BoolFour.ofNat 6) := rfl

theorem degreeZeroSix_of_fixed14 (g : BitVec 91)
    (sixRegular : fixedDegreeSequenceUpper (n := 14) g
      [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] = true) :
    (degreeBitsUpper (n := 14) g 0).same (BoolFour.ofNat 6) = true := by
  norm_num [fixedDegreeSequenceUpper, matchesDegreesFromUpper] at sixRegular ⊢
  exact sixRegular.1

theorem degreeUpperNat_zero_eq_six_of_fixed14 (g : BitVec 91)
    (sixRegular : fixedDegreeSequenceUpper (n := 14) g
      [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] = true) :
    degreeUpperNat (n := 14) g 0 = 6 := by
  have h := degreeZeroSix_of_fixed14 g sixRegular
  rw [degreeBitsUpper_dp_eq_finiteBase] at h
  exact degreeUpperNat_eq_six_of_same g 0 h

theorem zeroNeighbors14_length_eq_degreeUpperNat (g : BitVec 91) :
    (zeroNeighbors14 g).length = degreeUpperNat (n := 14) g 0 := by
  let pFin : Fin 14 → Bool := fun v => adjUpper (n := 14) g 0 v
  -- degreeUpperNat uses FiniteBase.adjUpper, definitionally equal to DP.adjUpper.
  let pNat : Nat → Bool := fun v => adjUpper (n := 14) g 0 v
  unfold zeroNeighbors14 degreeUpperNat
  change (nonzeroVertices14.filter pFin).length =
    (List.range 14).foldl
      (fun count v => count + if pNat v then 1 else 0) 0
  rw [← List.countP_eq_length_filter]
  rw [foldl_count_eq_countP14, Nat.zero_add]
  calc
    nonzeroVertices14.countP pFin =
        ((0 : Fin 14) :: nonzeroVertices14).countP pFin := by
      simp [pFin, adjUpper]
    _ = (List.finRange 14).countP pFin := by
      rw [zero_cons_nonzeroVertices14]
    _ = (List.range 14).countP pNat := by
      rw [← List.map_coe_finRange_eq_range, List.countP_map]
      rfl

theorem zeroNeighbors14_length_of_degreeSix (g : BitVec 91)
    (sixRegular : fixedDegreeSequenceUpper (n := 14) g
      [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] = true) :
    (zeroNeighbors14 g).length = 6 := by
  rw [zeroNeighbors14_length_eq_degreeUpperNat,
    degreeUpperNat_zero_eq_six_of_fixed14 g sixRegular]

theorem sortedZeroNeighbors14_length_of_degreeSix (g : BitVec 91)
    (sixRegular : fixedDegreeSequenceUpper (n := 14) g
      [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] = true) :
    (sortedZeroNeighbors14 g).length = 6 := by
  rw [sortedZeroNeighbors14, List.length_insertionSort]
  exact zeroNeighbors14_length_of_degreeSix g sixRegular

theorem zeroNonneighbors14_length_of_degreeSix (g : BitVec 91)
    (sixRegular : fixedDegreeSequenceUpper (n := 14) g
      [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] = true) :
    (zeroNonneighbors14 g).length = 7 := by
  have lengths := (zeroBlocks_perm_nonzeroVertices14 g).length_eq
  rw [List.length_append, zeroNeighbors14_length_of_degreeSix g sixRegular]
    at lengths
  norm_num [nonzeroVertices14] at lengths ⊢
  omega

theorem sortedZeroNonneighbors14_length_of_degreeSix (g : BitVec 91)
    (sixRegular : fixedDegreeSequenceUpper (n := 14) g
      [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] = true) :
    (sortedZeroNonneighbors14 g).length = 7 := by
  rw [sortedZeroNonneighbors14, List.length_insertionSort]
  exact zeroNonneighbors14_length_of_degreeSix g sixRegular

theorem canonicalVertex14_zero (g : BitVec 91) :
    canonicalVertex14 g 0 = 0 := by
  rfl

theorem canonicalVertex14_neighborIndex (g : BitVec 91)
    (sixRegular : fixedDegreeSequenceUpper (n := 14) g
      [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] = true) (i : Fin 6) :
    canonicalVertex14 g ⟨i + 1, by omega⟩ =
      (sortedZeroNeighbors14 g).get
        ⟨i, by
          rw [sortedZeroNeighbors14_length_of_degreeSix g sixRegular]
          exact i.isLt⟩ := by
  unfold canonicalVertex14 canonicalOrder14
  simp only [List.get_eq_getElem]
  rw [List.getElem_append_left]
  · rw [List.getElem_cons_succ]
  · simp only [List.length_cons]
    rw [sortedZeroNeighbors14_length_of_degreeSix g sixRegular]
    omega

theorem canonicalVertex14_nonneighborIndex (g : BitVec 91)
    (sixRegular : fixedDegreeSequenceUpper (n := 14) g
      [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] = true) (i : Fin 7) :
    canonicalVertex14 g ⟨i + 7, by omega⟩ =
      (sortedZeroNonneighbors14 g).get
        ⟨i, by
          rw [sortedZeroNonneighbors14_length_of_degreeSix g sixRegular]
          exact i.isLt⟩ := by
  unfold canonicalVertex14 canonicalOrder14
  simp only [List.get_eq_getElem]
  rw [List.getElem_append_right]
  · congr
    simp only [List.length_cons]
    rw [sortedZeroNeighbors14_length_of_degreeSix g sixRegular]
    omega
  · simp only [List.length_cons]
    rw [sortedZeroNeighbors14_length_of_degreeSix g sixRegular]
    omega

theorem canonicalVertex14_neighbor_adj (g : BitVec 91)
    (sixRegular : fixedDegreeSequenceUpper (n := 14) g
      [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] = true) (i : Fin 6) :
    adjUpper (n := 14) g 0 (canonicalVertex14 g ⟨i + 1, by omega⟩) = true := by
  rw [canonicalVertex14_neighborIndex g sixRegular i]
  have memSorted := List.get_mem (sortedZeroNeighbors14 g)
    ⟨i, by
      rw [sortedZeroNeighbors14_length_of_degreeSix g sixRegular]
      exact i.isLt⟩
  simp only [sortedZeroNeighbors14, List.mem_insertionSort] at memSorted
  exact (List.mem_filter.mp memSorted).2

theorem canonicalVertex14_nonneighbor_notAdj (g : BitVec 91)
    (sixRegular : fixedDegreeSequenceUpper (n := 14) g
      [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] = true) (i : Fin 7) :
    (!adjUpper (n := 14) g 0 (canonicalVertex14 g ⟨i + 7, by omega⟩)) = true := by
  rw [canonicalVertex14_nonneighborIndex g sixRegular i]
  have memSorted := List.get_mem (sortedZeroNonneighbors14 g)
    ⟨i, by
      rw [sortedZeroNonneighbors14_length_of_degreeSix g sixRegular]
      exact i.isLt⟩
  simp only [sortedZeroNonneighbors14, List.mem_insertionSort] at memSorted
  exact (List.mem_filter.mp memSorted).2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem canonicalEncodingFast14_zeroNeighborhood : ∀ g : BitVec 91,
    fixedDegreeSequenceUpper (n := 14) g
      [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] = true →
    canonicalZeroNeighborhood14 (canonicalEncodingFast14 g) = true := by
  intro g sixRegular
  have adj (i : Fin 6) :
      adjUpper (n := 14) (canonicalEncodingFast14 g) 0 (i + 1 : Nat) = true := by
    change adjUpper (n := 14) (canonicalEncodingFast14 g)
      (0 : Fin 14) (⟨i + 1, by omega⟩ : Fin 14) = true
    rw [adjUpper_canonicalEncodingFast14, canonicalVertex14_zero]
    exact canonicalVertex14_neighbor_adj g sixRegular i
  have nadj (i : Fin 7) :
      (!adjUpper (n := 14) (canonicalEncodingFast14 g) 0 (i + 7 : Nat)) = true := by
    change (!adjUpper (n := 14) (canonicalEncodingFast14 g)
      (0 : Fin 14) (⟨i + 7, by omega⟩ : Fin 14)) = true
    rw [adjUpper_canonicalEncodingFast14, canonicalVertex14_zero]
    exact canonicalVertex14_nonneighbor_notAdj g sixRegular i
  simp only [canonicalZeroNeighborhood14,
    adj ⟨0, by omega⟩, adj ⟨1, by omega⟩, adj ⟨2, by omega⟩,
    adj ⟨3, by omega⟩, adj ⟨4, by omega⟩, adj ⟨5, by omega⟩,
    nadj ⟨0, by omega⟩, nadj ⟨1, by omega⟩, nadj ⟨2, by omega⟩,
    nadj ⟨3, by omega⟩, nadj ⟨4, by omega⟩, nadj ⟨5, by omega⟩,
    nadj ⟨6, by omega⟩]
  rfl

end WOWII217Relabel
