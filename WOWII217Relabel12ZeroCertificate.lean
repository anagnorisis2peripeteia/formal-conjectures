import WOWII217Relabel12Core
import WOWII217Finite12Regular
import WOWII217Degree12

/-! Finite certificate for the zero-neighbourhood part of the order-12 relabelling. -/

namespace WOWII217Relabel12

open WOWII217FiniteBase WOWII217Closure WOWII217Finite12Regular
open WOWII217Encoding12
open WOWII217Degree12

theorem foldl_count_eq_countP12 {α : Type*} (p : α → Bool) :
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

theorem zeroNeighbors12_length_eq_degreeUpperNat (g : BitVec 66) :
    (zeroNeighbors12 g).length = degreeUpperNat (n := 12) g 0 := by
  let pFin : Fin 12 → Bool := fun v => adjUpper (n := 12) g 0 v
  let pNat : Nat → Bool := fun v => adjUpper (n := 12) g 0 v
  unfold zeroNeighbors12 degreeUpperNat
  change (nonzeroVertices12.filter pFin).length =
    (List.range 12).foldl
      (fun count v => count + if pNat v then 1 else 0) 0
  rw [← List.countP_eq_length_filter]
  rw [foldl_count_eq_countP12, Nat.zero_add]
  calc
    nonzeroVertices12.countP pFin =
        ((0 : Fin 12) :: nonzeroVertices12).countP pFin := by
      simp [pFin, adjUpper]
    _ = (List.finRange 12).countP pFin := by
      rw [zero_cons_nonzeroVertices12]
    _ = (List.range 12).countP pNat := by
      rw [← List.map_coe_finRange_eq_range, List.countP_map]
      rfl

theorem zeroNeighbors12_length_of_degreeFive (g : BitVec 66)
    (degreeFive : (degreeBitsUpper (n := 12) g 0).same
      (BoolFour.ofNat 5) = true) :
    (zeroNeighbors12 g).length = 5 := by
  rw [zeroNeighbors12_length_eq_degreeUpperNat]
  exact degreeUpperNat_eq_five_of_same g 0 degreeFive

theorem sortedZeroNeighbors12_length_of_degreeFive (g : BitVec 66)
    (degreeFive : (degreeBitsUpper (n := 12) g 0).same
      (BoolFour.ofNat 5) = true) :
    (sortedZeroNeighbors12 g).length = 5 := by
  rw [sortedZeroNeighbors12, List.length_insertionSort]
  exact zeroNeighbors12_length_of_degreeFive g degreeFive

theorem zeroNonneighbors12_length_of_degreeFive (g : BitVec 66)
    (degreeFive : (degreeBitsUpper (n := 12) g 0).same
      (BoolFour.ofNat 5) = true) :
    (zeroNonneighbors12 g).length = 6 := by
  have lengths := (zeroBlocks_perm_nonzeroVertices12 g).length_eq
  rw [List.length_append, zeroNeighbors12_length_of_degreeFive g degreeFive] at lengths
  norm_num [nonzeroVertices12] at lengths ⊢
  omega

theorem sortedZeroNonneighbors12_length_of_degreeFive (g : BitVec 66)
    (degreeFive : (degreeBitsUpper (n := 12) g 0).same
      (BoolFour.ofNat 5) = true) :
    (sortedZeroNonneighbors12 g).length = 6 := by
  rw [sortedZeroNonneighbors12, List.length_insertionSort]
  exact zeroNonneighbors12_length_of_degreeFive g degreeFive

theorem canonicalVertex12_zero (g : BitVec 66) :
    canonicalVertex12 g 0 = 0 := by
  rfl

theorem canonicalVertex12_neighborIndex (g : BitVec 66)
    (degreeFive : (degreeBitsUpper (n := 12) g 0).same
      (BoolFour.ofNat 5) = true) (i : Fin 5) :
    canonicalVertex12 g ⟨i + 1, by omega⟩ =
      (sortedZeroNeighbors12 g).get
        ⟨i, by
          rw [sortedZeroNeighbors12_length_of_degreeFive g degreeFive]
          exact i.isLt⟩ := by
  unfold canonicalVertex12 canonicalOrder12
  simp only [List.get_eq_getElem]
  rw [List.getElem_append_left]
  · rw [List.getElem_cons_succ]
  · simp only [List.length_cons]
    rw [sortedZeroNeighbors12_length_of_degreeFive g degreeFive]
    omega

theorem canonicalVertex12_nonneighborIndex (g : BitVec 66)
    (degreeFive : (degreeBitsUpper (n := 12) g 0).same
      (BoolFour.ofNat 5) = true) (i : Fin 6) :
    canonicalVertex12 g ⟨i + 6, by omega⟩ =
      (sortedZeroNonneighbors12 g).get
        ⟨i, by
          rw [sortedZeroNonneighbors12_length_of_degreeFive g degreeFive]
          exact i.isLt⟩ := by
  unfold canonicalVertex12 canonicalOrder12
  simp only [List.get_eq_getElem]
  rw [List.getElem_append_right]
  · congr
    simp only [List.length_cons]
    rw [sortedZeroNeighbors12_length_of_degreeFive g degreeFive]
    omega
  · simp only [List.length_cons]
    rw [sortedZeroNeighbors12_length_of_degreeFive g degreeFive]
    omega

theorem canonicalVertex12_neighbor_adj (g : BitVec 66)
    (degreeFive : (degreeBitsUpper (n := 12) g 0).same
      (BoolFour.ofNat 5) = true) (i : Fin 5) :
    adjUpper (n := 12) g 0 (canonicalVertex12 g ⟨i + 1, by omega⟩) = true := by
  rw [canonicalVertex12_neighborIndex g degreeFive i]
  have memSorted := List.get_mem (sortedZeroNeighbors12 g)
    ⟨i, by
      rw [sortedZeroNeighbors12_length_of_degreeFive g degreeFive]
      exact i.isLt⟩
  simp only [sortedZeroNeighbors12, List.mem_insertionSort] at memSorted
  exact (List.mem_filter.mp memSorted).2

theorem canonicalVertex12_nonneighbor_notAdj (g : BitVec 66)
    (degreeFive : (degreeBitsUpper (n := 12) g 0).same
      (BoolFour.ofNat 5) = true) (i : Fin 6) :
    (!adjUpper (n := 12) g 0 (canonicalVertex12 g ⟨i + 6, by omega⟩)) = true := by
  rw [canonicalVertex12_nonneighborIndex g degreeFive i]
  have memSorted := List.get_mem (sortedZeroNonneighbors12 g)
    ⟨i, by
      rw [sortedZeroNonneighbors12_length_of_degreeFive g degreeFive]
      exact i.isLt⟩
  simp only [sortedZeroNonneighbors12, List.mem_insertionSort] at memSorted
  exact (List.mem_filter.mp memSorted).2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
theorem canonicalEncodingFast12_zeroNeighborhood : ∀ g : BitVec 66,
    (degreeBitsUpper (n := 12) g 0).same (BoolFour.ofNat 5) = true →
    canonicalZeroNeighborhood12 (canonicalEncodingFast12 g) = true := by
  intro g degreeFive
  simp only [canonicalZeroNeighborhood12, Bool.and_eq_true]
  constructor
  · apply List.all_eq_true.mpr
    intro offset mem
    have offsetLt : offset < 5 := List.mem_range.mp mem
    let i : Fin 5 := ⟨offset, offsetLt⟩
    change adjUpper (n := 12) (canonicalEncodingFast12 g)
      (0 : Fin 12) (⟨offset + 1, by omega⟩ : Fin 12) = true
    rw [adjUpper_canonicalEncodingFast12, canonicalVertex12_zero]
    exact canonicalVertex12_neighbor_adj g degreeFive i
  · apply List.all_eq_true.mpr
    intro offset mem
    have offsetLt : offset < 6 := List.mem_range.mp mem
    let i : Fin 6 := ⟨offset, offsetLt⟩
    change (!adjUpper (n := 12) (canonicalEncodingFast12 g)
      (0 : Fin 12) (⟨offset + 6, by omega⟩ : Fin 12)) = true
    rw [adjUpper_canonicalEncodingFast12, canonicalVertex12_zero]
    exact canonicalVertex12_nonneighbor_notAdj g degreeFive i

end WOWII217Relabel12
