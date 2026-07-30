import WOWII217Relabel12ZeroCertificate

/-! Structural certificate for the partition-degree ordering of the order-12 relabelling. -/

namespace WOWII217Relabel12

open WOWII217FiniteBase WOWII217Closure WOWII217Finite12Regular
open WOWII217Encoding12

def canonicalNeighborVertices12 (g : BitVec 66) : List (Fin 12) :=
  List.ofFn fun i : Fin 5 => canonicalVertex12 g ⟨i + 1, by omega⟩

def canonicalNonneighborVertices12 (g : BitVec 66) : List (Fin 12) :=
  List.ofFn fun i : Fin 6 => canonicalVertex12 g ⟨i + 6, by omega⟩

theorem sortedZeroNeighbors12_eq_canonicalNeighborVertices12 (g : BitVec 66)
    (degreeFive : (degreeBitsUpper (n := 12) g 0).same
      (BoolFour.ofNat 5) = true) :
    sortedZeroNeighbors12 g = canonicalNeighborVertices12 g := by
  apply List.ext_get
  · rw [sortedZeroNeighbors12_length_of_degreeFive g degreeFive]
    simp [canonicalNeighborVertices12]
  · intro n hnSorted hnCanonical
    have hn : n < 5 := by
      simpa [canonicalNeighborVertices12] using hnCanonical
    change (sortedZeroNeighbors12 g).get ⟨n, hnSorted⟩ =
      (List.ofFn fun i : Fin 5 => canonicalVertex12 g ⟨i + 1, by omega⟩).get
        ⟨n, hnCanonical⟩
    rw [List.get_ofFn]
    simpa using (canonicalVertex12_neighborIndex g degreeFive ⟨n, hn⟩).symm

theorem sortedZeroNonneighbors12_eq_canonicalNonneighborVertices12 (g : BitVec 66)
    (degreeFive : (degreeBitsUpper (n := 12) g 0).same
      (BoolFour.ofNat 5) = true) :
    sortedZeroNonneighbors12 g = canonicalNonneighborVertices12 g := by
  apply List.ext_get
  · rw [sortedZeroNonneighbors12_length_of_degreeFive g degreeFive]
    simp [canonicalNonneighborVertices12]
  · intro n hnSorted hnCanonical
    have hn : n < 6 := by
      simpa [canonicalNonneighborVertices12] using hnCanonical
    change (sortedZeroNonneighbors12 g).get ⟨n, hnSorted⟩ =
      (List.ofFn fun i : Fin 6 => canonicalVertex12 g ⟨i + 6, by omega⟩).get
        ⟨n, hnCanonical⟩
    rw [List.get_ofFn]
    simpa using (canonicalVertex12_nonneighborIndex g degreeFive ⟨n, hn⟩).symm

theorem adjUpper_canonicalEncodingFast12_nat (g : BitVec 66)
    (u v : Nat) (hu : u < 12) (hv : v < 12) :
    adjUpper (n := 12) (canonicalEncodingFast12 g) u v =
      adjUpper (n := 12) g
        (canonicalVertex12 g ⟨u, hu⟩) (canonicalVertex12 g ⟨v, hv⟩) := by
  exact adjUpper_canonicalEncodingFast12 g ⟨u, hu⟩ ⟨v, hv⟩

theorem degreeCountRange12_toNonneighbors (g : BitVec 66) (u : Fin 12) :
    degreeCountRange12 (canonicalEncodingFast12 g) u 6 6 =
      adjCountTo12 g (canonicalVertex12 g u) (canonicalNonneighborVertices12 g) := by
  simp [degreeCountRange12, adjCountTo12, canonicalNonneighborVertices12,
    List.range, List.range.loop, adjUpper_canonicalEncodingFast12_nat]

theorem degreeCountRange12_toNeighbors (g : BitVec 66) (u : Fin 12) :
    degreeCountRange12 (canonicalEncodingFast12 g) u 1 5 =
      adjCountTo12 g (canonicalVertex12 g u) (canonicalNeighborVertices12 g) := by
  simp [degreeCountRange12, adjCountTo12, canonicalNeighborVertices12,
    List.range, List.range.loop, adjUpper_canonicalEncodingFast12_nat]

theorem adjCountTo12_eq_of_perm (g : BitVec 66) (u : Fin 12)
    {xs ys : List (Fin 12)} (h : xs.Perm ys) :
    adjCountTo12 g u xs = adjCountTo12 g u ys := by
  unfold adjCountTo12
  rw [foldl_count_eq_countP12, foldl_count_eq_countP12]
  simp only [Nat.zero_add]
  have hm :
      (xs.flatMap (fun v : Fin 12 => [(v : Nat)])).Perm
        (ys.flatMap (fun v : Fin 12 => [(v : Nat)])) :=
    h.flatMap (fun _ _ => .rfl)
  exact hm.countP_eq (fun v : Nat => adjUpper (n := 12) g u v)

theorem adjCountTo12_sortedNonneighbors_eq_zeroNonneighbors
    (g : BitVec 66) (u : Fin 12) :
    adjCountTo12 g u (sortedZeroNonneighbors12 g) =
      adjCountTo12 g u (zeroNonneighbors12 g) := by
  apply adjCountTo12_eq_of_perm
  exact List.perm_insertionSort _ _

theorem pairwise_insertionSort_natScore12 {α : Type*}
    (score : α → Nat) (xs : List α) :
    (xs.insertionSort fun u v => score u ≤ score v).Pairwise
      fun u v => score u ≤ score v := by
  letI : Std.Total (fun u v : α => score u ≤ score v) :=
    ⟨fun u v => Nat.le_total (score u) (score v)⟩
  letI : IsTrans α (fun u v : α => score u ≤ score v) :=
    ⟨fun _ _ _ hab hbc => Nat.le_trans hab hbc⟩
  exact List.pairwise_insertionSort _ _

theorem sortedZeroNeighbors12_pairwise (g : BitVec 66) :
    (sortedZeroNeighbors12 g).Pairwise fun u v =>
      adjCountTo12 g u (zeroNonneighbors12 g) ≤
        adjCountTo12 g v (zeroNonneighbors12 g) := by
  unfold sortedZeroNeighbors12
  exact pairwise_insertionSort_natScore12
    (fun u => adjCountTo12 g u (zeroNonneighbors12 g)) _

theorem sortedZeroNonneighbors12_pairwise (g : BitVec 66) :
    (sortedZeroNonneighbors12 g).Pairwise fun u v =>
      adjCountTo12 g u (sortedZeroNeighbors12 g) ≤
        adjCountTo12 g v (sortedZeroNeighbors12 g) := by
  unfold sortedZeroNonneighbors12
  exact pairwise_insertionSort_natScore12
    (fun u => adjCountTo12 g u (sortedZeroNeighbors12 g)) _

theorem adjacentCanonicalNeighborCounts_le (g : BitVec 66)
    (degreeFive : (degreeBitsUpper (n := 12) g 0).same
      (BoolFour.ofNat 5) = true) (i : Fin 4) :
    adjCountTo12 g (canonicalVertex12 g ⟨i + 1, by omega⟩)
        (zeroNonneighbors12 g) ≤
      adjCountTo12 g (canonicalVertex12 g ⟨i + 2, by omega⟩)
        (zeroNonneighbors12 g) := by
  have hpair := sortedZeroNeighbors12_pairwise g
  have hrel := hpair.rel_get_of_lt
    (a := ⟨i, by
      rw [sortedZeroNeighbors12_length_of_degreeFive g degreeFive]
      omega⟩)
    (b := ⟨i + 1, by
      rw [sortedZeroNeighbors12_length_of_degreeFive g degreeFive]
      omega⟩)
    (by exact Nat.lt_succ_self i)
  rw [← canonicalVertex12_neighborIndex g degreeFive ⟨i, by omega⟩,
    ← canonicalVertex12_neighborIndex g degreeFive ⟨i + 1, by omega⟩] at hrel
  exact hrel

theorem adjacentCanonicalNonneighborCounts_le (g : BitVec 66)
    (degreeFive : (degreeBitsUpper (n := 12) g 0).same
      (BoolFour.ofNat 5) = true) (i : Fin 5) :
    adjCountTo12 g (canonicalVertex12 g ⟨i + 6, by omega⟩)
        (sortedZeroNeighbors12 g) ≤
      adjCountTo12 g (canonicalVertex12 g ⟨i + 7, by omega⟩)
        (sortedZeroNeighbors12 g) := by
  have hpair := sortedZeroNonneighbors12_pairwise g
  have hrel := hpair.rel_get_of_lt
    (a := ⟨i, by
      rw [sortedZeroNonneighbors12_length_of_degreeFive g degreeFive]
      omega⟩)
    (b := ⟨i + 1, by
      rw [sortedZeroNonneighbors12_length_of_degreeFive g degreeFive]
      omega⟩)
    (by exact Nat.lt_succ_self i)
  rw [← canonicalVertex12_nonneighborIndex g degreeFive ⟨i, by omega⟩,
    ← canonicalVertex12_nonneighborIndex g degreeFive ⟨i + 1, by omega⟩] at hrel
  exact hrel

theorem adjacentCanonicalNeighborDegrees_le (g : BitVec 66)
    (degreeFive : (degreeBitsUpper (n := 12) g 0).same
      (BoolFour.ofNat 5) = true) (i : Fin 4) :
    degreeCountRange12 (canonicalEncodingFast12 g) (i + 1) 6 6 ≤
      degreeCountRange12 (canonicalEncodingFast12 g) (i + 2) 6 6 := by
  rw [degreeCountRange12_toNonneighbors g ⟨i + 1, by omega⟩,
    degreeCountRange12_toNonneighbors g ⟨i + 2, by omega⟩]
  rw [← sortedZeroNonneighbors12_eq_canonicalNonneighborVertices12 g degreeFive]
  rw [adjCountTo12_sortedNonneighbors_eq_zeroNonneighbors,
    adjCountTo12_sortedNonneighbors_eq_zeroNonneighbors]
  exact adjacentCanonicalNeighborCounts_le g degreeFive i

theorem adjacentCanonicalNonneighborDegrees_le (g : BitVec 66)
    (degreeFive : (degreeBitsUpper (n := 12) g 0).same
      (BoolFour.ofNat 5) = true) (i : Fin 5) :
    degreeCountRange12 (canonicalEncodingFast12 g) (i + 6) 1 5 ≤
      degreeCountRange12 (canonicalEncodingFast12 g) (i + 7) 1 5 := by
  rw [degreeCountRange12_toNeighbors g ⟨i + 6, by omega⟩,
    degreeCountRange12_toNeighbors g ⟨i + 7, by omega⟩]
  rw [← sortedZeroNeighbors12_eq_canonicalNeighborVertices12 g degreeFive]
  exact adjacentCanonicalNonneighborCounts_le g degreeFive i

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
theorem canonicalEncodingFast12_partitionSorted : ∀ g : BitVec 66,
    (degreeBitsUpper (n := 12) g 0).same (BoolFour.ofNat 5) = true →
    canonicalPartitionDegreesSorted12 (canonicalEncodingFast12 g) = true := by
  intro g degreeFive
  simp only [canonicalPartitionDegreesSorted12, Bool.and_eq_true]
  constructor
  · apply List.all_eq_true.mpr
    intro offset mem
    have offsetLt : offset < 4 := List.mem_range.mp mem
    exact decide_eq_true
      (adjacentCanonicalNeighborDegrees_le g degreeFive ⟨offset, offsetLt⟩)
  · apply List.all_eq_true.mpr
    intro offset mem
    have offsetLt : offset < 5 := List.mem_range.mp mem
    exact decide_eq_true
      (adjacentCanonicalNonneighborDegrees_le g degreeFive ⟨offset, offsetLt⟩)

end WOWII217Relabel12
