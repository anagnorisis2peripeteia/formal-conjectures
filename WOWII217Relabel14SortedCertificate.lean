import WOWII217Relabel14ZeroCertificate

/-! Structural certificate for the partition-degree ordering of the order-14 relabelling. -/

set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

namespace WOWII217Relabel

open WOWII217DP
open WOWII217Encoding

def canonicalNeighborVertices14 (g : BitVec 91) : List (Fin 14) :=
  List.ofFn fun i : Fin 6 => canonicalVertex14 g ⟨i + 1, by omega⟩

def canonicalNonneighborVertices14 (g : BitVec 91) : List (Fin 14) :=
  List.ofFn fun i : Fin 7 => canonicalVertex14 g ⟨i + 7, by omega⟩

theorem sortedZeroNeighbors14_eq_canonicalNeighborVertices14 (g : BitVec 91)
    (sixRegular : fixedDegreeSequenceUpper (n := 14) g
      [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] = true) :
    sortedZeroNeighbors14 g = canonicalNeighborVertices14 g := by
  apply List.ext_get
  · rw [sortedZeroNeighbors14_length_of_degreeSix g sixRegular]
    simp [canonicalNeighborVertices14]
  · intro n hnSorted hnCanonical
    have hn : n < 6 := by
      simpa [canonicalNeighborVertices14] using hnCanonical
    change (sortedZeroNeighbors14 g).get ⟨n, hnSorted⟩ =
      (List.ofFn fun i : Fin 6 => canonicalVertex14 g ⟨i + 1, by omega⟩).get
        ⟨n, hnCanonical⟩
    rw [List.get_ofFn]
    simpa using (canonicalVertex14_neighborIndex g sixRegular ⟨n, hn⟩).symm

theorem sortedZeroNonneighbors14_eq_canonicalNonneighborVertices14 (g : BitVec 91)
    (sixRegular : fixedDegreeSequenceUpper (n := 14) g
      [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] = true) :
    sortedZeroNonneighbors14 g = canonicalNonneighborVertices14 g := by
  apply List.ext_get
  · rw [sortedZeroNonneighbors14_length_of_degreeSix g sixRegular]
    simp [canonicalNonneighborVertices14]
  · intro n hnSorted hnCanonical
    have hn : n < 7 := by
      simpa [canonicalNonneighborVertices14] using hnCanonical
    change (sortedZeroNonneighbors14 g).get ⟨n, hnSorted⟩ =
      (List.ofFn fun i : Fin 7 => canonicalVertex14 g ⟨i + 7, by omega⟩).get
        ⟨n, hnCanonical⟩
    rw [List.get_ofFn]
    simpa using (canonicalVertex14_nonneighborIndex g sixRegular ⟨n, hn⟩).symm

theorem adjUpper_canonicalEncodingFast14_nat (g : BitVec 91)
    (u v : Nat) (hu : u < 14) (hv : v < 14) :
    adjUpper (n := 14) (canonicalEncodingFast14 g) u v =
      adjUpper (n := 14) g
        (canonicalVertex14 g ⟨u, hu⟩) (canonicalVertex14 g ⟨v, hv⟩) := by
  exact adjUpper_canonicalEncodingFast14 g ⟨u, hu⟩ ⟨v, hv⟩

def degreeCountRange14 (g : BitVec 91) (u start count : Nat) : Nat :=
  (List.range count).foldl (fun acc offset =>
    acc + if adjUpper (n := 14) g u (start + offset) then 1 else 0) 0

theorem degreeCountRange14_toNonneighbors (g : BitVec 91) (u : Fin 14) :
    degreeCountRange14 (canonicalEncodingFast14 g) u 7 7 =
      adjCountTo14 g (canonicalVertex14 g u) (canonicalNonneighborVertices14 g) := by
  simp [degreeCountRange14, adjCountTo14, canonicalNonneighborVertices14,
    List.range, List.range.loop, adjUpper_canonicalEncodingFast14_nat]

theorem degreeCountRange14_toNeighbors (g : BitVec 91) (u : Fin 14) :
    degreeCountRange14 (canonicalEncodingFast14 g) u 1 6 =
      adjCountTo14 g (canonicalVertex14 g u) (canonicalNeighborVertices14 g) := by
  simp [degreeCountRange14, adjCountTo14, canonicalNeighborVertices14,
    List.range, List.range.loop, adjUpper_canonicalEncodingFast14_nat]

theorem adjCountTo14_eq_of_perm (g : BitVec 91) (u : Fin 14)
    {xs ys : List (Fin 14)} (h : xs.Perm ys) :
    adjCountTo14 g u xs = adjCountTo14 g u ys := by
  unfold adjCountTo14
  refine List.Perm.foldl_eq' h ?_ 0
  intro x _ y _ z
  cases hx : adjUpper (n := 14) g u.val x.val <;>
    cases hy : adjUpper (n := 14) g u.val y.val <;>
    simp [Nat.add_left_comm, Nat.add_comm]

theorem adjCountTo14_sortedNonneighbors_eq_zeroNonneighbors
    (g : BitVec 91) (u : Fin 14) :
    adjCountTo14 g u (sortedZeroNonneighbors14 g) =
      adjCountTo14 g u (zeroNonneighbors14 g) := by
  apply adjCountTo14_eq_of_perm
  exact List.perm_insertionSort _ _

theorem pairwise_insertionSort_natScore14 {α : Type*}
    (score : α → Nat) (xs : List α) :
    (xs.insertionSort fun u v => score u ≤ score v).Pairwise
      fun u v => score u ≤ score v := by
  letI : Std.Total (fun u v : α => score u ≤ score v) :=
    ⟨fun u v => Nat.le_total (score u) (score v)⟩
  letI : IsTrans α (fun u v : α => score u ≤ score v) :=
    ⟨fun _ _ _ hab hbc => Nat.le_trans hab hbc⟩
  exact List.pairwise_insertionSort _ _

theorem sortedZeroNeighbors14_pairwise (g : BitVec 91) :
    (sortedZeroNeighbors14 g).Pairwise fun u v =>
      adjCountTo14 g u (zeroNonneighbors14 g) ≤
        adjCountTo14 g v (zeroNonneighbors14 g) := by
  unfold sortedZeroNeighbors14
  exact pairwise_insertionSort_natScore14
    (fun u => adjCountTo14 g u (zeroNonneighbors14 g)) _

theorem sortedZeroNonneighbors14_pairwise (g : BitVec 91) :
    (sortedZeroNonneighbors14 g).Pairwise fun u v =>
      nonneighborKey14 g (sortedZeroNeighbors14 g) u ≤
        nonneighborKey14 g (sortedZeroNeighbors14 g) v := by
  unfold sortedZeroNonneighbors14
  exact pairwise_insertionSort_natScore14
    (fun u => nonneighborKey14 g (sortedZeroNeighbors14 g) u) _

theorem adjacentCanonicalNeighborCounts_le (g : BitVec 91)
    (sixRegular : fixedDegreeSequenceUpper (n := 14) g
      [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] = true) (i : Fin 5) :
    adjCountTo14 g (canonicalVertex14 g ⟨i + 1, by omega⟩)
        (zeroNonneighbors14 g) ≤
      adjCountTo14 g (canonicalVertex14 g ⟨i + 2, by omega⟩)
        (zeroNonneighbors14 g) := by
  have hpair := sortedZeroNeighbors14_pairwise g
  have hrel := hpair.rel_get_of_lt
    (a := ⟨i, by
      rw [sortedZeroNeighbors14_length_of_degreeSix g sixRegular]
      omega⟩)
    (b := ⟨i + 1, by
      rw [sortedZeroNeighbors14_length_of_degreeSix g sixRegular]
      omega⟩)
    (by exact Nat.lt_succ_self i)
  rw [← canonicalVertex14_neighborIndex g sixRegular ⟨i, by omega⟩,
    ← canonicalVertex14_neighborIndex g sixRegular ⟨i + 1, by omega⟩] at hrel
  exact hrel

theorem adjacentCanonicalNonneighborKeys_le (g : BitVec 91)
    (sixRegular : fixedDegreeSequenceUpper (n := 14) g
      [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] = true) (i : Fin 6) :
    nonneighborKey14 g (sortedZeroNeighbors14 g)
        (canonicalVertex14 g ⟨i + 7, by omega⟩) ≤
      nonneighborKey14 g (sortedZeroNeighbors14 g)
        (canonicalVertex14 g ⟨i + 8, by omega⟩) := by
  have hpair := sortedZeroNonneighbors14_pairwise g
  have hrel := hpair.rel_get_of_lt
    (a := ⟨i, by
      rw [sortedZeroNonneighbors14_length_of_degreeSix g sixRegular]
      omega⟩)
    (b := ⟨i + 1, by
      rw [sortedZeroNonneighbors14_length_of_degreeSix g sixRegular]
      omega⟩)
    (by exact Nat.lt_succ_self i)
  rw [← canonicalVertex14_nonneighborIndex g sixRegular ⟨i, by omega⟩,
    ← canonicalVertex14_nonneighborIndex g sixRegular ⟨i + 1, by omega⟩] at hrel
  exact hrel

theorem adjacentCanonicalNeighborDegrees_le (g : BitVec 91)
    (sixRegular : fixedDegreeSequenceUpper (n := 14) g
      [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] = true) (i : Fin 5) :
    degreeCountRange14 (canonicalEncodingFast14 g) (i + 1) 7 7 ≤
      degreeCountRange14 (canonicalEncodingFast14 g) (i + 2) 7 7 := by
  rw [degreeCountRange14_toNonneighbors g ⟨i + 1, by omega⟩,
    degreeCountRange14_toNonneighbors g ⟨i + 2, by omega⟩]
  rw [← sortedZeroNonneighbors14_eq_canonicalNonneighborVertices14 g sixRegular]
  rw [adjCountTo14_sortedNonneighbors_eq_zeroNonneighbors,
    adjCountTo14_sortedNonneighbors_eq_zeroNonneighbors]
  exact adjacentCanonicalNeighborCounts_le g sixRegular i

/-- DP BoolFour value. -/
def dpBoolFourValue (x : BoolFour) : Nat :=
  (if x.b0 then 1 else 0) +
  2 * (if x.b1 then 1 else 0) +
  4 * (if x.b2 then 1 else 0) +
  8 * (if x.b3 then 1 else 0)

theorem dpBoolFourValue_increment_of_lt_fifteen (x : BoolFour) (b : Bool)
    (hx : dpBoolFourValue x < 15) :
    dpBoolFourValue (x.increment b) =
      dpBoolFourValue x + if b then 1 else 0 := by
  rcases x with ⟨b0, b1, b2, b3⟩
  fin_cases b0 <;> fin_cases b1 <;> fin_cases b2 <;> fin_cases b3 <;>
    fin_cases b <;> simp [dpBoolFourValue, BoolFour.increment] at hx ⊢

theorem dpBoolFourValue_foldl_increment {α : Type*} (f : α → Bool) :
    ∀ (xs : List α) (initial : BoolFour),
      dpBoolFourValue initial + xs.length < 16 →
      dpBoolFourValue (xs.foldl (fun bits x => bits.increment (f x)) initial) =
        xs.foldl (fun count x => count + if f x then 1 else 0)
          (dpBoolFourValue initial) := by
  intro xs
  induction xs with
  | nil => intro initial _; simp
  | cons x xs ih =>
      intro initial bound
      simp only [List.foldl_cons, List.length_cons] at bound ⊢
      have initialLt : dpBoolFourValue initial < 15 := by omega
      have incrementValue :=
        dpBoolFourValue_increment_of_lt_fifteen initial (f x) initialLt
      have bitLe : (if f x then 1 else 0) ≤ 1 := by split <;> simp
      have nextBound :
          dpBoolFourValue (initial.increment (f x)) + xs.length < 16 := by
        rw [incrementValue]
        omega
      rw [ih (initial.increment (f x)) nextBound, incrementValue]

theorem degreeBitsRangeUpper_value_eq_count (g : BitVec 91)
    (u start count : Nat) (hcount : count < 16) :
    dpBoolFourValue (degreeBitsRangeUpper g u start count) =
      degreeCountRange14 g u start count := by
  unfold degreeBitsRangeUpper degreeCountRange14
  have folded := dpBoolFourValue_foldl_increment
    (fun offset => adjUpper (n := 14) g u (start + offset)) (List.range count)
      { b0 := false, b1 := false, b2 := false, b3 := false }
  have bound :
      dpBoolFourValue { b0 := false, b1 := false, b2 := false, b3 := false } +
        (List.range count).length < 16 := by
    change 0 + (List.range count).length < 16
    simp only [List.length_range]
    omega
  simpa [dpBoolFourValue] using folded bound

theorem degreeCountRange14_le_count (g : BitVec 91) (u start count : Nat) :
    degreeCountRange14 g u start count ≤ count := by
  unfold degreeCountRange14
  have H :
      (List.range count).foldl (fun acc offset =>
          acc + if adjUpper (n := 14) g u (start + offset) then 1 else 0) 0 =
        (List.range count).countP
          (fun offset => adjUpper (n := 14) g u (start + offset)) := by
    simpa using
      (foldl_count_eq_countP14
        (fun offset => adjUpper (n := 14) g u (start + offset))
        (List.range count) 0)
  rw [H]
  have := List.countP_le_length
    (p := fun offset => adjUpper (n := 14) g u (start + offset))
    (l := List.range count)
  simpa [List.length_range] using this

theorem degreeCountRange14_lt_sixteen (g : BitVec 91) (u start count : Nat)
    (hcount : count < 16) :
    degreeCountRange14 g u start count < 16 :=
  Nat.lt_of_le_of_lt (degreeCountRange14_le_count g u start count) hcount

/-- Finite table: `BoolFour.ofNat` comparison matches `Nat.le` on `0..15`. -/
theorem boolFour_ofNat_le_table :
    (List.range 16).all (fun x =>
      (List.range 16).all (fun y =>
        !((BoolFour.ofNat x).le (BoolFour.ofNat y) ^^ decide (x ≤ y)))) = true := by
  native_decide

theorem boolFour_ofNat_same_table :
    (List.range 16).all (fun x =>
      (List.range 16).all (fun y =>
        !((BoolFour.ofNat x).same (BoolFour.ofNat y) ^^ decide (x = y)))) = true := by
  native_decide

theorem dpBoolFour_le_ofNat (x y : Nat) (hx : x < 16) (hy : y < 16) :
    (BoolFour.ofNat x).le (BoolFour.ofNat y) = decide (x ≤ y) := by
  have hall := boolFour_ofNat_le_table
  have hxmem : x ∈ List.range 16 := List.mem_range.mpr hx
  have hymem : y ∈ List.range 16 := List.mem_range.mpr hy
  have hxall := (List.all_eq_true.mp hall) x hxmem
  have hyall := (List.all_eq_true.mp hxall) y hymem
  -- hyall : !((ofNat x).le (ofNat y) ^^ decide (x ≤ y)) = true
  -- so the two sides are equal
  have : ¬(((BoolFour.ofNat x).le (BoolFour.ofNat y) ^^ decide (x ≤ y)) = true) := by
    simpa using hyall
  cases hle : (BoolFour.ofNat x).le (BoolFour.ofNat y) <;>
    cases hdec : decide (x ≤ y) <;> simp_all

theorem dpBoolFour_same_ofNat (x y : Nat) (hx : x < 16) (hy : y < 16) :
    (BoolFour.ofNat x).same (BoolFour.ofNat y) = decide (x = y) := by
  have hall := boolFour_ofNat_same_table
  have hxmem : x ∈ List.range 16 := List.mem_range.mpr hx
  have hymem : y ∈ List.range 16 := List.mem_range.mpr hy
  have hxall := (List.all_eq_true.mp hall) x hxmem
  have hyall := (List.all_eq_true.mp hxall) y hymem
  have : ¬(((BoolFour.ofNat x).same (BoolFour.ofNat y) ^^ decide (x = y)) = true) := by
    simpa using hyall
  cases hle : (BoolFour.ofNat x).same (BoolFour.ofNat y) <;>
    cases hdec : decide (x = y) <;> simp_all

theorem dpBoolFourValue_ofNat (x : Nat) (hx : x < 16) :
    dpBoolFourValue (BoolFour.ofNat x) = x := by
  interval_cases x <;> native_decide

theorem dpBoolFourValue_injective : Function.Injective dpBoolFourValue := by
  intro a b hab
  rcases a with ⟨a0, a1, a2, a3⟩
  rcases b with ⟨b0, b1, b2, b3⟩
  fin_cases a0 <;> fin_cases a1 <;> fin_cases a2 <;> fin_cases a3 <;>
    fin_cases b0 <;> fin_cases b1 <;> fin_cases b2 <;> fin_cases b3 <;>
    simp [dpBoolFourValue] at hab ⊢ <;> omega

theorem eq_ofNat_dpBoolFourValue (x : BoolFour) :
    x = BoolFour.ofNat (dpBoolFourValue x) := by
  rcases x with ⟨a, b, c, d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> rfl

theorem dpBoolFourValue_lt_sixteen (x : BoolFour) :
    dpBoolFourValue x < 16 := by
  rcases x with ⟨a, b, c, d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [dpBoolFourValue]

/-- BoolFour.le matches Nat.le of the decoded values. -/
theorem dpBoolFour_le_iff_value (x y : BoolFour) :
    x.le y = decide (dpBoolFourValue x ≤ dpBoolFourValue y) := by
  set vx := dpBoolFourValue x
  set vy := dpBoolFourValue y
  have hxlt : vx < 16 := dpBoolFourValue_lt_sixteen x
  have hylt : vy < 16 := dpBoolFourValue_lt_sixteen y
  have hx : x = BoolFour.ofNat vx := eq_ofNat_dpBoolFourValue x
  have hy : y = BoolFour.ofNat vy := eq_ofNat_dpBoolFourValue y
  -- Rewrite only the left-hand comparison, not the values on the right.
  conv_lhs => rw [hx, hy]
  exact dpBoolFour_le_ofNat vx vy hxlt hylt

theorem dpBoolFour_same_iff_value (x y : BoolFour) :
    x.same y = decide (dpBoolFourValue x = dpBoolFourValue y) := by
  set vx := dpBoolFourValue x
  set vy := dpBoolFourValue y
  have hxlt : vx < 16 := dpBoolFourValue_lt_sixteen x
  have hylt : vy < 16 := dpBoolFourValue_lt_sixteen y
  have hx : x = BoolFour.ofNat vx := eq_ofNat_dpBoolFourValue x
  have hy : y = BoolFour.ofNat vy := eq_ofNat_dpBoolFourValue y
  conv_lhs => rw [hx, hy]
  exact dpBoolFour_same_ofNat vx vy hxlt hylt

theorem degreeBitsRangeUpper_le_of_count_le (g : BitVec 91)
    (u v start count : Nat) (hcount : count < 16)
    (hle : degreeCountRange14 g u start count ≤ degreeCountRange14 g v start count) :
    (degreeBitsRangeUpper g u start count).le
      (degreeBitsRangeUpper g v start count) = true := by
  have hu := degreeBitsRangeUpper_value_eq_count g u start count hcount
  have hv := degreeBitsRangeUpper_value_eq_count g v start count hcount
  have hcmp := dpBoolFour_le_iff_value
    (degreeBitsRangeUpper g u start count)
    (degreeBitsRangeUpper g v start count)
  rw [hcmp, hu, hv, decide_eq_true_iff]
  exact hle

theorem degreeBitsRangeUpper_le_eq_decide (g : BitVec 91)
    (u v start count : Nat) (hcount : count < 16) :
    (degreeBitsRangeUpper g u start count).le
        (degreeBitsRangeUpper g v start count) =
      decide (degreeCountRange14 g u start count ≤
        degreeCountRange14 g v start count) := by
  have hu := degreeBitsRangeUpper_value_eq_count g u start count hcount
  have hv := degreeBitsRangeUpper_value_eq_count g v start count hcount
  have hcmp := dpBoolFour_le_iff_value
    (degreeBitsRangeUpper g u start count)
    (degreeBitsRangeUpper g v start count)
  rw [hcmp, hu, hv]

theorem adjacentCanonicalNeighborBoolLe (g : BitVec 91)
    (sixRegular : fixedDegreeSequenceUpper (n := 14) g
      [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] = true) (i : Fin 5) :
    (degreeBitsRangeUpper (canonicalEncodingFast14 g) (i + 1) 7 7).le
      (degreeBitsRangeUpper (canonicalEncodingFast14 g) (i + 2) 7 7) = true := by
  rw [degreeBitsRangeUpper_le_eq_decide (canonicalEncodingFast14 g)
    (↑i + 1) (↑i + 2) 7 7 (by decide : 7 < 16)]
  exact decide_eq_true (adjacentCanonicalNeighborDegrees_le g sixRegular i)

/-- Row code of adjacencies to the six zero-neighbours (LSB = vertex 1). -/
def neighborRowCodeFast14 (g : BitVec 91) (u : Nat) : Nat :=
  (if adjUpper (n := 14) g u 1 then 1 else 0) +
  (if adjUpper (n := 14) g u 2 then 2 else 0) +
  (if adjUpper (n := 14) g u 3 then 4 else 0) +
  (if adjUpper (n := 14) g u 4 then 8 else 0) +
  (if adjUpper (n := 14) g u 5 then 16 else 0) +
  (if adjUpper (n := 14) g u 6 then 32 else 0)

theorem sortedZeroNeighbors14_getD (g : BitVec 91)
    (sixRegular : fixedDegreeSequenceUpper (n := 14) g
      [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] = true) (i : Fin 6) :
    (sortedZeroNeighbors14 g).getD (i : Nat) 0 =
      canonicalVertex14 g ⟨i + 1, by omega⟩ := by
  have hlen : (sortedZeroNeighbors14 g).length = 6 :=
    sortedZeroNeighbors14_length_of_degreeSix g sixRegular
  have hsorted := sortedZeroNeighbors14_eq_canonicalNeighborVertices14 g sixRegular
  have hi : (i : Nat) < (canonicalNeighborVertices14 g).length := by
    simp [canonicalNeighborVertices14, List.length_ofFn]
  have hi' : (i : Nat) < (sortedZeroNeighbors14 g).length := by omega
  rw [List.getD_eq_getElem (l := sortedZeroNeighbors14 g) (d := 0) hi']
  -- After equality of lists, getElem matches ofFn.
  -- Transport along hsorted, then evaluate ofFn.
  have : (sortedZeroNeighbors14 g)[i.val] =
      (canonicalNeighborVertices14 g)[i.val] := by
    simp [hsorted]
  rw [this]
  -- canonicalNeighborVertices14 = ofFn (i ↦ canonicalVertex (i+1))
  change (List.ofFn fun j : Fin 6 =>
      canonicalVertex14 g ⟨j + 1, by omega⟩)[i.val] =
    canonicalVertex14 g ⟨i + 1, by omega⟩
  rw [List.getElem_ofFn]

theorem neighborRowCode14_expand (g : BitVec 91) (neighbors : List (Fin 14))
    (u : Fin 14) :
    neighborRowCode14 g neighbors u =
      (if adjUpper (n := 14) g u (neighbors.getD 0 0) then 1 else 0) +
      (if adjUpper (n := 14) g u (neighbors.getD 1 0) then 2 else 0) +
      (if adjUpper (n := 14) g u (neighbors.getD 2 0) then 4 else 0) +
      (if adjUpper (n := 14) g u (neighbors.getD 3 0) then 8 else 0) +
      (if adjUpper (n := 14) g u (neighbors.getD 4 0) then 16 else 0) +
      (if adjUpper (n := 14) g u (neighbors.getD 5 0) then 32 else 0) := by
  unfold neighborRowCode14
  have hr : List.range 6 = [0, 1, 2, 3, 4, 5] := by native_decide
  rw [hr]
  simp only [List.foldl_cons, List.foldl_nil]
  -- 2^0..2^5 reduce
  norm_num [pow_zero, pow_one, pow_succ]

theorem neighborRowCodeFast14_eq_rowCode (g : BitVec 91) (u : Fin 14)
    (sixRegular : fixedDegreeSequenceUpper (n := 14) g
      [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] = true) :
    neighborRowCodeFast14 (canonicalEncodingFast14 g) u =
      neighborRowCode14 g (sortedZeroNeighbors14 g) (canonicalVertex14 g u) := by
  rw [neighborRowCode14_expand]
  unfold neighborRowCodeFast14
  have get (i : Fin 6) := sortedZeroNeighbors14_getD g sixRegular i
  have adj (i : Fin 6) :
      adjUpper (n := 14) (canonicalEncodingFast14 g) u (i + 1 : Nat) =
        adjUpper (n := 14) g (canonicalVertex14 g u)
          ((sortedZeroNeighbors14 g).getD i 0) := by
    rw [get i]
    exact adjUpper_canonicalEncodingFast14_nat g u (i + 1) u.isLt (by omega)
  simp only [adj ⟨0, by omega⟩, adj ⟨1, by omega⟩, adj ⟨2, by omega⟩,
    adj ⟨3, by omega⟩, adj ⟨4, by omega⟩, adj ⟨5, by omega⟩]

theorem neighborRowCodeFast14_lt_sixtyfour (g : BitVec 91) (u : Nat) :
    neighborRowCodeFast14 g u < 64 := by
  unfold neighborRowCodeFast14
  have h0 : (if adjUpper (n := 14) g u 1 then 1 else 0) ≤ 1 := by split <;> simp
  have h1 : (if adjUpper (n := 14) g u 2 then 2 else 0) ≤ 2 := by split <;> simp
  have h2 : (if adjUpper (n := 14) g u 3 then 4 else 0) ≤ 4 := by split <;> simp
  have h3 : (if adjUpper (n := 14) g u 4 then 8 else 0) ≤ 8 := by split <;> simp
  have h4 : (if adjUpper (n := 14) g u 5 then 16 else 0) ≤ 16 := by split <;> simp
  have h5 : (if adjUpper (n := 14) g u 6 then 32 else 0) ≤ 32 := by split <;> simp
  omega

/-- Finite table: 6-bit MSB-first lex order matches `Nat.le` on `0..63`. -/
theorem bitListLexLe_table :
    (List.range 64).all (fun x =>
      (List.range 64).all (fun y =>
        !(bitListLexLe
            [maskHas x 5, maskHas x 4, maskHas x 3, maskHas x 2, maskHas x 1, maskHas x 0]
            [maskHas y 5, maskHas y 4, maskHas y 3, maskHas y 2, maskHas y 1, maskHas y 0] ^^
          decide (x ≤ y)))) = true := by
  native_decide

theorem bitListLexLe_iff_nat (x y : Nat) (hx : x < 64) (hy : y < 64) :
    bitListLexLe
        [maskHas x 5, maskHas x 4, maskHas x 3, maskHas x 2, maskHas x 1, maskHas x 0]
        [maskHas y 5, maskHas y 4, maskHas y 3, maskHas y 2, maskHas y 1, maskHas y 0] =
      decide (x ≤ y) := by
  have hall := bitListLexLe_table
  have hxmem : x ∈ List.range 64 := List.mem_range.mpr hx
  have hymem : y ∈ List.range 64 := List.mem_range.mpr hy
  have hxall := (List.all_eq_true.mp hall) x hxmem
  have hyall := (List.all_eq_true.mp hxall) y hymem
  have : ¬((bitListLexLe
      [maskHas x 5, maskHas x 4, maskHas x 3, maskHas x 2, maskHas x 1, maskHas x 0]
      [maskHas y 5, maskHas y 4, maskHas y 3, maskHas y 2, maskHas y 1, maskHas y 0] ^^
    decide (x ≤ y)) = true) := by
    simpa using hyall
  cases hle : bitListLexLe
      [maskHas x 5, maskHas x 4, maskHas x 3, maskHas x 2, maskHas x 1, maskHas x 0]
      [maskHas y 5, maskHas y 4, maskHas y 3, maskHas y 2, maskHas y 1, maskHas y 0] <;>
    cases hdec : decide (x ≤ y) <;> simp_all

/-- Extract bit `i` from a 6-bit packed adjacency row. -/
theorem maskHas_neighborRowCode (g : BitVec 91) (u : Nat) (i : Fin 6) :
    maskHas (neighborRowCodeFast14 g u) i =
      adjUpper (n := 14) g u (i + 1) := by
  unfold neighborRowCodeFast14 maskHas
  fin_cases i
  · cases h0 : adjUpper (n := 14) g u 1 <;>
      cases h1 : adjUpper (n := 14) g u 2 <;>
      cases h2 : adjUpper (n := 14) g u 3 <;>
      cases h3 : adjUpper (n := 14) g u 4 <;>
      cases h4 : adjUpper (n := 14) g u 5 <;>
      cases h5 : adjUpper (n := 14) g u 6 <;> native_decide
  · cases h0 : adjUpper (n := 14) g u 1 <;>
      cases h1 : adjUpper (n := 14) g u 2 <;>
      cases h2 : adjUpper (n := 14) g u 3 <;>
      cases h3 : adjUpper (n := 14) g u 4 <;>
      cases h4 : adjUpper (n := 14) g u 5 <;>
      cases h5 : adjUpper (n := 14) g u 6 <;> native_decide
  · cases h0 : adjUpper (n := 14) g u 1 <;>
      cases h1 : adjUpper (n := 14) g u 2 <;>
      cases h2 : adjUpper (n := 14) g u 3 <;>
      cases h3 : adjUpper (n := 14) g u 4 <;>
      cases h4 : adjUpper (n := 14) g u 5 <;>
      cases h5 : adjUpper (n := 14) g u 6 <;> native_decide
  · cases h0 : adjUpper (n := 14) g u 1 <;>
      cases h1 : adjUpper (n := 14) g u 2 <;>
      cases h2 : adjUpper (n := 14) g u 3 <;>
      cases h3 : adjUpper (n := 14) g u 4 <;>
      cases h4 : adjUpper (n := 14) g u 5 <;>
      cases h5 : adjUpper (n := 14) g u 6 <;> native_decide
  · cases h0 : adjUpper (n := 14) g u 1 <;>
      cases h1 : adjUpper (n := 14) g u 2 <;>
      cases h2 : adjUpper (n := 14) g u 3 <;>
      cases h3 : adjUpper (n := 14) g u 4 <;>
      cases h4 : adjUpper (n := 14) g u 5 <;>
      cases h5 : adjUpper (n := 14) g u 6 <;> native_decide
  · cases h0 : adjUpper (n := 14) g u 1 <;>
      cases h1 : adjUpper (n := 14) g u 2 <;>
      cases h2 : adjUpper (n := 14) g u 3 <;>
      cases h3 : adjUpper (n := 14) g u 4 <;>
      cases h4 : adjUpper (n := 14) g u 5 <;>
      cases h5 : adjUpper (n := 14) g u 6 <;> native_decide

theorem adjacencyRow_eq_maskBits (g : BitVec 91) (u : Nat) :
    adjacencyRowToZeroNeighbors14 g u =
      [maskHas (neighborRowCodeFast14 g u) 5,
        maskHas (neighborRowCodeFast14 g u) 4,
        maskHas (neighborRowCodeFast14 g u) 3,
        maskHas (neighborRowCodeFast14 g u) 2,
        maskHas (neighborRowCodeFast14 g u) 1,
        maskHas (neighborRowCodeFast14 g u) 0] := by
  simp only [adjacencyRowToZeroNeighbors14]
  rw [maskHas_neighborRowCode g u ⟨5, by omega⟩,
    maskHas_neighborRowCode g u ⟨4, by omega⟩,
    maskHas_neighborRowCode g u ⟨3, by omega⟩,
    maskHas_neighborRowCode g u ⟨2, by omega⟩,
    maskHas_neighborRowCode g u ⟨1, by omega⟩,
    maskHas_neighborRowCode g u ⟨0, by omega⟩]

theorem nonneighborKey_eq_composite (g : BitVec 91) (u : Fin 14)
    (sixRegular : fixedDegreeSequenceUpper (n := 14) g
      [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] = true) :
    nonneighborKey14 g (sortedZeroNeighbors14 g) (canonicalVertex14 g u) =
      64 * degreeCountRange14 (canonicalEncodingFast14 g) u 1 6 +
        neighborRowCodeFast14 (canonicalEncodingFast14 g) u := by
  unfold nonneighborKey14
  have hdeg :
      adjCountTo14 g (canonicalVertex14 g u) (sortedZeroNeighbors14 g) =
        degreeCountRange14 (canonicalEncodingFast14 g) u 1 6 := by
    rw [sortedZeroNeighbors14_eq_canonicalNeighborVertices14 g sixRegular]
    exact (degreeCountRange14_toNeighbors g u).symm
  rw [hdeg, neighborRowCodeFast14_eq_rowCode g u sixRegular]

theorem nonneighborKeyLe14_of_nat_le (g : BitVec 91) (u v : Nat)
    (hle : 64 * degreeCountRange14 g u 1 6 + neighborRowCodeFast14 g u ≤
      64 * degreeCountRange14 g v 1 6 + neighborRowCodeFast14 g v) :
    nonneighborKeyLe14 g u v = true := by
  unfold nonneighborKeyLe14
  set du := degreeCountRange14 g u 1 6
  set dv := degreeCountRange14 g v 1 6
  set cu := neighborRowCodeFast14 g u
  set cv := neighborRowCodeFast14 g v
  have du_lt : du < 16 := degreeCountRange14_lt_sixteen g u 1 6 (by decide)
  have dv_lt : dv < 16 := degreeCountRange14_lt_sixteen g v 1 6 (by decide)
  have cu_lt : cu < 64 := neighborRowCodeFast14_lt_sixtyfour g u
  have cv_lt : cv < 64 := neighborRowCodeFast14_lt_sixtyfour g v
  have hduVal :
      dpBoolFourValue (degreeBitsRangeUpper g u 1 6) = du :=
    degreeBitsRangeUpper_value_eq_count g u 1 6 (by decide)
  have hdvVal :
      dpBoolFourValue (degreeBitsRangeUpper g v 1 6) = dv :=
    degreeBitsRangeUpper_value_eq_count g v 1 6 (by decide)
  have hdecomp : du < dv ∨ (du = dv ∧ cu ≤ cv) := by
    by_cases hlt : du < dv
    · exact Or.inl hlt
    · have hge : dv ≤ du := Nat.le_of_not_gt hlt
      by_cases heq : du = dv
      · exact Or.inr ⟨heq, by omega⟩
      · have : 64 ≤ cv := by omega
        exact absurd this (Nat.not_le_of_gt cv_lt)
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true]
  rcases hdecomp with hlt | ⟨heq, hcode⟩
  · have hle' : du ≤ dv := Nat.le_of_lt hlt
    have hne : du ≠ dv := Nat.ne_of_lt hlt
    constructor
    · rw [dpBoolFour_le_iff_value, hduVal, hdvVal, decide_eq_true_iff]
      exact hle'
    · left
      rw [dpBoolFour_same_iff_value, hduVal, hdvVal]
      simp [hne]
  · have du_eq_dv : du = dv := heq
    constructor
    · rw [dpBoolFour_le_iff_value, hduVal, hdvVal, decide_eq_true_iff, du_eq_dv]
    · right
      rw [adjacencyRow_eq_maskBits g u, adjacencyRow_eq_maskBits g v]
      change bitListLexLe
          [maskHas cu 5, maskHas cu 4, maskHas cu 3, maskHas cu 2, maskHas cu 1, maskHas cu 0]
          [maskHas cv 5, maskHas cv 4, maskHas cv 3, maskHas cv 2, maskHas cv 1, maskHas cv 0] =
        true
      rw [bitListLexLe_iff_nat cu cv cu_lt cv_lt, decide_eq_true_iff]
      exact hcode

theorem adjacentCanonicalNonneighborKeyLe (g : BitVec 91)
    (sixRegular : fixedDegreeSequenceUpper (n := 14) g
      [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] = true) (i : Fin 6) :
    nonneighborKeyLe14 (canonicalEncodingFast14 g) (i + 7) (i + 8) = true := by
  apply nonneighborKeyLe14_of_nat_le
  have hkey_u := nonneighborKey_eq_composite g ⟨i + 7, by omega⟩ sixRegular
  have hkey_v := nonneighborKey_eq_composite g ⟨i + 8, by omega⟩ sixRegular
  have hle := adjacentCanonicalNonneighborKeys_le g sixRegular i
  rw [← hkey_u, ← hkey_v]
  exact hle

set_option maxRecDepth 100000 in
set_option maxHeartbeats 800000 in
theorem canonicalEncodingFast14_partitionSorted : ∀ g : BitVec 91,
    fixedDegreeSequenceUpper (n := 14) g
      [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] = true →
    canonicalPartitionDegreesSorted14 (canonicalEncodingFast14 g) = true := by
  intro g sixRegular
  have n0 := adjacentCanonicalNeighborBoolLe g sixRegular ⟨0, by omega⟩
  have n1 := adjacentCanonicalNeighborBoolLe g sixRegular ⟨1, by omega⟩
  have n2 := adjacentCanonicalNeighborBoolLe g sixRegular ⟨2, by omega⟩
  have n3 := adjacentCanonicalNeighborBoolLe g sixRegular ⟨3, by omega⟩
  have n4 := adjacentCanonicalNeighborBoolLe g sixRegular ⟨4, by omega⟩
  have k0 := adjacentCanonicalNonneighborKeyLe g sixRegular ⟨0, by omega⟩
  have k1 := adjacentCanonicalNonneighborKeyLe g sixRegular ⟨1, by omega⟩
  have k2 := adjacentCanonicalNonneighborKeyLe g sixRegular ⟨2, by omega⟩
  have k3 := adjacentCanonicalNonneighborKeyLe g sixRegular ⟨3, by omega⟩
  have k4 := adjacentCanonicalNonneighborKeyLe g sixRegular ⟨4, by omega⟩
  have k5 := adjacentCanonicalNonneighborKeyLe g sixRegular ⟨5, by omega⟩
  simp only [canonicalPartitionDegreesSorted14, n0, n1, n2, n3, n4, k0, k1, k2, k3, k4, k5]
  rfl

end WOWII217Relabel
