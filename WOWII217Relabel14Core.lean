import WOWII217Encoding
import WOWII217DP
import WOWII217Semantics

/-! The canonical vertex order and its graph/bitvector encodings for order 14. -/

namespace WOWII217Relabel

open SimpleGraph
open WOWII217DP
open WOWII217Encoding
open WOWII217Semantics (graphOfUpper14)

def nonzeroVertices14 : List (Fin 14) :=
  [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]

def zeroNeighbors14 (g : BitVec 91) : List (Fin 14) :=
  nonzeroVertices14.filter fun v => adjUpper (n := 14) g 0 v

def zeroNonneighbors14 (g : BitVec 91) : List (Fin 14) :=
  nonzeroVertices14.filter fun v => !adjUpper (n := 14) g 0 v

def adjCountTo14 (g : BitVec 91) (u : Fin 14) (vs : List (Fin 14)) : Nat :=
  vs.foldl (fun count (v : Fin 14) =>
    count + if adjUpper (n := 14) g u.val v.val then 1 else 0) 0

def sortedZeroNeighbors14 (g : BitVec 91) : List (Fin 14) :=
  (zeroNeighbors14 g).insertionSort fun u v =>
    adjCountTo14 g u (zeroNonneighbors14 g) ≤
      adjCountTo14 g v (zeroNonneighbors14 g)

def neighborRowCode14 (g : BitVec 91) (neighbors : List (Fin 14))
    (u : Fin 14) : Nat :=
  (List.range 6).foldl (fun code i =>
    code + if adjUpper (n := 14) g u (neighbors.getD i 0) then 2 ^ i else 0) 0

def nonneighborKey14 (g : BitVec 91) (neighbors : List (Fin 14))
    (u : Fin 14) : Nat :=
  64 * adjCountTo14 g u neighbors + neighborRowCode14 g neighbors u

def sortedZeroNonneighbors14 (g : BitVec 91) : List (Fin 14) :=
  let neighbors := sortedZeroNeighbors14 g
  (zeroNonneighbors14 g).insertionSort fun u v =>
    nonneighborKey14 g neighbors u ≤ nonneighborKey14 g neighbors v

def canonicalOrder14 (g : BitVec 91) : List (Fin 14) :=
  0 :: sortedZeroNeighbors14 g ++ sortedZeroNonneighbors14 g

theorem zeroBlocks_perm_nonzeroVertices14 (g : BitVec 91) :
    (zeroNeighbors14 g ++ zeroNonneighbors14 g).Perm nonzeroVertices14 := by
  exact List.filter_append_perm
    (fun v : Fin 14 => adjUpper (n := 14) g 0 v)
    nonzeroVertices14

theorem sortedBlocks_perm_nonzeroVertices14 (g : BitVec 91) :
    (sortedZeroNeighbors14 g ++ sortedZeroNonneighbors14 g).Perm
      nonzeroVertices14 := by
  apply List.Perm.trans (List.Perm.append
    (List.perm_insertionSort
      (fun u v : Fin 14 =>
        adjCountTo14 g u (zeroNonneighbors14 g) ≤
          adjCountTo14 g v (zeroNonneighbors14 g))
      (zeroNeighbors14 g))
    (List.perm_insertionSort
      (fun u v : Fin 14 =>
        nonneighborKey14 g (sortedZeroNeighbors14 g) u ≤
          nonneighborKey14 g (sortedZeroNeighbors14 g) v)
      (zeroNonneighbors14 g)))
  exact zeroBlocks_perm_nonzeroVertices14 g

theorem zero_cons_nonzeroVertices14 :
    (0 : Fin 14) :: nonzeroVertices14 = List.finRange 14 := by
  native_decide

theorem canonicalOrder14_perm_finRange (g : BitVec 91) :
    (canonicalOrder14 g).Perm (List.finRange 14) := by
  rw [canonicalOrder14]
  exact (sortedBlocks_perm_nonzeroVertices14 g).cons 0 |>.trans
    (List.Perm.of_eq zero_cons_nonzeroVertices14)

theorem canonicalOrder14_length (g : BitVec 91) :
    (canonicalOrder14 g).length = 14 := by
  simpa using (canonicalOrder14_perm_finRange g).length_eq

theorem canonicalOrder14_nodup (g : BitVec 91) :
    (canonicalOrder14 g).Nodup :=
  (canonicalOrder14_perm_finRange g).nodup_iff.mpr (List.nodup_finRange 14)

theorem mem_canonicalOrder14 (g : BitVec 91) (v : Fin 14) :
    v ∈ canonicalOrder14 g := by
  exact (canonicalOrder14_perm_finRange g).mem_iff.mpr (List.mem_finRange v)

def canonicalEquiv14 (g : BitVec 91) : Fin 14 ≃ Fin 14 :=
  (finCongr (canonicalOrder14_length g)).symm |>.trans
    ((canonicalOrder14_nodup g).getEquivOfForallMemList
      (canonicalOrder14 g) (mem_canonicalOrder14 g))

def canonicalVertex14 (g : BitVec 91) (i : Fin 14) : Fin 14 :=
  (canonicalOrder14 g).get
    ⟨i, by rw [canonicalOrder14_length]; exact i.isLt⟩

theorem canonicalEquiv14_apply (g : BitVec 91) (i : Fin 14) :
    canonicalEquiv14 g i = canonicalVertex14 g i := by
  rfl

theorem adjUpper_comm14 (g : BitVec 91) (u v : Nat) :
    adjUpper (n := 14) g u v = adjUpper (n := 14) g v u := by
  by_cases huv : u < v
  · have hvu : ¬ v < u := Nat.not_lt_of_ge (Nat.le_of_lt huv)
    simp [adjUpper, huv, hvu]
  · by_cases hvu : v < u
    · simp [adjUpper, huv, hvu]
    · have huvEq : u = v :=
        Nat.le_antisymm (Nat.le_of_not_gt hvu) (Nat.le_of_not_gt huv)
      subst v
      simp [adjUpper]

def canonicalEncodingFast14 (g : BitVec 91) : BitVec 91 :=
  BitVec.ofFnLE fun i : Fin 91 =>
    let edge := upperPairs14.getD i (0, 0)
    adjUpper (n := 14) g
      (canonicalVertex14 g (fin14Wrap edge.1))
      (canonicalVertex14 g (fin14Wrap edge.2))

theorem canonicalEncodingFast14_getLsbD (g : BitVec 91)
    (u v : Fin 14) (huv : u < v) :
    (canonicalEncodingFast14 g).getLsbD (edgeIndex14 u v) =
      adjUpper (n := 14) g (canonicalVertex14 g u) (canonicalVertex14 g v) := by
  unfold canonicalEncodingFast14
  simp only [BitVec.getLsbD_ofFnLE]
  simp only [edgeIndex14_lt u v huv, dite_true]
  rw [upperPairs14_getD_edgeIndex u v huv, fin14Wrap_coe, fin14Wrap_coe]

theorem adjUpper_canonicalEncodingFast14 (g : BitVec 91) (u v : Fin 14) :
    adjUpper (n := 14) (canonicalEncodingFast14 g) u v =
      adjUpper (n := 14) g (canonicalVertex14 g u) (canonicalVertex14 g v) := by
  by_cases huv : (u : Nat) < v
  · simp only [adjUpper, huv, if_true]
    exact canonicalEncodingFast14_getLsbD g u v huv
  · by_cases hvu : (v : Nat) < u
    · simp only [adjUpper, huv, if_false, hvu, if_true]
      change (canonicalEncodingFast14 g).getLsbD (edgeIndex14 v u) =
        adjUpper (n := 14) g (canonicalVertex14 g u) (canonicalVertex14 g v)
      rw [canonicalEncodingFast14_getLsbD g v u hvu]
      exact adjUpper_comm14 g _ _
    · have huvEq : u = v := by
        apply Fin.ext
        omega
      subst v
      simp [adjUpper]

def canonicalGraph14 (g : BitVec 91) : SimpleGraph (Fin 14) :=
  (graphOfUpper14 g).comap (canonicalEquiv14 g).toEmbedding

def canonicalEncoding14 (g : BitVec 91) : BitVec 91 := by
  letI : DecidableRel (canonicalGraph14 g).Adj := fun u v => by
    change Decidable
      (WOWII217Semantics.adjUpper (n := 14) g
        (canonicalEquiv14 g u) (canonicalEquiv14 g v) = true)
    infer_instance
  exact encodeUpper14 (canonicalGraph14 g)

theorem adjUpper_semantics_eq_dp (g : BitVec 91) (u v : Nat) :
    WOWII217Semantics.adjUpper (n := 14) g u v =
      adjUpper (n := 14) g u v := rfl

theorem canonicalEncodingFast14_eq (g : BitVec 91) :
    canonicalEncodingFast14 g = canonicalEncoding14 g := by
  letI : DecidableRel (canonicalGraph14 g).Adj := fun u v => by
    change Decidable
      (WOWII217Semantics.adjUpper (n := 14) g
        (canonicalEquiv14 g u) (canonicalEquiv14 g v) = true)
    infer_instance
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro i hi
  unfold canonicalEncodingFast14 canonicalEncoding14 encodeUpper14
  simp only [BitVec.getLsbD_ofFnLE, BitVec.getLsbD_cast,
    BitVec.getLsbD_ofBoolListLE, hi]
  let edge := upperPairs14.getD i (0, 0)
  let bits := List.ofFn fun j : Fin 91 =>
    let pair := upperPairs14.getD j (0, 0)
    decide ((canonicalGraph14 g).Adj
      (fin14Wrap pair.1) (fin14Wrap pair.2))
  change
    adjUpper (n := 14) g
        (canonicalVertex14 g (fin14Wrap edge.1))
        (canonicalVertex14 g (fin14Wrap edge.2)) =
      bits.getD i false
  have hindex : i < bits.length := by
    rw [List.length_ofFn]
    exact hi
  rw [List.getD_eq_getElem (l := bits) (d := false) hindex]
  rw [List.getElem_ofFn]
  simp only [edge, canonicalGraph14, SimpleGraph.comap_adj,
    graphOfUpper14]
  rw [adjUpper_semantics_eq_dp]
  exact (Bool.decide_coe
    (adjUpper (n := 14) g
      (canonicalVertex14 g (fin14Wrap (upperPairs14.getD i (0, 0)).1))
      (canonicalVertex14 g (fin14Wrap (upperPairs14.getD i (0, 0)).2)))).symm

def canonicalIso14 (g : BitVec 91) :
    canonicalGraph14 g ≃g graphOfUpper14 g :=
  SimpleGraph.Iso.comap (canonicalEquiv14 g) (graphOfUpper14 g)

theorem graphOfUpper14_canonicalEncoding14 (g : BitVec 91) :
    graphOfUpper14 (canonicalEncoding14 g) = canonicalGraph14 g := by
  letI : DecidableRel (canonicalGraph14 g).Adj := fun u v => by
    change Decidable
      (WOWII217Semantics.adjUpper (n := 14) g
        (canonicalEquiv14 g u) (canonicalEquiv14 g v) = true)
    infer_instance
  unfold canonicalEncoding14
  exact graphOfUpper14_encodeUpper14 (canonicalGraph14 g)

end WOWII217Relabel
