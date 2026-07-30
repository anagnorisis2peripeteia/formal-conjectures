import WOWII217Encoding12

/-! The canonical vertex order and its graph/bitvector encodings for order 12. -/

namespace WOWII217Relabel12

open SimpleGraph
open WOWII217FiniteBase WOWII217Closure WOWII217ClosureSemantics
open WOWII217Encoding12

def nonzeroVertices12 : List (Fin 12) :=
  [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

def zeroNeighbors12 (g : BitVec 66) : List (Fin 12) :=
  nonzeroVertices12.filter fun v => adjUpper (n := 12) g 0 v

def zeroNonneighbors12 (g : BitVec 66) : List (Fin 12) :=
  nonzeroVertices12.filter fun v => !adjUpper (n := 12) g 0 v

def adjCountTo12 (g : BitVec 66) (u : Fin 12) (vs : List (Fin 12)) : Nat :=
  vs.foldl (fun count v =>
    count + if adjUpper (n := 12) g u v then 1 else 0) 0

def sortedZeroNeighbors12 (g : BitVec 66) : List (Fin 12) :=
  (zeroNeighbors12 g).insertionSort fun u v =>
    adjCountTo12 g u (zeroNonneighbors12 g) ≤
      adjCountTo12 g v (zeroNonneighbors12 g)

def sortedZeroNonneighbors12 (g : BitVec 66) : List (Fin 12) :=
  let neighbors := sortedZeroNeighbors12 g
  (zeroNonneighbors12 g).insertionSort fun u v =>
    adjCountTo12 g u neighbors ≤ adjCountTo12 g v neighbors

def canonicalOrder12 (g : BitVec 66) : List (Fin 12) :=
  0 :: sortedZeroNeighbors12 g ++ sortedZeroNonneighbors12 g

theorem zeroBlocks_perm_nonzeroVertices12 (g : BitVec 66) :
    (zeroNeighbors12 g ++ zeroNonneighbors12 g).Perm nonzeroVertices12 := by
  exact List.filter_append_perm
    (fun v : Fin 12 => adjUpper (n := 12) g 0 v)
    nonzeroVertices12

theorem sortedBlocks_perm_nonzeroVertices12 (g : BitVec 66) :
    (sortedZeroNeighbors12 g ++ sortedZeroNonneighbors12 g).Perm
      nonzeroVertices12 := by
  apply List.Perm.trans (List.Perm.append
    (List.perm_insertionSort
      (fun u v : Fin 12 =>
        adjCountTo12 g u (zeroNonneighbors12 g) ≤
          adjCountTo12 g v (zeroNonneighbors12 g))
      (zeroNeighbors12 g))
    (List.perm_insertionSort
      (fun u v : Fin 12 =>
        adjCountTo12 g u (sortedZeroNeighbors12 g) ≤
          adjCountTo12 g v (sortedZeroNeighbors12 g))
      (zeroNonneighbors12 g)))
  exact zeroBlocks_perm_nonzeroVertices12 g

theorem zero_cons_nonzeroVertices12 :
    (0 : Fin 12) :: nonzeroVertices12 = List.finRange 12 := by
  native_decide

theorem canonicalOrder12_perm_finRange (g : BitVec 66) :
    (canonicalOrder12 g).Perm (List.finRange 12) := by
  rw [canonicalOrder12]
  exact (sortedBlocks_perm_nonzeroVertices12 g).cons 0 |>.trans
    (List.Perm.of_eq zero_cons_nonzeroVertices12)

theorem canonicalOrder12_length (g : BitVec 66) :
    (canonicalOrder12 g).length = 12 := by
  simpa using (canonicalOrder12_perm_finRange g).length_eq

theorem canonicalOrder12_nodup (g : BitVec 66) :
    (canonicalOrder12 g).Nodup :=
  (canonicalOrder12_perm_finRange g).nodup_iff.mpr (List.nodup_finRange 12)

theorem mem_canonicalOrder12 (g : BitVec 66) (v : Fin 12) :
    v ∈ canonicalOrder12 g := by
  exact (canonicalOrder12_perm_finRange g).mem_iff.mpr (List.mem_finRange v)

def canonicalEquiv12 (g : BitVec 66) : Fin 12 ≃ Fin 12 :=
  (finCongr (canonicalOrder12_length g)).symm |>.trans
    ((canonicalOrder12_nodup g).getEquivOfForallMemList
      (canonicalOrder12 g) (mem_canonicalOrder12 g))

def canonicalVertex12 (g : BitVec 66) (i : Fin 12) : Fin 12 :=
  (canonicalOrder12 g).get
    ⟨i, by rw [canonicalOrder12_length]; exact i.isLt⟩

theorem canonicalEquiv12_apply (g : BitVec 66) (i : Fin 12) :
    canonicalEquiv12 g i = canonicalVertex12 g i := by
  rfl

def canonicalEncodingFast12 (g : BitVec 66) : BitVec 66 :=
  BitVec.ofFnLE fun i : Fin 66 =>
    let edge := (upperPairs 12).getD i (0, 0)
    adjUpper (n := 12) g
      (canonicalVertex12 g (fin12Wrap edge.1))
      (canonicalVertex12 g (fin12Wrap edge.2))

theorem canonicalEncodingFast12_getLsbD (g : BitVec 66)
    (u v : Fin 12) (huv : u < v) :
    (canonicalEncodingFast12 g).getLsbD (edgeIndex12 u v) =
      adjUpper (n := 12) g (canonicalVertex12 g u) (canonicalVertex12 g v) := by
  unfold canonicalEncodingFast12
  simp only [BitVec.getLsbD_ofFnLE]
  simp only [edgeIndex12_lt u v huv, dite_true]
  rw [upperPairs12_getD_edgeIndex u v huv, fin12Wrap_coe, fin12Wrap_coe]

theorem adjUpper_canonicalEncodingFast12 (g : BitVec 66) (u v : Fin 12) :
    adjUpper (n := 12) (canonicalEncodingFast12 g) u v =
      adjUpper (n := 12) g (canonicalVertex12 g u) (canonicalVertex12 g v) := by
  by_cases huv : (u : Nat) < v
  · simp only [adjUpper, huv, if_true]
    exact canonicalEncodingFast12_getLsbD g u v huv
  · by_cases hvu : (v : Nat) < u
    · simp only [adjUpper, huv, if_false, hvu, if_true]
      change (canonicalEncodingFast12 g).getLsbD (edgeIndex12 v u) =
        adjUpper (n := 12) g (canonicalVertex12 g u) (canonicalVertex12 g v)
      rw [canonicalEncodingFast12_getLsbD g v u hvu]
      exact adjUpper_comm (n := 12) g _ _
    · have huvEq : u = v := by
        apply Fin.ext
        omega
      subst v
      simp [adjUpper]

def canonicalGraph12 (g : BitVec 66) : SimpleGraph (Fin 12) :=
  (graphOfUpper (n := 12) g).comap (canonicalEquiv12 g).toEmbedding

def canonicalEncoding12 (g : BitVec 66) : BitVec 66 := by
  letI : DecidableRel (canonicalGraph12 g).Adj := fun u v => by
    change Decidable
      (adjUpper (n := 12) g
        (canonicalEquiv12 g u) (canonicalEquiv12 g v) = true)
    infer_instance
  exact encodeUpper12 (canonicalGraph12 g)

theorem canonicalEncodingFast12_eq (g : BitVec 66) :
    canonicalEncodingFast12 g = canonicalEncoding12 g := by
  letI : DecidableRel (canonicalGraph12 g).Adj := fun u v => by
    change Decidable
      (adjUpper (n := 12) g
        (canonicalEquiv12 g u) (canonicalEquiv12 g v) = true)
    infer_instance
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro i hi
  unfold canonicalEncodingFast12 canonicalEncoding12 encodeUpper12
  simp only [BitVec.getLsbD_ofFnLE, BitVec.getLsbD_cast,
    BitVec.getLsbD_ofBoolListLE, hi]
  let edge := (upperPairs 12).getD i (0, 0)
  let bits := List.ofFn fun j : Fin 66 =>
    let pair := (upperPairs 12).getD j (0, 0)
    decide ((canonicalGraph12 g).Adj
      (fin12Wrap pair.1) (fin12Wrap pair.2))
  change
    adjUpper (n := 12) g
        (canonicalVertex12 g (fin12Wrap edge.1))
        (canonicalVertex12 g (fin12Wrap edge.2)) =
      bits.getD i false
  have hindex : i < bits.length := by
    rw [List.length_ofFn]
    exact hi
  rw [List.getD_eq_getElem (l := bits) (d := false) hindex]
  rw [List.getElem_ofFn]
  simp only [edge, canonicalGraph12, SimpleGraph.comap_adj,
    graphOfUpper]
  exact (Bool.decide_coe
    (adjUpper (n := 12) g
      (canonicalVertex12 g (fin12Wrap ((upperPairs 12).getD i (0, 0)).1))
      (canonicalVertex12 g (fin12Wrap ((upperPairs 12).getD i (0, 0)).2)))).symm

def canonicalIso12 (g : BitVec 66) :
    canonicalGraph12 g ≃g graphOfUpper (n := 12) g :=
  SimpleGraph.Iso.comap (canonicalEquiv12 g) (graphOfUpper (n := 12) g)

theorem graphOfUpper_canonicalEncoding12 (g : BitVec 66) :
    graphOfUpper (n := 12) (canonicalEncoding12 g) = canonicalGraph12 g := by
  letI : DecidableRel (canonicalGraph12 g).Adj := fun u v => by
    change Decidable
      (adjUpper (n := 12) g
        (canonicalEquiv12 g u) (canonicalEquiv12 g v) = true)
    infer_instance
  unfold canonicalEncoding12
  exact graphOfUpper_encodeUpper12 (canonicalGraph12 g)

end WOWII217Relabel12
