import WOWII217ClosureSemantics

/-! Exact encoding of simple graphs on `Fin 10` by 45 upper-triangle bits. -/

namespace WOWII217Encoding10

open SimpleGraph
open WOWII217FiniteBase WOWII217Closure WOWII217ClosureSemantics

def fin10Wrap (n : Nat) : Fin 10 :=
  ⟨n % 10, Nat.mod_lt _ (by omega)⟩

theorem fin10Wrap_coe (v : Fin 10) : fin10Wrap v = v := by
  ext
  simp [fin10Wrap, Nat.mod_eq_of_lt v.isLt]

def edgeIndex10 (u v : Nat) : Nat := upperIndex u v

theorem edgeIndex10_lt :
    ∀ (u v : Fin 10), u < v → edgeIndex10 u v < 45 := by
  native_decide

theorem upperPairs10_getD_edgeIndex :
    ∀ (u v : Fin 10), u < v →
      (upperPairs 10).getD (edgeIndex10 u v) (0, 0) =
        ((u : Nat), (v : Nat)) := by
  native_decide

def encodeUpper10 (G : SimpleGraph (Fin 10)) [DecidableRel G.Adj] : BitVec 45 := by
  let bits := List.ofFn fun i : Fin 45 =>
    let edge := (upperPairs 10).getD i (0, 0)
    decide (G.Adj (fin10Wrap edge.1) (fin10Wrap edge.2))
  exact BitVec.cast List.length_ofFn (BitVec.ofBoolListLE bits)

theorem encodeUpper10_getLsbD (G : SimpleGraph (Fin 10)) [DecidableRel G.Adj]
    (u v : Fin 10) (huv : u < v) :
    (encodeUpper10 G).getLsbD (edgeIndex10 u v) = decide (G.Adj u v) := by
  classical
  unfold encodeUpper10
  simp only [BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE]
  let bits := List.ofFn fun i : Fin 45 =>
    let edge := (upperPairs 10).getD i (0, 0)
    decide (G.Adj (fin10Wrap edge.1) (fin10Wrap edge.2))
  change bits.getD (edgeIndex10 u v) false = decide (G.Adj u v)
  have hindex : edgeIndex10 u v < bits.length := by
    rw [List.length_ofFn]
    exact edgeIndex10_lt u v huv
  rw [List.getD_eq_getElem (l := bits) (d := false) hindex]
  rw [List.getElem_ofFn]
  dsimp only
  rw [upperPairs10_getD_edgeIndex u v huv, fin10Wrap_coe, fin10Wrap_coe]

theorem adjUpper_encodeUpper10 (G : SimpleGraph (Fin 10)) [DecidableRel G.Adj]
    (u v : Fin 10) :
    adjUpper (n := 10) (encodeUpper10 G) u v = decide (G.Adj u v) := by
  by_cases huv : (u : Nat) < v
  · simp only [adjUpper, huv, if_true]
    exact encodeUpper10_getLsbD G u v huv
  · by_cases hvu : (v : Nat) < u
    · simp only [adjUpper, huv, if_false, hvu, if_true]
      change (encodeUpper10 G).getLsbD (edgeIndex10 v u) = decide (G.Adj u v)
      rw [encodeUpper10_getLsbD G v u hvu]
      simp only [G.adj_comm]
    · have huvEq : u = v := by
        apply Fin.ext
        omega
      subst v
      simp [adjUpper]

theorem graphOfUpper_encodeUpper10 (G : SimpleGraph (Fin 10))
    [DecidableRel G.Adj] :
    graphOfUpper (n := 10) (encodeUpper10 G) = G := by
  ext u v
  simp only [graphOfUpper, adjUpper_encodeUpper10, decide_eq_true_iff]

end WOWII217Encoding10
