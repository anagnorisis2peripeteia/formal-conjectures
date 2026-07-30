import WOWII217ClosureSemantics

/-! Exact encoding of simple graphs on `Fin 4` by 6 upper-triangle bits. -/

namespace WOWII217Encoding4

open SimpleGraph
open WOWII217FiniteBase WOWII217Closure WOWII217ClosureSemantics

def fin4Wrap (n : Nat) : Fin 4 :=
  ⟨n % 4, Nat.mod_lt _ (by omega)⟩

theorem fin4Wrap_coe (v : Fin 4) : fin4Wrap v = v := by
  ext
  simp [fin4Wrap, Nat.mod_eq_of_lt v.isLt]

def edgeIndex4 (u v : Nat) : Nat := upperIndex u v

theorem edgeIndex4_lt :
    ∀ (u v : Fin 4), u < v → edgeIndex4 u v < 6 := by
  native_decide

theorem upperPairs4_getD_edgeIndex :
    ∀ (u v : Fin 4), u < v →
      (upperPairs 4).getD (edgeIndex4 u v) (0, 0) =
        ((u : Nat), (v : Nat)) := by
  native_decide

def encodeUpper4 (G : SimpleGraph (Fin 4)) [DecidableRel G.Adj] : BitVec 6 := by
  let bits := List.ofFn fun i : Fin 6 =>
    let edge := (upperPairs 4).getD i (0, 0)
    decide (G.Adj (fin4Wrap edge.1) (fin4Wrap edge.2))
  exact BitVec.cast List.length_ofFn (BitVec.ofBoolListLE bits)

theorem encodeUpper4_getLsbD (G : SimpleGraph (Fin 4)) [DecidableRel G.Adj]
    (u v : Fin 4) (huv : u < v) :
    (encodeUpper4 G).getLsbD (edgeIndex4 u v) = decide (G.Adj u v) := by
  classical
  unfold encodeUpper4
  simp only [BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE]
  let bits := List.ofFn fun i : Fin 6 =>
    let edge := (upperPairs 4).getD i (0, 0)
    decide (G.Adj (fin4Wrap edge.1) (fin4Wrap edge.2))
  change bits.getD (edgeIndex4 u v) false = decide (G.Adj u v)
  have hindex : edgeIndex4 u v < bits.length := by
    rw [List.length_ofFn]
    exact edgeIndex4_lt u v huv
  rw [List.getD_eq_getElem (l := bits) (d := false) hindex]
  rw [List.getElem_ofFn]
  dsimp only
  rw [upperPairs4_getD_edgeIndex u v huv, fin4Wrap_coe, fin4Wrap_coe]

theorem adjUpper_encodeUpper4 (G : SimpleGraph (Fin 4)) [DecidableRel G.Adj]
    (u v : Fin 4) :
    adjUpper (n := 4) (encodeUpper4 G) u v = decide (G.Adj u v) := by
  by_cases huv : (u : Nat) < v
  · simp only [adjUpper, huv, if_true]
    exact encodeUpper4_getLsbD G u v huv
  · by_cases hvu : (v : Nat) < u
    · simp only [adjUpper, huv, if_false, hvu, if_true]
      change (encodeUpper4 G).getLsbD (edgeIndex4 v u) = decide (G.Adj u v)
      rw [encodeUpper4_getLsbD G v u hvu]
      simp only [G.adj_comm]
    · have huvEq : u = v := by
        apply Fin.ext
        omega
      subst v
      simp [adjUpper]

theorem graphOfUpper_encodeUpper4 (G : SimpleGraph (Fin 4))
    [DecidableRel G.Adj] :
    graphOfUpper (n := 4) (encodeUpper4 G) = G := by
  ext u v
  simp only [graphOfUpper, adjUpper_encodeUpper4, decide_eq_true_iff]

end WOWII217Encoding4
