import WOWII217ClosureSemantics

/-! Exact encoding of simple graphs on `Fin 8` by 28 upper-triangle bits. -/

namespace WOWII217Encoding8

open SimpleGraph
open WOWII217FiniteBase WOWII217Closure WOWII217ClosureSemantics

def fin8Wrap (n : Nat) : Fin 8 :=
  ⟨n % 8, Nat.mod_lt _ (by omega)⟩

theorem fin8Wrap_coe (v : Fin 8) : fin8Wrap v = v := by
  ext
  simp [fin8Wrap, Nat.mod_eq_of_lt v.isLt]

def edgeIndex8 (u v : Nat) : Nat := upperIndex u v

theorem edgeIndex8_lt :
    ∀ (u v : Fin 8), u < v → edgeIndex8 u v < 28 := by
  native_decide

theorem upperPairs8_getD_edgeIndex :
    ∀ (u v : Fin 8), u < v →
      (upperPairs 8).getD (edgeIndex8 u v) (0, 0) =
        ((u : Nat), (v : Nat)) := by
  native_decide

def encodeUpper8 (G : SimpleGraph (Fin 8)) [DecidableRel G.Adj] : BitVec 28 := by
  let bits := List.ofFn fun i : Fin 28 =>
    let edge := (upperPairs 8).getD i (0, 0)
    decide (G.Adj (fin8Wrap edge.1) (fin8Wrap edge.2))
  exact BitVec.cast List.length_ofFn (BitVec.ofBoolListLE bits)

theorem encodeUpper8_getLsbD (G : SimpleGraph (Fin 8)) [DecidableRel G.Adj]
    (u v : Fin 8) (huv : u < v) :
    (encodeUpper8 G).getLsbD (edgeIndex8 u v) = decide (G.Adj u v) := by
  classical
  unfold encodeUpper8
  simp only [BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE]
  let bits := List.ofFn fun i : Fin 28 =>
    let edge := (upperPairs 8).getD i (0, 0)
    decide (G.Adj (fin8Wrap edge.1) (fin8Wrap edge.2))
  change bits.getD (edgeIndex8 u v) false = decide (G.Adj u v)
  have hindex : edgeIndex8 u v < bits.length := by
    rw [List.length_ofFn]
    exact edgeIndex8_lt u v huv
  rw [List.getD_eq_getElem (l := bits) (d := false) hindex]
  rw [List.getElem_ofFn]
  dsimp only
  rw [upperPairs8_getD_edgeIndex u v huv, fin8Wrap_coe, fin8Wrap_coe]

theorem adjUpper_encodeUpper8 (G : SimpleGraph (Fin 8)) [DecidableRel G.Adj]
    (u v : Fin 8) :
    adjUpper (n := 8) (encodeUpper8 G) u v = decide (G.Adj u v) := by
  by_cases huv : (u : Nat) < v
  · simp only [adjUpper, huv, if_true]
    exact encodeUpper8_getLsbD G u v huv
  · by_cases hvu : (v : Nat) < u
    · simp only [adjUpper, huv, if_false, hvu, if_true]
      change (encodeUpper8 G).getLsbD (edgeIndex8 v u) = decide (G.Adj u v)
      rw [encodeUpper8_getLsbD G v u hvu]
      simp only [G.adj_comm]
    · have huvEq : u = v := by
        apply Fin.ext
        omega
      subst v
      simp [adjUpper]

theorem graphOfUpper_encodeUpper8 (G : SimpleGraph (Fin 8))
    [DecidableRel G.Adj] :
    graphOfUpper (n := 8) (encodeUpper8 G) = G := by
  ext u v
  simp only [graphOfUpper, adjUpper_encodeUpper8, decide_eq_true_iff]

end WOWII217Encoding8
