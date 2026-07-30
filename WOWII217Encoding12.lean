import WOWII217ClosureSemantics

/-! Exact encoding of simple graphs on `Fin 12` by 66 upper-triangle bits. -/

namespace WOWII217Encoding12

open SimpleGraph
open WOWII217FiniteBase WOWII217Closure WOWII217ClosureSemantics

def fin12Wrap (n : Nat) : Fin 12 :=
  ⟨n % 12, Nat.mod_lt _ (by omega)⟩

theorem fin12Wrap_coe (v : Fin 12) : fin12Wrap v = v := by
  ext
  simp [fin12Wrap, Nat.mod_eq_of_lt v.isLt]

def edgeIndex12 (u v : Nat) : Nat := upperIndex u v

theorem edgeIndex12_lt :
    ∀ (u v : Fin 12), u < v → edgeIndex12 u v < 66 := by
  native_decide

theorem upperPairs12_getD_edgeIndex :
    ∀ (u v : Fin 12), u < v →
      (upperPairs 12).getD (edgeIndex12 u v) (0, 0) =
        ((u : Nat), (v : Nat)) := by
  native_decide

def encodeUpper12 (G : SimpleGraph (Fin 12)) [DecidableRel G.Adj] : BitVec 66 := by
  let bits := List.ofFn fun i : Fin 66 =>
    let edge := (upperPairs 12).getD i (0, 0)
    decide (G.Adj (fin12Wrap edge.1) (fin12Wrap edge.2))
  exact BitVec.cast List.length_ofFn (BitVec.ofBoolListLE bits)

theorem encodeUpper12_getLsbD (G : SimpleGraph (Fin 12)) [DecidableRel G.Adj]
    (u v : Fin 12) (huv : u < v) :
    (encodeUpper12 G).getLsbD (edgeIndex12 u v) = decide (G.Adj u v) := by
  classical
  unfold encodeUpper12
  simp only [BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE]
  let bits := List.ofFn fun i : Fin 66 =>
    let edge := (upperPairs 12).getD i (0, 0)
    decide (G.Adj (fin12Wrap edge.1) (fin12Wrap edge.2))
  change bits.getD (edgeIndex12 u v) false = decide (G.Adj u v)
  have hindex : edgeIndex12 u v < bits.length := by
    rw [List.length_ofFn]
    exact edgeIndex12_lt u v huv
  rw [List.getD_eq_getElem (l := bits) (d := false) hindex]
  rw [List.getElem_ofFn]
  dsimp only
  rw [upperPairs12_getD_edgeIndex u v huv, fin12Wrap_coe, fin12Wrap_coe]

theorem adjUpper_encodeUpper12 (G : SimpleGraph (Fin 12)) [DecidableRel G.Adj]
    (u v : Fin 12) :
    adjUpper (n := 12) (encodeUpper12 G) u v = decide (G.Adj u v) := by
  by_cases huv : (u : Nat) < v
  · simp only [adjUpper, huv, if_true]
    exact encodeUpper12_getLsbD G u v huv
  · by_cases hvu : (v : Nat) < u
    · simp only [adjUpper, huv, if_false, hvu, if_true]
      change (encodeUpper12 G).getLsbD (edgeIndex12 v u) = decide (G.Adj u v)
      rw [encodeUpper12_getLsbD G v u hvu]
      simp only [G.adj_comm]
    · have huvEq : u = v := by
        apply Fin.ext
        omega
      subst v
      simp [adjUpper]

theorem graphOfUpper_encodeUpper12 (G : SimpleGraph (Fin 12))
    [DecidableRel G.Adj] :
    graphOfUpper (n := 12) (encodeUpper12 G) = G := by
  ext u v
  simp only [graphOfUpper, adjUpper_encodeUpper12, decide_eq_true_iff]

end WOWII217Encoding12
