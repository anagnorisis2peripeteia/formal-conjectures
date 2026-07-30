import WOWII217ClosureSemantics

/-! Exact encoding of simple graphs on `Fin 11` by 55 upper-triangle bits. -/

namespace WOWII217Encoding11

open SimpleGraph
open WOWII217FiniteBase WOWII217Closure WOWII217ClosureSemantics

def fin11Wrap (n : Nat) : Fin 11 :=
  ⟨n % 11, Nat.mod_lt _ (by omega)⟩

theorem fin11Wrap_coe (v : Fin 11) : fin11Wrap v = v := by
  ext
  simp [fin11Wrap, Nat.mod_eq_of_lt v.isLt]

def edgeIndex11 (u v : Nat) : Nat := upperIndex u v

theorem edgeIndex11_lt :
    ∀ (u v : Fin 11), u < v → edgeIndex11 u v < 55 := by
  native_decide

theorem upperPairs11_getD_edgeIndex :
    ∀ (u v : Fin 11), u < v →
      (upperPairs 11).getD (edgeIndex11 u v) (0, 0) =
        ((u : Nat), (v : Nat)) := by
  native_decide

def encodeUpper11 (G : SimpleGraph (Fin 11)) [DecidableRel G.Adj] : BitVec 55 := by
  let bits := List.ofFn fun i : Fin 55 =>
    let edge := (upperPairs 11).getD i (0, 0)
    decide (G.Adj (fin11Wrap edge.1) (fin11Wrap edge.2))
  exact BitVec.cast List.length_ofFn (BitVec.ofBoolListLE bits)

theorem encodeUpper11_getLsbD (G : SimpleGraph (Fin 11)) [DecidableRel G.Adj]
    (u v : Fin 11) (huv : u < v) :
    (encodeUpper11 G).getLsbD (edgeIndex11 u v) = decide (G.Adj u v) := by
  classical
  unfold encodeUpper11
  simp only [BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE]
  let bits := List.ofFn fun i : Fin 55 =>
    let edge := (upperPairs 11).getD i (0, 0)
    decide (G.Adj (fin11Wrap edge.1) (fin11Wrap edge.2))
  change bits.getD (edgeIndex11 u v) false = decide (G.Adj u v)
  have hindex : edgeIndex11 u v < bits.length := by
    rw [List.length_ofFn]
    exact edgeIndex11_lt u v huv
  rw [List.getD_eq_getElem (l := bits) (d := false) hindex]
  rw [List.getElem_ofFn]
  dsimp only
  rw [upperPairs11_getD_edgeIndex u v huv, fin11Wrap_coe, fin11Wrap_coe]

theorem adjUpper_encodeUpper11 (G : SimpleGraph (Fin 11)) [DecidableRel G.Adj]
    (u v : Fin 11) :
    adjUpper (n := 11) (encodeUpper11 G) u v = decide (G.Adj u v) := by
  by_cases huv : (u : Nat) < v
  · simp only [adjUpper, huv, if_true]
    exact encodeUpper11_getLsbD G u v huv
  · by_cases hvu : (v : Nat) < u
    · simp only [adjUpper, huv, if_false, hvu, if_true]
      change (encodeUpper11 G).getLsbD (edgeIndex11 v u) = decide (G.Adj u v)
      rw [encodeUpper11_getLsbD G v u hvu]
      simp only [G.adj_comm]
    · have huvEq : u = v := by
        apply Fin.ext
        omega
      subst v
      simp [adjUpper]

theorem graphOfUpper_encodeUpper11 (G : SimpleGraph (Fin 11))
    [DecidableRel G.Adj] :
    graphOfUpper (n := 11) (encodeUpper11 G) = G := by
  ext u v
  simp only [graphOfUpper, adjUpper_encodeUpper11, decide_eq_true_iff]

end WOWII217Encoding11
