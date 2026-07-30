import WOWII217ClosureSemantics

/-! Exact encoding of simple graphs on `Fin 5` by 10 upper-triangle bits. -/

namespace WOWII217Encoding5

open SimpleGraph
open WOWII217FiniteBase WOWII217Closure WOWII217ClosureSemantics

def fin5Wrap (n : Nat) : Fin 5 :=
  ⟨n % 5, Nat.mod_lt _ (by omega)⟩

theorem fin5Wrap_coe (v : Fin 5) : fin5Wrap v = v := by
  ext
  simp [fin5Wrap, Nat.mod_eq_of_lt v.isLt]

def edgeIndex5 (u v : Nat) : Nat := upperIndex u v

theorem edgeIndex5_lt :
    ∀ (u v : Fin 5), u < v → edgeIndex5 u v < 10 := by
  native_decide

theorem upperPairs5_getD_edgeIndex :
    ∀ (u v : Fin 5), u < v →
      (upperPairs 5).getD (edgeIndex5 u v) (0, 0) =
        ((u : Nat), (v : Nat)) := by
  native_decide

def encodeUpper5 (G : SimpleGraph (Fin 5)) [DecidableRel G.Adj] : BitVec 10 := by
  let bits := List.ofFn fun i : Fin 10 =>
    let edge := (upperPairs 5).getD i (0, 0)
    decide (G.Adj (fin5Wrap edge.1) (fin5Wrap edge.2))
  exact BitVec.cast List.length_ofFn (BitVec.ofBoolListLE bits)

theorem encodeUpper5_getLsbD (G : SimpleGraph (Fin 5)) [DecidableRel G.Adj]
    (u v : Fin 5) (huv : u < v) :
    (encodeUpper5 G).getLsbD (edgeIndex5 u v) = decide (G.Adj u v) := by
  classical
  unfold encodeUpper5
  simp only [BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE]
  let bits := List.ofFn fun i : Fin 10 =>
    let edge := (upperPairs 5).getD i (0, 0)
    decide (G.Adj (fin5Wrap edge.1) (fin5Wrap edge.2))
  change bits.getD (edgeIndex5 u v) false = decide (G.Adj u v)
  have hindex : edgeIndex5 u v < bits.length := by
    rw [List.length_ofFn]
    exact edgeIndex5_lt u v huv
  rw [List.getD_eq_getElem (l := bits) (d := false) hindex]
  rw [List.getElem_ofFn]
  dsimp only
  rw [upperPairs5_getD_edgeIndex u v huv, fin5Wrap_coe, fin5Wrap_coe]

theorem adjUpper_encodeUpper5 (G : SimpleGraph (Fin 5)) [DecidableRel G.Adj]
    (u v : Fin 5) :
    adjUpper (n := 5) (encodeUpper5 G) u v = decide (G.Adj u v) := by
  by_cases huv : (u : Nat) < v
  · simp only [adjUpper, huv, if_true]
    exact encodeUpper5_getLsbD G u v huv
  · by_cases hvu : (v : Nat) < u
    · simp only [adjUpper, huv, if_false, hvu, if_true]
      change (encodeUpper5 G).getLsbD (edgeIndex5 v u) = decide (G.Adj u v)
      rw [encodeUpper5_getLsbD G v u hvu]
      simp only [G.adj_comm]
    · have huvEq : u = v := by
        apply Fin.ext
        omega
      subst v
      simp [adjUpper]

theorem graphOfUpper_encodeUpper5 (G : SimpleGraph (Fin 5))
    [DecidableRel G.Adj] :
    graphOfUpper (n := 5) (encodeUpper5 G) = G := by
  ext u v
  simp only [graphOfUpper, adjUpper_encodeUpper5, decide_eq_true_iff]

end WOWII217Encoding5
