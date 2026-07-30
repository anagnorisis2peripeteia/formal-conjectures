import WOWII217ClosureSemantics

/-! Exact encoding of simple graphs on `Fin 13` by 78 upper-triangle bits. -/

namespace WOWII217Encoding13

open SimpleGraph
open WOWII217FiniteBase WOWII217Closure WOWII217ClosureSemantics

def fin13Wrap (n : Nat) : Fin 13 :=
  ⟨n % 13, Nat.mod_lt _ (by omega)⟩

theorem fin13Wrap_coe (v : Fin 13) : fin13Wrap v = v := by
  ext
  simp [fin13Wrap, Nat.mod_eq_of_lt v.isLt]

def edgeIndex13 (u v : Nat) : Nat := upperIndex u v

theorem edgeIndex13_lt :
    ∀ (u v : Fin 13), u < v → edgeIndex13 u v < 78 := by
  native_decide

theorem upperPairs13_getD_edgeIndex :
    ∀ (u v : Fin 13), u < v →
      (upperPairs 13).getD (edgeIndex13 u v) (0, 0) =
        ((u : Nat), (v : Nat)) := by
  native_decide

def encodeUpper13 (G : SimpleGraph (Fin 13)) [DecidableRel G.Adj] : BitVec 78 := by
  let bits := List.ofFn fun i : Fin 78 =>
    let edge := (upperPairs 13).getD i (0, 0)
    decide (G.Adj (fin13Wrap edge.1) (fin13Wrap edge.2))
  exact BitVec.cast List.length_ofFn (BitVec.ofBoolListLE bits)

theorem encodeUpper13_getLsbD (G : SimpleGraph (Fin 13)) [DecidableRel G.Adj]
    (u v : Fin 13) (huv : u < v) :
    (encodeUpper13 G).getLsbD (edgeIndex13 u v) = decide (G.Adj u v) := by
  classical
  unfold encodeUpper13
  simp only [BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE]
  let bits := List.ofFn fun i : Fin 78 =>
    let edge := (upperPairs 13).getD i (0, 0)
    decide (G.Adj (fin13Wrap edge.1) (fin13Wrap edge.2))
  change bits.getD (edgeIndex13 u v) false = decide (G.Adj u v)
  have hindex : edgeIndex13 u v < bits.length := by
    rw [List.length_ofFn]
    exact edgeIndex13_lt u v huv
  rw [List.getD_eq_getElem (l := bits) (d := false) hindex]
  rw [List.getElem_ofFn]
  dsimp only
  rw [upperPairs13_getD_edgeIndex u v huv, fin13Wrap_coe, fin13Wrap_coe]

theorem adjUpper_encodeUpper13 (G : SimpleGraph (Fin 13)) [DecidableRel G.Adj]
    (u v : Fin 13) :
    adjUpper (n := 13) (encodeUpper13 G) u v = decide (G.Adj u v) := by
  by_cases huv : (u : Nat) < v
  · simp only [adjUpper, huv, if_true]
    exact encodeUpper13_getLsbD G u v huv
  · by_cases hvu : (v : Nat) < u
    · simp only [adjUpper, huv, if_false, hvu, if_true]
      change (encodeUpper13 G).getLsbD (edgeIndex13 v u) = decide (G.Adj u v)
      rw [encodeUpper13_getLsbD G v u hvu]
      simp only [G.adj_comm]
    · have huvEq : u = v := by
        apply Fin.ext
        omega
      subst v
      simp [adjUpper]

theorem graphOfUpper_encodeUpper13 (G : SimpleGraph (Fin 13))
    [DecidableRel G.Adj] :
    graphOfUpper (n := 13) (encodeUpper13 G) = G := by
  ext u v
  simp only [graphOfUpper, adjUpper_encodeUpper13, decide_eq_true_iff]

end WOWII217Encoding13
