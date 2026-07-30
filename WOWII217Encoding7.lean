import WOWII217ClosureSemantics

/-! Exact encoding of simple graphs on `Fin 7` by 21 upper-triangle bits. -/

namespace WOWII217Encoding7

open SimpleGraph
open WOWII217FiniteBase WOWII217Closure WOWII217ClosureSemantics

def fin7Wrap (n : Nat) : Fin 7 :=
  ⟨n % 7, Nat.mod_lt _ (by omega)⟩

theorem fin7Wrap_coe (v : Fin 7) : fin7Wrap v = v := by
  ext
  simp [fin7Wrap, Nat.mod_eq_of_lt v.isLt]

def edgeIndex7 (u v : Nat) : Nat := upperIndex u v

theorem edgeIndex7_lt :
    ∀ (u v : Fin 7), u < v → edgeIndex7 u v < 21 := by
  native_decide

theorem upperPairs7_getD_edgeIndex :
    ∀ (u v : Fin 7), u < v →
      (upperPairs 7).getD (edgeIndex7 u v) (0, 0) =
        ((u : Nat), (v : Nat)) := by
  native_decide

def encodeUpper7 (G : SimpleGraph (Fin 7)) [DecidableRel G.Adj] : BitVec 21 := by
  let bits := List.ofFn fun i : Fin 21 =>
    let edge := (upperPairs 7).getD i (0, 0)
    decide (G.Adj (fin7Wrap edge.1) (fin7Wrap edge.2))
  exact BitVec.cast List.length_ofFn (BitVec.ofBoolListLE bits)

theorem encodeUpper7_getLsbD (G : SimpleGraph (Fin 7)) [DecidableRel G.Adj]
    (u v : Fin 7) (huv : u < v) :
    (encodeUpper7 G).getLsbD (edgeIndex7 u v) = decide (G.Adj u v) := by
  classical
  unfold encodeUpper7
  simp only [BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE]
  let bits := List.ofFn fun i : Fin 21 =>
    let edge := (upperPairs 7).getD i (0, 0)
    decide (G.Adj (fin7Wrap edge.1) (fin7Wrap edge.2))
  change bits.getD (edgeIndex7 u v) false = decide (G.Adj u v)
  have hindex : edgeIndex7 u v < bits.length := by
    rw [List.length_ofFn]
    exact edgeIndex7_lt u v huv
  rw [List.getD_eq_getElem (l := bits) (d := false) hindex]
  rw [List.getElem_ofFn]
  dsimp only
  rw [upperPairs7_getD_edgeIndex u v huv, fin7Wrap_coe, fin7Wrap_coe]

theorem adjUpper_encodeUpper7 (G : SimpleGraph (Fin 7)) [DecidableRel G.Adj]
    (u v : Fin 7) :
    adjUpper (n := 7) (encodeUpper7 G) u v = decide (G.Adj u v) := by
  by_cases huv : (u : Nat) < v
  · simp only [adjUpper, huv, if_true]
    exact encodeUpper7_getLsbD G u v huv
  · by_cases hvu : (v : Nat) < u
    · simp only [adjUpper, huv, if_false, hvu, if_true]
      change (encodeUpper7 G).getLsbD (edgeIndex7 v u) = decide (G.Adj u v)
      rw [encodeUpper7_getLsbD G v u hvu]
      simp only [G.adj_comm]
    · have huvEq : u = v := by
        apply Fin.ext
        omega
      subst v
      simp [adjUpper]

theorem graphOfUpper_encodeUpper7 (G : SimpleGraph (Fin 7))
    [DecidableRel G.Adj] :
    graphOfUpper (n := 7) (encodeUpper7 G) = G := by
  ext u v
  simp only [graphOfUpper, adjUpper_encodeUpper7, decide_eq_true_iff]

end WOWII217Encoding7
