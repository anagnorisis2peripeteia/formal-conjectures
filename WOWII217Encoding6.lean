import WOWII217ClosureSemantics

/-! Exact encoding of simple graphs on `Fin 6` by 15 upper-triangle bits. -/

namespace WOWII217Encoding6

open SimpleGraph
open WOWII217FiniteBase WOWII217Closure WOWII217ClosureSemantics

def fin6Wrap (n : Nat) : Fin 6 :=
  ⟨n % 6, Nat.mod_lt _ (by omega)⟩

theorem fin6Wrap_coe (v : Fin 6) : fin6Wrap v = v := by
  ext
  simp [fin6Wrap, Nat.mod_eq_of_lt v.isLt]

def edgeIndex6 (u v : Nat) : Nat := upperIndex u v

theorem edgeIndex6_lt :
    ∀ (u v : Fin 6), u < v → edgeIndex6 u v < 15 := by
  native_decide

theorem upperPairs6_getD_edgeIndex :
    ∀ (u v : Fin 6), u < v →
      (upperPairs 6).getD (edgeIndex6 u v) (0, 0) =
        ((u : Nat), (v : Nat)) := by
  native_decide

def encodeUpper6 (G : SimpleGraph (Fin 6)) [DecidableRel G.Adj] : BitVec 15 := by
  let bits := List.ofFn fun i : Fin 15 =>
    let edge := (upperPairs 6).getD i (0, 0)
    decide (G.Adj (fin6Wrap edge.1) (fin6Wrap edge.2))
  exact BitVec.cast List.length_ofFn (BitVec.ofBoolListLE bits)

theorem encodeUpper6_getLsbD (G : SimpleGraph (Fin 6)) [DecidableRel G.Adj]
    (u v : Fin 6) (huv : u < v) :
    (encodeUpper6 G).getLsbD (edgeIndex6 u v) = decide (G.Adj u v) := by
  classical
  unfold encodeUpper6
  simp only [BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE]
  let bits := List.ofFn fun i : Fin 15 =>
    let edge := (upperPairs 6).getD i (0, 0)
    decide (G.Adj (fin6Wrap edge.1) (fin6Wrap edge.2))
  change bits.getD (edgeIndex6 u v) false = decide (G.Adj u v)
  have hindex : edgeIndex6 u v < bits.length := by
    rw [List.length_ofFn]
    exact edgeIndex6_lt u v huv
  rw [List.getD_eq_getElem (l := bits) (d := false) hindex]
  rw [List.getElem_ofFn]
  dsimp only
  rw [upperPairs6_getD_edgeIndex u v huv, fin6Wrap_coe, fin6Wrap_coe]

theorem adjUpper_encodeUpper6 (G : SimpleGraph (Fin 6)) [DecidableRel G.Adj]
    (u v : Fin 6) :
    adjUpper (n := 6) (encodeUpper6 G) u v = decide (G.Adj u v) := by
  by_cases huv : (u : Nat) < v
  · simp only [adjUpper, huv, if_true]
    exact encodeUpper6_getLsbD G u v huv
  · by_cases hvu : (v : Nat) < u
    · simp only [adjUpper, huv, if_false, hvu, if_true]
      change (encodeUpper6 G).getLsbD (edgeIndex6 v u) = decide (G.Adj u v)
      rw [encodeUpper6_getLsbD G v u hvu]
      simp only [G.adj_comm]
    · have huvEq : u = v := by
        apply Fin.ext
        omega
      subst v
      simp [adjUpper]

theorem graphOfUpper_encodeUpper6 (G : SimpleGraph (Fin 6))
    [DecidableRel G.Adj] :
    graphOfUpper (n := 6) (encodeUpper6 G) = G := by
  ext u v
  simp only [graphOfUpper, adjUpper_encodeUpper6, decide_eq_true_iff]

end WOWII217Encoding6
