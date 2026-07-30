import WOWII217ClosureSemantics

/-! Exact encoding of simple graphs on `Fin 9` by 36 upper-triangle bits. -/

namespace WOWII217Encoding9

open SimpleGraph
open WOWII217FiniteBase WOWII217Closure WOWII217ClosureSemantics

def fin9Wrap (n : Nat) : Fin 9 :=
  ⟨n % 9, Nat.mod_lt _ (by omega)⟩

theorem fin9Wrap_coe (v : Fin 9) : fin9Wrap v = v := by
  ext
  simp [fin9Wrap, Nat.mod_eq_of_lt v.isLt]

def edgeIndex9 (u v : Nat) : Nat := upperIndex u v

theorem edgeIndex9_lt :
    ∀ (u v : Fin 9), u < v → edgeIndex9 u v < 36 := by
  native_decide

theorem upperPairs9_getD_edgeIndex :
    ∀ (u v : Fin 9), u < v →
      (upperPairs 9).getD (edgeIndex9 u v) (0, 0) =
        ((u : Nat), (v : Nat)) := by
  native_decide

def encodeUpper9 (G : SimpleGraph (Fin 9)) [DecidableRel G.Adj] : BitVec 36 := by
  let bits := List.ofFn fun i : Fin 36 =>
    let edge := (upperPairs 9).getD i (0, 0)
    decide (G.Adj (fin9Wrap edge.1) (fin9Wrap edge.2))
  exact BitVec.cast List.length_ofFn (BitVec.ofBoolListLE bits)

theorem encodeUpper9_getLsbD (G : SimpleGraph (Fin 9)) [DecidableRel G.Adj]
    (u v : Fin 9) (huv : u < v) :
    (encodeUpper9 G).getLsbD (edgeIndex9 u v) = decide (G.Adj u v) := by
  classical
  unfold encodeUpper9
  simp only [BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE]
  let bits := List.ofFn fun i : Fin 36 =>
    let edge := (upperPairs 9).getD i (0, 0)
    decide (G.Adj (fin9Wrap edge.1) (fin9Wrap edge.2))
  change bits.getD (edgeIndex9 u v) false = decide (G.Adj u v)
  have hindex : edgeIndex9 u v < bits.length := by
    rw [List.length_ofFn]
    exact edgeIndex9_lt u v huv
  rw [List.getD_eq_getElem (l := bits) (d := false) hindex]
  rw [List.getElem_ofFn]
  dsimp only
  rw [upperPairs9_getD_edgeIndex u v huv, fin9Wrap_coe, fin9Wrap_coe]

theorem adjUpper_encodeUpper9 (G : SimpleGraph (Fin 9)) [DecidableRel G.Adj]
    (u v : Fin 9) :
    adjUpper (n := 9) (encodeUpper9 G) u v = decide (G.Adj u v) := by
  by_cases huv : (u : Nat) < v
  · simp only [adjUpper, huv, if_true]
    exact encodeUpper9_getLsbD G u v huv
  · by_cases hvu : (v : Nat) < u
    · simp only [adjUpper, huv, if_false, hvu, if_true]
      change (encodeUpper9 G).getLsbD (edgeIndex9 v u) = decide (G.Adj u v)
      rw [encodeUpper9_getLsbD G v u hvu]
      simp only [G.adj_comm]
    · have huvEq : u = v := by
        apply Fin.ext
        omega
      subst v
      simp [adjUpper]

theorem graphOfUpper_encodeUpper9 (G : SimpleGraph (Fin 9))
    [DecidableRel G.Adj] :
    graphOfUpper (n := 9) (encodeUpper9 G) = G := by
  ext u v
  simp only [graphOfUpper, adjUpper_encodeUpper9, decide_eq_true_iff]

end WOWII217Encoding9
