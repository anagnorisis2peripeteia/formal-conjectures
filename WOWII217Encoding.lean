import WOWII217Semantics

/-!
Exact encoding of simple graphs on `Fin 14` by the 91 upper-triangle bits.
-/

namespace WOWII217Encoding

open SimpleGraph

def upperPairs14 : List (Nat × Nat) :=
  (List.range 14).flatMap fun v => (List.range v).map fun u => (u, v)

def fin14Wrap (n : Nat) : Fin 14 := ⟨n % 14, Nat.mod_lt _ (by omega)⟩

theorem fin14Wrap_coe (v : Fin 14) : fin14Wrap v = v := by
  ext
  simp [fin14Wrap, Nat.mod_eq_of_lt v.isLt]

def edgeIndex14 (u v : Nat) : Nat := v * (v - 1) / 2 + u

theorem edgeIndex14_lt :
    ∀ (u v : Fin 14), u < v → edgeIndex14 u v < 91 := by
  native_decide

theorem upperPairs14_getD_edgeIndex :
    ∀ (u v : Fin 14), u < v →
      upperPairs14.getD (edgeIndex14 u v) (0, 0) = ((u : Nat), (v : Nat)) := by
  native_decide

def encodeUpper14 (G : SimpleGraph (Fin 14)) [DecidableRel G.Adj] : BitVec 91 := by
  let bits := List.ofFn fun i : Fin 91 =>
    let edge := upperPairs14.getD i (0, 0)
    decide (G.Adj (fin14Wrap edge.1) (fin14Wrap edge.2))
  exact BitVec.cast List.length_ofFn (BitVec.ofBoolListLE bits)

theorem encodeUpper14_getLsbD (G : SimpleGraph (Fin 14)) [DecidableRel G.Adj]
    (u v : Fin 14) (huv : u < v) :
    (encodeUpper14 G).getLsbD (edgeIndex14 u v) = decide (G.Adj u v) := by
  classical
  unfold encodeUpper14
  simp only [BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE]
  let bits := List.ofFn fun i : Fin 91 =>
    let edge := upperPairs14.getD i (0, 0)
    decide (G.Adj (fin14Wrap edge.1) (fin14Wrap edge.2))
  change bits.getD (edgeIndex14 u v) false = decide (G.Adj u v)
  have hindex : edgeIndex14 u v < bits.length := by
    rw [List.length_ofFn]
    exact edgeIndex14_lt u v huv
  rw [List.getD_eq_getElem (l := bits) (d := false) hindex]
  rw [List.getElem_ofFn]
  dsimp only
  rw [upperPairs14_getD_edgeIndex u v huv, fin14Wrap_coe, fin14Wrap_coe]

theorem adjUpper_encodeUpper14 (G : SimpleGraph (Fin 14)) [DecidableRel G.Adj]
    (u v : Fin 14) :
    WOWII217Semantics.adjUpper (n := 14) (encodeUpper14 G) u v =
      decide (G.Adj u v) := by
  by_cases huv : (u : Nat) < v
  · simp only [WOWII217Semantics.adjUpper, huv, if_true]
    exact encodeUpper14_getLsbD G u v huv
  · by_cases hvu : (v : Nat) < u
    · simp only [WOWII217Semantics.adjUpper, huv, if_false, hvu, if_true]
      change (encodeUpper14 G).getLsbD (edgeIndex14 v u) = decide (G.Adj u v)
      rw [encodeUpper14_getLsbD G v u hvu]
      simp only [G.adj_comm]
    · have huvEq : u = v := by
        apply Fin.ext
        omega
      subst v
      simp [WOWII217Semantics.adjUpper, G.loopless]

theorem graphOfUpper14_encodeUpper14 (G : SimpleGraph (Fin 14)) [DecidableRel G.Adj] :
    WOWII217Semantics.graphOfUpper14 (encodeUpper14 G) = G := by
  ext u v
  simp only [WOWII217Semantics.graphOfUpper14, adjUpper_encodeUpper14,
    decide_eq_true_iff]

end WOWII217Encoding
