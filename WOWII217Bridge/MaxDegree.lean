import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

namespace MaxDeg

open SimpleGraph Finset

/-- A connected graph on at least 3 vertices has a vertex of degree at least 2.

Consequence for `WOWII217SmallNExceptions`: `hStuck : 2 * G.maxDegree < card V - 1`
forces `maxDegree ≤ 1` when `card V ≤ 5`, so the `exception_stuck_non_regular`
cases for `card V = 4` and `card V = 5` are VACUOUS. -/
theorem two_le_maxDegree_of_connected {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (conn : G.Connected)
    (hcard : 3 ≤ Fintype.card V) : 2 ≤ G.maxDegree := by
  by_contra hlt
  push_neg at hlt
  -- every degree is at most 1
  have hdeg : ∀ v : V, G.degree v ≤ 1 := fun v =>
    le_trans (G.degree_le_maxDegree v) (by omega)
  -- handshake: 2 * #edges = sum of degrees ≤ card V
  have hsum : ∑ v : V, G.degree v ≤ Fintype.card V := by
    calc ∑ v : V, G.degree v ≤ ∑ _v : V, 1 := Finset.sum_le_sum fun v _ => hdeg v
      _ = Fintype.card V := by simp
  have hhand : 2 * #G.edgeFinset ≤ Fintype.card V := by
    rw [← G.sum_degrees_eq_twice_card_edges]; exact hsum
  -- connectivity: card V ≤ #edges + 1
  have hconn : Fintype.card V ≤ #G.edgeFinset + 1 := by
    have := conn.card_vert_le_card_edgeSet_add_one
    simpa [Nat.card_eq_fintype_card, Set.ncard_eq_toFinset_card', edgeFinset] using this
  omega


/-- `hStuck` is unsatisfiable for `card V = 4` and `card V = 5`:
`2 * maxDegree < card V - 1` forces `maxDegree ≤ 1`, contradicting the lemma above. -/
theorem stuck_vacuous_of_card_le_five {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (conn : G.Connected)
    (hcard3 : 3 ≤ Fintype.card V) (hcard5 : Fintype.card V ≤ 5)
    (hStuck : 2 * G.maxDegree < Fintype.card V - 1) : False := by
  have h2 := two_le_maxDegree_of_connected G conn hcard3
  omega

end MaxDeg


