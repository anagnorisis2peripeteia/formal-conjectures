import WOWII217ClosureSemantics
import WOWII217Closure
import WOWII217BondyChvatal

namespace L6Work

open SimpleGraph WOWII217FiniteBase WOWII217Closure WOWII217ClosureSemantics
open WOWII217BondyChvatal

/-- L0. Degree is monotone in the graph. Not in Mathlib. -/
theorem degree_mono {V : Type*} [Fintype V] [DecidableEq V] {G H : SimpleGraph V}
    [DecidableRel G.Adj] [DecidableRel H.Adj] (h : G ≤ H) (v : V) :
    G.degree v ≤ H.degree v := by
  rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree]
  apply Finset.card_le_card
  intro w hw
  rw [mem_neighborFinset] at hw ⊢
  exact h hw

/-- Absorbing an edge that is already present. -/
theorem sup_edge_of_adj {V : Type*} {G : SimpleGraph V} {u v : V} (h : G.Adj u v) :
    G ⊔ SimpleGraph.edge u v = G := by
  rw [sup_eq_left]
  intro a b hab
  rw [SimpleGraph.edge_adj] at hab
  obtain ⟨heq, _⟩ := hab
  rcases heq with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · subst ha; subst hb; exact h
  · subst ha; subst hb; exact h.symm

/-- L6. No `¬Adj` hypothesis: if the edge is already there the step is absorbed,
otherwise `traceable_sup_edge_iff` applies. The degree justification is stated
against the ORIGINAL `G` and survives the fold by `degree_mono`. -/
theorem traceable_foldl_sup_edge {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] :
    ∀ (es : List (V × V)) (G : SimpleGraph V) [DecidableRel G.Adj],
      (∀ p ∈ es, Fintype.card V - 1 ≤ G.degree p.1 + G.degree p.2) →
      (Traceable (es.foldl (fun H p => H ⊔ SimpleGraph.edge p.1 p.2) G) ↔ Traceable G) := by
  intro es
  induction es with
  | nil => intro G _ _; simp
  | cons p rest ih =>
      intro G _ hjust
      have hp := hjust p (by simp)
      have hle : G ≤ G ⊔ SimpleGraph.edge p.1 p.2 := le_sup_left
      have htail : ∀ q ∈ rest,
          Fintype.card V - 1 ≤ (G ⊔ SimpleGraph.edge p.1 p.2).degree q.1
                             + (G ⊔ SimpleGraph.edge p.1 p.2).degree q.2 := by
        intro q hq
        exact le_trans (hjust q (by simp [hq]))
          (Nat.add_le_add (degree_mono hle q.1) (degree_mono hle q.2))
      rw [List.foldl_cons, ih (G ⊔ SimpleGraph.edge p.1 p.2) htail]
      by_cases hadj : G.Adj p.1 p.2
      · rw [sup_edge_of_adj hadj]
      · exact traceable_sup_edge_iff hadj hp

end L6Work

