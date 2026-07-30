import WOWII217Chvatal

namespace RoundChar

open SimpleGraph WOWII217ClosureSemantics WOWII217Ore WOWII217Chvatal

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Clean adjacency characterisation of one graph-level closure round. -/
theorem adj_pathClosureRound_iff (G : SimpleGraph V) [DecidableRel G.Adj] (x y : V) :
    (pathClosureRound G).Adj x y ↔
      G.Adj x y ∨ (x ≠ y ∧ Fintype.card V - 1 ≤ G.degree x + G.degree y) := by
  classical
  have hd : ∀ (i : DecidableRel G.Adj) (a : V),
      @SimpleGraph.degree V G a (@SimpleGraph.neighborSetFintype V G _ i a) = G.degree a := by
    intro i a; congr 1 <;> exact Subsingleton.elim _ _
  unfold pathClosureRound
  rw [adj_addEligibleEdgesFrom_iff]
  constructor
  · rintro (hadj | ⟨⟨u, v⟩, hmem, hdeg, hedge⟩)
    · exact Or.inl hadj
    · right
      rw [SimpleGraph.edge_adj] at hedge
      obtain ⟨heq, hne⟩ := hedge
      refine ⟨hne, ?_⟩
      rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · convert hdeg using 3 <;> exact Subsingleton.elim _ _
      · rw [Nat.add_comm]; convert hdeg using 3 <;> exact Subsingleton.elim _ _
  · rintro (hadj | ⟨hne, hdeg⟩)
    · exact Or.inl hadj
    · right
      refine ⟨(x, y), mem_allDistinctPairs hne, ?_, ?_⟩
      · convert hdeg using 3 <;> exact Subsingleton.elim _ _
      rw [SimpleGraph.edge_adj]
      exact ⟨Or.inl ⟨rfl, rfl⟩, hne⟩

end RoundChar
