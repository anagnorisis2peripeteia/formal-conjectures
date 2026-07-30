import FormalConjecturesUtil

namespace WOWII217Proof

open SimpleGraph

variable {α : Type*} [DecidableEq α] {G : SimpleGraph α}

/-- A nonempty list whose consecutive vertices are adjacent is the support of a walk. -/
theorem exists_walk_support_eq_of_isChain (l : List α) (hl : l ≠ [])
    (hchain : l.IsChain G.Adj) :
    ∃ a b : α, ∃ p : G.Walk a b, p.support = l := by
  induction l with
  | nil => exact (hl rfl).elim
  | cons a l ih =>
      cases l with
      | nil => exact ⟨a, a, .nil, rfl⟩
      | cons b t =>
          rw [List.isChain_cons_cons] at hchain
          obtain ⟨c, d, p, hp⟩ := ih (by simp) hchain.2
          have hbc : b = c := by
            simpa [hp] using p.head_support
          subst c
          exact ⟨a, d, .cons hchain.1 p, by simp [hp]⟩

/-- A vertex ordering certifies a Hamiltonian path when it is duplicate-free,
contains every vertex, and consecutive vertices are adjacent. -/
theorem exists_hamiltonian_walk_of_vertex_order (l : List α) (hl : l ≠ [])
    (hchain : l.IsChain G.Adj) (hnodup : l.Nodup) (hcover : ∀ v : α, v ∈ l) :
    ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian := by
  obtain ⟨a, b, p, hp⟩ := exists_walk_support_eq_of_isChain l hl hchain
  refine ⟨a, b, p, ?_⟩
  apply Walk.IsPath.isHamiltonian_of_mem (Walk.IsPath.mk' ?_) ?_
  · simpa [hp] using hnodup
  · simpa [hp] using hcover

end WOWII217Proof
