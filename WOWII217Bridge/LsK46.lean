import WOWII217SpanningTree
import WOWII217ClosureSemantics

/-!
`Ls (K 4 6) >= 8`, which is what excludes K(4,6) from conjecture 217.

K(4,6) is connected, has residue 2 and degree sequence [6,6,6,6,4,4,4,4,4,4], yet has NO
Hamiltonian path (a bipartite graph whose parts differ by more than one cannot have one).
It is excluded from the conjecture only by the `Ls G <= 6` hypothesis, so the residual
branches need this bound to discharge it.

The witnessing spanning tree joins vertex `0` to all six right vertices and hangs
`1, 2, 3` off vertex `4`: nine edges, ten vertices, eight leaves.
-/

namespace LsK46

open SimpleGraph Finset WOWII217ClosureSemantics

/-- `K(4,6)` on `Fin 10`, parts `{0,1,2,3}` and `{4,...,9}`.

Defined AS the decoded counterexample encoding, so no bridge lemma is needed: this is
literally the `g` that `bv_decide` produced for degree sequence [6,6,6,6,4,4,4,4,4,4]. -/
def K46 : SimpleGraph (Fin 10) := graphOfUpper (n := 10) 1034850648000#45

instance : DecidableRel K46.Adj := graphOfUpper_decidableRel _

/-- Sanity check that the encoding really is the complete bipartite graph. -/
theorem K46_adj (u v : Fin 10) : K46.Adj u v ↔ ((u.val < 4) ≠ (v.val < 4)) := by
  revert u v; decide

/-- The witnessing spanning tree. -/
def TG : SimpleGraph (Fin 10) where
  Adj u v := u ≠ v ∧
    ((u = 0 ∧ 4 ≤ v.val) ∨ (v = 0 ∧ 4 ≤ u.val) ∨
     (u = 4 ∧ (v = 1 ∨ v = 2 ∨ v = 3)) ∨ (v = 4 ∧ (u = 1 ∨ u = 2 ∨ u = 3)))
  symm := by intro u v h; refine ⟨h.1.symm, ?_⟩; rcases h.2 with a|a|a|a <;> tauto
  loopless := by intro v h; exact h.1 rfl

instance : DecidableRel TG.Adj := fun u v => by unfold TG; infer_instance

theorem TG_le_K46 : TG ≤ K46 := by
  have h : ∀ u v : Fin 10, TG.Adj u v → K46.Adj u v := by decide
  exact fun {u v} => h u v

theorem TG_connected : TG.Connected := by decide

theorem TG_isTree : TG.IsTree := by
  rw [isTree_iff_connected_and_card]
  refine ⟨TG_connected, ?_⟩
  simp only [Nat.card_eq_fintype_card]
  decide

/-- Eight vertices of the tree have degree one. -/
theorem TG_leaves : (univ.filter fun v : Fin 10 => TG.degree v = 1).card = 8 := by decide

/-- The tree, as a spanning subgraph of `K46`. -/
def TT : K46.Subgraph := K46.toSubgraph TG TG_le_K46

theorem TT_spanning : TT.IsSpanning := by
  intro v; trivial

theorem TT_isTree : IsTree TT.coe := by
  have h := (TT.spanningCoeEquivCoeOfSpanning TT_spanning).isTree_iff.mp TG_isTree
  simpa [TT] using h

theorem TT_leafCount : WOWII217SpanningTree.spanningLeafCount TT = 8 := by
  classical
  have hdeg : ∀ v : Fin 10, TT.degree v = TG.degree v := by
    intro v
    simpa [TT] using SimpleGraph.degree_toSubgraph K46 TG TG_le_K46 (v := v)
  unfold WOWII217SpanningTree.spanningLeafCount
  have hset : (TT.verts.toFinset.filter fun v => TT.degree v = 1)
      = (univ.filter fun v : Fin 10 => TG.degree v = 1) := by
    ext v
    simp [TT, hdeg v]
  rw [hset]
  exact TG_leaves

/-- THE BOUND: `Ls (K 4 6) >= 8`, so K(4,6) fails `Ls G <= 6`. -/
theorem Ls_K46_ge_eight : (8 : ℝ) ≤ Ls K46 := by
  have h := WOWII217SpanningTree.spanningTree_leafCount_le_Ls K46 TT TT_spanning TT_isTree
  rwa [TT_leafCount] at h
  
end LsK46
