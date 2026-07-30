import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import WOWII217BondyChvatal
import WOWII217ClosureSemantics

/-!
# Ore-type sufficient condition for Hamiltonian paths

If every pair of non-adjacent vertices has degree sum at least `|V| - 1`,
one parallel Bondy--Chvátal path-closure round produces the complete graph.
Traceability is preserved by legal closure steps; the complete graph is
traceable (via the path graph).
-/

namespace WOWII217Ore

open Classical SimpleGraph
open WOWII217BondyChvatal
open WOWII217ClosureSemantics

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Graph homomorphism embedding `pathGraph (n+1)` into `pathGraph (n+2)` by
`Fin.castSucc`. -/
def castSuccPathHom (n : Nat) :
    pathGraph (n + 1) →g pathGraph (n + 2) where
  toFun := Fin.castSucc
  map_rel' := by
    intro a b h
    simp only [pathGraph_adj, Fin.val_castSucc] at h ⊢
    exact h

theorem castSuccPathHom_injective (n : Nat) :
    Function.Injective (castSuccPathHom n) :=
  Fin.castSucc_injective (n + 1)

/-- The standard Hamiltonian path `0 — 1 — … — n` in `pathGraph (n+1)`. -/
def pathGraphPath : (n : Nat) → (pathGraph (n + 1)).Walk 0 (Fin.last n)
  | 0 => Walk.nil
  | n + 1 =>
      let p : (pathGraph (n + 2)).Walk 0 (Fin.castSucc (Fin.last n)) :=
        (pathGraphPath n).map (castSuccPathHom n)
      have hadj :
          (pathGraph (n + 2)).Adj (Fin.castSucc (Fin.last n)) (Fin.last (n + 1)) := by
        simp [pathGraph_adj, Fin.val_castSucc, Fin.val_last]
      p.concat hadj

theorem support_pathGraphPath_concat (n : Nat)
    (h :
      (pathGraph (n + 2)).Adj (Fin.castSucc (Fin.last n)) (Fin.last (n + 1))) :
    ((pathGraphPath n).map (castSuccPathHom n) |>.concat h).support =
      ((pathGraphPath n).map (castSuccPathHom n)).support ++
        [Fin.last (n + 1)] := by
  simp [Walk.concat_eq_append, Walk.support_append, Walk.support_cons,
    Walk.support_nil]

theorem pathGraphPath_isPath (n : Nat) : (pathGraphPath n).IsPath := by
  induction n with
  | zero =>
      exact Walk.IsPath.nil
  | succ n ih =>
      simp only [pathGraphPath]
      have hmap :
          ((pathGraphPath n).map (castSuccPathHom n)).IsPath :=
        Walk.map_isPath_of_injective (castSuccPathHom_injective n) ih
      apply Walk.IsPath.mk'
      rw [support_pathGraphPath_concat, List.nodup_append']
      refine ⟨hmap.support_nodup, List.nodup_singleton _, ?_⟩
      intro x hx hxLast
      have hxEq : x = Fin.last (n + 1) := List.mem_singleton.mp hxLast
      subst x
      rw [Walk.support_map] at hx
      obtain ⟨z, hz, hzx⟩ := List.mem_map.mp hx
      have hval : z.val = n + 1 := by
        have := congrArg Fin.val hzx
        simpa [Fin.val_castSucc, Fin.val_last] using this
      exact absurd hval (Nat.ne_of_lt z.isLt)

theorem pathGraphPath_support_eq (n : Nat) :
    ∀ w : Fin (n + 1), w ∈ (pathGraphPath n).support := by
  induction n with
  | zero =>
      intro w
      fin_cases w
      simp [pathGraphPath]
  | succ n ih =>
      intro w
      simp only [pathGraphPath]
      rw [support_pathGraphPath_concat, List.mem_append, List.mem_singleton]
      by_cases hw : w = Fin.last (n + 1)
      · exact Or.inr hw
      · left
        have hwlt : w.val < n + 1 := by
          have : w.val < n + 2 := w.isLt
          have hne : w.val ≠ n + 1 := by
            intro h
            exact hw (Fin.ext (by simpa [Fin.val_last] using h))
          omega
        let w' : Fin (n + 1) := ⟨w.val, hwlt⟩
        have hmem' : w' ∈ (pathGraphPath n).support := ih w'
        rw [Walk.support_map]
        refine List.mem_map.mpr ⟨w', hmem', ?_⟩
        ext
        simp [w', castSuccPathHom]

theorem pathGraphPath_isHamiltonian (n : Nat) :
    (pathGraphPath n).IsHamiltonian :=
  Walk.IsPath.isHamiltonian_of_mem (pathGraphPath_isPath n)
    (pathGraphPath_support_eq n)

/-- The path graph is traceable for `n ≥ 1`. -/
theorem pathGraph_traceable (n : Nat) (hn : 1 ≤ n) :
    Traceable (pathGraph n) := by
  cases n with
  | zero => omega
  | succ m =>
      refine ⟨0, Fin.last m, pathGraphPath m, pathGraphPath_isHamiltonian m⟩

/-- The complete graph on a finite nonempty type with at least two vertices is
traceable. -/
theorem traceable_top [Nontrivial V] :
    Traceable (⊤ : SimpleGraph V) := by
  classical
  let n := Fintype.card V
  have hn : 1 < n := Fintype.one_lt_card
  have hpath : Traceable (pathGraph n) := pathGraph_traceable n (by omega)
  -- pathGraph ≤ ⊤, and transport along Fin n ≃ V
  have hTopFin : Traceable (⊤ : SimpleGraph (Fin n)) :=
    Traceable.mono (fun _ _ h => by
      simp only [top_adj]
      exact (pathGraph_adj.mp h).elim
        (fun h' => by
          intro heq
          have := congrArg Fin.val heq
          omega)
        (fun h' => by
          intro heq
          have := congrArg Fin.val heq
          omega)) hpath
  let e : Fin n ≃ V := (Fintype.equivFin V).symm
  let f : (⊤ : SimpleGraph (Fin n)) →g (⊤ : SimpleGraph V) :=
    ⟨e, fun {x y} h => by
      simp only [top_adj] at h ⊢
      exact e.injective.ne h⟩
  rcases hTopFin with ⟨a, b, p, hp⟩
  exact ⟨e a, e b, p.map f, hp.map f e.bijective⟩

/-- All ordered pairs of distinct vertices. -/
noncomputable def allDistinctPairs : List (V × V) :=
  (Finset.univ ×ˢ Finset.univ).filter (fun p => p.1 ≠ p.2) |>.toList

theorem mem_allDistinctPairs {u v : V} (hne : u ≠ v) :
    (u, v) ∈ allDistinctPairs := by
  simp [allDistinctPairs, hne]

/-- Under Ore's condition every missing edge is path-closure eligible. -/
theorem addEligible_eq_top_of_ore (G : SimpleGraph V) [DecidableRel G.Adj]
    (hOre : ∀ u v : V, u ≠ v → ¬ G.Adj u v →
      Fintype.card V - 1 ≤ G.degree u + G.degree v) :
    addEligibleEdgesFrom G allDistinctPairs G = (⊤ : SimpleGraph V) := by
  classical
  ext u v
  constructor
  · intro h
    exact SimpleGraph.Adj.ne h
  · intro hne
    have hne' : u ≠ v := by
      simpa [top_adj] using hne
    rw [adj_addEligibleEdgesFrom_iff]
    by_cases hadj : G.Adj u v
    · exact Or.inl hadj
    · refine Or.inr ⟨(u, v), mem_allDistinctPairs hne', hOre u v hne' hadj, ?_⟩
      simp [SimpleGraph.edge_adj, hne']

/-- Ore's theorem for Hamiltonian paths (threshold `|V| - 1`). -/
theorem traceable_of_ore [Nontrivial V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hOre : ∀ u v : V, u ≠ v → ¬ G.Adj u v →
      Fintype.card V - 1 ≤ G.degree u + G.degree v) :
    Traceable G := by
  classical
  have hTop : addEligibleEdgesFrom G allDistinctPairs G = ⊤ :=
    addEligible_eq_top_of_ore G hOre
  have hIff :
      Traceable (addEligibleEdgesFrom G allDistinctPairs G) ↔ Traceable G :=
    traceable_addEligibleEdgesFrom_iff G G allDistinctPairs le_rfl
  rw [← hIff, hTop]
  exact traceable_top

/-- If `n - 1 ≤ 2 · δ(G)` then `G` is traceable (Dirac-type path condition). -/
theorem traceable_of_minDegree_half [Nontrivial V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hδ : Fintype.card V - 1 ≤ 2 * G.minDegree) :
    Traceable G := by
  refine traceable_of_ore G ?_
  intro u v hne hadj
  have hu := G.minDegree_le_degree u
  have hv := G.minDegree_le_degree v
  omega

end WOWII217Ore
