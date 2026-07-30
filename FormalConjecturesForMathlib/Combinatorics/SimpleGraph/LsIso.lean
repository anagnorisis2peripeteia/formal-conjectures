import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.SpanningTree

namespace SimpleGraph
open Classical Finset Set

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
  (G : SimpleGraph α) [DecidableRel G.Adj] (H : SimpleGraph β) [DecidableRel H.Adj]

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

def fHom (f : G ≃g H) : G →g H := f
def fSymmHom (f : G ≃g H) : H →g G := f.symm

def Subgraph.mapIso (f : G ≃g H) (T : G.Subgraph) : T.coe ≃g (T.map (fHom G H f)).coe where
  toFun v := ⟨f v.1, Set.mem_image_of_mem f v.2⟩
  invFun v := ⟨f.symm v.1, by
    rcases v.2 with ⟨x, hx, hx'⟩
    have h : f x = v.1 := hx'
    have : x = f.symm v.1 := by
      calc x = f.symm (f x) := (f.left_inv x).symm
           _ = f.symm v.1 := congrArg f.symm h
    rw [←this]
    exact hx⟩
  left_inv v := Subtype.ext (f.left_inv v.1)
  right_inv v := Subtype.ext (f.right_inv v.1)
  map_rel_iff' := by
    intro ⟨v, hv⟩ ⟨w, hw⟩
    dsimp only [Subgraph.map]
    constructor
    · rintro ⟨a, b, hab, ha, hb⟩
      have h1 : a = v := f.injective ha
      have h2 : b = w := f.injective hb
      rwa [h1, h2] at hab
    · intro h
      exact ⟨v, w, h, rfl, rfl⟩

lemma map_isSpanning (f : G ≃g H) (T : G.Subgraph) (h : T.IsSpanning) : (T.map (fHom G H f)).IsSpanning := by
  intro v
  have : v = f (f.symm v) := (f.right_inv v).symm
  rw [this]
  exact Set.mem_image_of_mem f (h (f.symm v))

lemma map_isTree (f : G ≃g H) (T : G.Subgraph) (h : IsTree T.coe) : IsTree (T.map (fHom G H f)).coe := by
  rwa [← (Subgraph.mapIso G H f T).isTree_iff]

lemma map_degree (f : G ≃g H) (T : G.Subgraph) (v : α) : (T.map (fHom G H f)).degree (f v) = T.degree v := by
  unfold Subgraph.degree
  let e : (T.map (fHom G H f)).neighborSet (f v) ≃ T.neighborSet v := {
    toFun := fun w => ⟨f.symm w.1, by
      rcases w.2 with hw
      simp only [Subgraph.mem_neighborSet, Subgraph.map] at hw
      rcases hw with ⟨a, b, hab, ha, hb⟩
      have h1 : a = v := f.injective ha
      have h2 : b = f.symm w.1 := by
        calc b = f.symm (f b) := (f.left_inv b).symm
             _ = f.symm w.1 := congrArg f.symm hb
      rw [h1, h2] at hab
      exact hab⟩
    invFun := fun w => ⟨f w.1, by
      rcases w.2 with hw
      simp only [Subgraph.mem_neighborSet, Subgraph.map]
      exact ⟨v, w.1, hw, rfl, rfl⟩⟩
    left_inv := fun w => Subtype.ext (f.right_inv w.1)
    right_inv := fun w => Subtype.ext (f.left_inv w.1)
  }
  exact Fintype.card_congr e

lemma map_leaves_card (f : G ≃g H) (T : G.Subgraph) :
    ((T.map (fHom G H f)).verts.toFinset.filter (fun v => (T.map (fHom G H f)).degree v = 1)).card =
    (T.verts.toFinset.filter (fun v => T.degree v = 1)).card := by
  let S1 := T.verts.toFinset.filter (fun v => T.degree v = 1)
  let S2 := (T.map (fHom G H f)).verts.toFinset.filter (fun v => (T.map (fHom G H f)).degree v = 1)
  have h_S2 : S2 = Finset.map (f : α ≃ β).toEmbedding S1 := by
    ext w
    simp only [S2, S1, mem_filter, mem_map, Equiv.coe_toEmbedding, Subgraph.map, Set.mem_toFinset, Set.mem_image]
    constructor
    · rintro ⟨⟨a, ha, rfl⟩, hw⟩
      refine ⟨a, ⟨ha, ?_⟩, rfl⟩
      have hd := map_degree G H f T a
      change (T.map (fHom G H f)).degree (f a) = 1 at hw
      rwa [hd] at hw
    · rintro ⟨a, ⟨ha1, ha2⟩, rfl⟩
      refine ⟨⟨a, ha1, rfl⟩, ?_⟩
      have hd := map_degree G H f T a
      change (T.map (fHom G H f)).degree (f a) = 1
      rwa [←hd] at ha2
  have h_card : S2.card = S1.card := by
    rw [h_S2, card_map]
  exact h_card

lemma Ls_le_of_iso (f : G ≃g H) : Ls G ≤ Ls H := by
  unfold Ls
  let ST_G := { T : G.Subgraph | T.IsSpanning ∧ IsTree T.coe }
  let ST_H := { T : H.Subgraph | T.IsSpanning ∧ IsTree T.coe }
  by_cases h : ST_G = ∅
  · have h2 : (fun (T : G.Subgraph) => ((T.verts.toFinset.filter fun v => T.degree v = 1).card : ℝ)) '' ST_G = ∅ := by simp [h]
    rw [h2, Real.sSup_empty]
    by_cases hH : ST_H = ∅
    · have h3 : (fun (T : H.Subgraph) => ((T.verts.toFinset.filter fun v => T.degree v = 1).card : ℝ)) '' ST_H = ∅ := by simp [hH]
      rw [h3, Real.sSup_empty]
    · have hH_ne := Set.nonempty_iff_ne_empty.mpr hH
      rcases hH_ne with ⟨T, hT⟩
      have hl1 : 0 ≤ (((T.verts.toFinset.filter fun v => T.degree v = 1).card : ℝ)) := Nat.cast_nonneg _
      have hl2 : (((T.verts.toFinset.filter fun v => T.degree v = 1).card : ℝ)) ≤ sSup ((fun (T : H.Subgraph) => ((T.verts.toFinset.filter fun v => T.degree v = 1).card : ℝ)) '' ST_H) := by
        apply le_csSup
        · refine ⟨(Fintype.card β : ℝ), ?_⟩
          rintro _ ⟨S, _, rfl⟩
          have hc : (S.verts.toFinset.filter fun v => S.degree v = 1).card ≤ Fintype.card β := Finset.card_le_univ _
          exact Nat.cast_le.mpr hc
        · exact ⟨T, hT, rfl⟩
      exact hl1.trans hl2
  · have h_ne := Set.nonempty_iff_ne_empty.mpr h
    apply csSup_le
    · exact Set.Nonempty.image _ h_ne
    · rintro x ⟨T, ⟨h_span, h_tree⟩, rfl⟩
      have hT_eq : ((T.verts.toFinset.filter fun v => T.degree v = 1).card : ℝ) =
                (((T.map (fHom G H f)).verts.toFinset.filter fun v => (T.map (fHom G H f)).degree v = 1).card : ℝ) :=
        congrArg _ (map_leaves_card G H f T).symm
      have hl2 : (((T.map (fHom G H f)).verts.toFinset.filter fun v => (T.map (fHom G H f)).degree v = 1).card : ℝ) ≤ sSup ((fun (T : H.Subgraph) => ((T.verts.toFinset.filter fun v => T.degree v = 1).card : ℝ)) '' ST_H) := by
        apply le_csSup
        · refine ⟨(Fintype.card β : ℝ), ?_⟩
          rintro _ ⟨S, _, rfl⟩
          have hc : (S.verts.toFinset.filter fun v => S.degree v = 1).card ≤ Fintype.card β := Finset.card_le_univ _
          exact Nat.cast_le.mpr hc
        · refine ⟨T.map (fHom G H f), ⟨map_isSpanning G H f T h_span, map_isTree G H f T h_tree⟩, rfl⟩
      exact (le_of_eq hT_eq).trans hl2

theorem Ls_eq_of_iso (f : G ≃g H) : Ls G = Ls H := by
  apply le_antisymm
  · exact Ls_le_of_iso G H f
  · exact Ls_le_of_iso H G f.symm

end SimpleGraph
