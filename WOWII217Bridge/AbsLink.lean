import WOWII217Bridge.DegLink
import WOWII217Bridge.SmallNPattern

namespace AbsLink

open SimpleGraph Finset

/-- Abstract-`V` form of `DegLink.exists_ofFn_eq_reverse_degreeSequence`: for a graph on
any `V` with `card V = n`, some indexing of `V` by `Fin n` lists the degrees in
DESCENDING order, which is what the chunk theorems (and hence the branch theorems)
require in their `hFinTrans` hypothesis. -/
theorem exists_ofFn_eq_reverse {V : Type*} [Fintype V] [DecidableEq V] {n : Nat}
    (G : SimpleGraph V) [DecidableRel G.Adj] (hcard : Fintype.card V = n) :
    ∃ e : Fin n ≃ V,
      List.ofFn (fun v : Fin n => G.degree (e v)) = G.degreeSequence.reverse := by
  classical
  -- move to `Fin n`
  let f : Fin n ≃ V := (Fintype.equivFinOfCardEq hcard).symm
  let G' : SimpleGraph (Fin n) := G.comap f.toEmbedding
  let iso : G' ≃g G := SimpleGraph.Iso.comap f G
  letI : DecidableRel G'.Adj := fun u v => by
    change Decidable (G.Adj (f u) (f v)); infer_instance
  -- sort the copy by descending degree
  obtain ⟨p, hp⟩ := DegLink.exists_ofFn_eq_reverse_degreeSequence G'
  refine ⟨p.trans f, ?_⟩
  have hdeg : ∀ v : Fin n, G'.degree v = G.degree (f v) := fun v => (iso.degree_eq v).symm
  have hseq : G'.degreeSequence = G.degreeSequence := by
    unfold SimpleGraph.degreeSequence
    congr 1
    have hfun : (fun v : Fin n => G'.degree v) = (fun w : V => G.degree w) ∘ f := funext hdeg
    rw [hfun, ← Multiset.map_map]
    congr 1
    have : (Finset.univ : Finset (Fin n)).map f.toEmbedding = Finset.univ :=
      Finset.map_univ_equiv f
    simpa [Finset.map] using congrArg Finset.val this
  calc List.ofFn (fun v : Fin n => G.degree ((p.trans f) v))
      = List.ofFn (fun v : Fin n => G'.degree (p v)) := by
        refine congrArg _ (funext fun v => ?_); simpa using (hdeg (p v)).symm
    _ = G'.degreeSequence.reverse := hp
    _ = G.degreeSequence.reverse := by rw [hseq]

end AbsLink

