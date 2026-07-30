import WOWII217ClosureSemantics
import WOWII217BondyChvatal
import Mathlib.Data.Fin.Tuple.Sort

namespace DegSort

open SimpleGraph WOWII217FiniteBase WOWII217Closure WOWII217ClosureSemantics
open WOWII217BondyChvatal

/-- Ascending: `Tuple.sort` straight off the shelf. -/
theorem exists_degree_monotone_equiv {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] :
    ∃ e : Equiv.Perm (Fin n), Monotone (fun v => G.degree (e v)) :=
  ⟨Tuple.sort (fun v => G.degree v), by
    simpa [Function.comp] using Tuple.monotone_sort (fun v => G.degree v)⟩

/-- Descending, which is the order the chunk theorems use
(`[6, 6, 5, 5, 5, 5, 3, 1]` = vertex 0 has degree 6, …).
Obtained by pre-composing the ascending sort with `Fin.revPerm`. -/
theorem exists_degree_antitone_equiv {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] :
    ∃ e : Equiv.Perm (Fin n), Antitone (fun v => G.degree (e v)) := by
  refine ⟨Fin.revPerm.trans (Tuple.sort (fun v => G.degree v)), ?_⟩
  intro a b hab
  simp only [Equiv.trans_apply, Fin.revPerm_apply]
  exact Tuple.monotone_sort (fun v => G.degree v) (Fin.rev_le_rev.mpr hab)


/-- GENERAL relabelling lemma. Generalises `traceable_of_degreeSequence_*_up_to_equiv`
(`WOWII217Relabel13.lean:71`) from one hand-written sequence to any `n` and any degree
function. `certified` is what a chunk theorem supplies. -/
theorem traceable_of_degreeOrder {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (connected : G.Connected) (ds : Fin n → ℕ)
    (degreeOrder : ∃ e : Fin n ≃ Fin n, ∀ v : Fin n, G.degree (e v) = ds v)
    (certified : ∀ (H : SimpleGraph (Fin n)) [DecidableRel H.Adj],
        H.Connected → (∀ v : Fin n, H.degree v = ds v) → Traceable H) :
    Traceable G := by
  obtain ⟨e, degrees⟩ := degreeOrder
  let canonical : SimpleGraph (Fin n) := G.comap e.toEmbedding
  let iso : canonical ≃g G := SimpleGraph.Iso.comap e G
  letI : DecidableRel canonical.Adj := fun u v => by
    change Decidable (G.Adj (e u) (e v)); infer_instance
  have canonicalConnected : canonical.Connected := iso.connected_iff.mpr connected
  have canonicalDegrees : ∀ v : Fin n, canonical.degree v = ds v := by
    intro v
    calc canonical.degree v = G.degree (e v) := (iso.degree_eq v).symm
      _ = ds v := degrees v
  rcases certified canonical canonicalConnected canonicalDegrees with ⟨a, b, p, hp⟩
  exact ⟨e a, e b, p.map iso.toHom, hp.map iso.toHom e.bijective⟩


/-- The last link: if `ds` is an antitone REARRANGEMENT of `G`'s degrees, then some
relabelling of `G` realises `ds` exactly. Uses `Tuple.unique_antitone`: two antitone
rearrangements of the same tuple coincide. -/
theorem exists_degreeOrder_of_antitone_rearrangement {n : Nat}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (ds : Fin n → ℕ)
    (hanti : Antitone ds)
    (hperm : ∃ τ : Equiv.Perm (Fin n), ds = (fun v => G.degree v) ∘ τ) :
    ∃ e : Equiv.Perm (Fin n), ∀ v : Fin n, G.degree (e v) = ds v := by
  obtain ⟨τ, rfl⟩ := hperm
  obtain ⟨e, he⟩ := exists_degree_antitone_equiv G
  exact ⟨e, congrFun (Tuple.unique_antitone (f := fun v => G.degree v) he hanti)⟩

end DegSort






