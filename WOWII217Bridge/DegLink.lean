import WOWII217Bridge.DegreeSort
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Degrees

namespace DegLink

open SimpleGraph Finset

variable {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

/-- `List.ofFn` of the degrees is a permutation of the degree multiset. -/
theorem ofFn_degree_perm :
    List.Perm (List.ofFn fun v : Fin n => G.degree v) G.degreeSequence := by
  classical
  have h1 : (Multiset.ofList (List.ofFn fun v : Fin n => G.degree v))
      = Multiset.map (fun v : Fin n => G.degree v) Finset.univ.val := by
    simp [List.ofFn_eq_map, Finset.univ, Fintype.elems]
  have h2 : (Multiset.ofList G.degreeSequence)
      = Multiset.map (fun v : Fin n => G.degree v) Finset.univ.val := by
    rw [SimpleGraph.degreeSequence]
    exact Multiset.sort_eq _ _
  exact Quotient.exact (h1.trans h2.symm)


/-- THE LINK: some relabelling of `G` realises the DESCENDING degree list, which is what
`fixedDegreeSequenceUpper` (indexed by vertex) actually requires. `degreeSequence` is
sorted ascending, so the target is its reverse. -/
theorem exists_ofFn_eq_reverse_degreeSequence :
    ∃ e : Equiv.Perm (Fin n),
      List.ofFn (fun v => G.degree (e v)) = G.degreeSequence.reverse := by
  classical
  obtain ⟨e, he⟩ := DegSort.exists_degree_antitone_equiv G
  refine ⟨e, ?_⟩
  have hperm : List.Perm (List.ofFn fun v => G.degree (e v)) G.degreeSequence.reverse := by
    refine List.Perm.trans ?_ (List.reverse_perm _).symm
    refine List.Perm.trans ?_ (ofFn_degree_perm G)
    exact e.ofFn_comp_perm (fun v => G.degree v)
  refine List.Perm.eq_of_pairwise' (r := (· ≥ ·)) ?_ ?_ hperm
  · rw [show (List.ofFn fun v => G.degree (e v)) = List.ofFn ((fun v => G.degree v) ∘ e) from rfl]
    exact (List.pairwise_ofFn.mpr fun i j h => he (le_of_lt h))
  · refine (List.pairwise_reverse).mpr ?_
    show List.Pairwise (· ≤ ·) _
    rw [SimpleGraph.degreeSequence]
    exact Multiset.sort_sorted _ _

end DegLink

