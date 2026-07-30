import WOWII217Chvatal
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Degrees

namespace ChvBridge

open SimpleGraph Finset WOWII217Chvatal

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Counting vertices by a degree predicate = counting entries of the degree sequence.
`degreeSequence` is the sorted multiset of degrees, so the two agree. -/
theorem length_filter_degreeSequence (G : SimpleGraph V) [DecidableRel G.Adj]
    (p : ℕ → Bool) :
    (G.degreeSequence.filter p).length
      = #(univ.filter fun v : V => p (G.degree v) = true) := by
  classical
  have hms : (Multiset.ofList G.degreeSequence)
      = Multiset.map (fun v : V => G.degree v) univ.val := by
    rw [SimpleGraph.degreeSequence]; exact Multiset.sort_eq _ _
  have h1 : (G.degreeSequence.filter p).length
      = Multiset.card (Multiset.filter (fun d => p d = true) (Multiset.ofList G.degreeSequence)) := by
    simp [Multiset.filter_coe, List.countP_eq_length_filter]
  rw [h1, hms, Multiset.filter_map, Multiset.card_map]
  rfl

/-- List-level, decidable form of the Chvátal path condition. -/
def chvatalPathList (n : ℕ) (s : List ℕ) : Bool :=
  (List.range (n / 2 + 1)).all fun i =>
    !decide (1 ≤ i) ||
      !decide (i ≤ (s.filter (fun d => decide (d ≤ i))).length) ||
        decide (i + 1 ≤ (s.filter (fun d => decide (n - i ≤ d))).length)

/-- THE BRIDGE: the decidable list condition implies the graph condition. -/
theorem meetsChvatalPath_of_list (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : chvatalPathList (Fintype.card V) G.degreeSequence = true) :
    MeetsChvatalPath G := by
  classical
  intro i hi1 hi2 hprem
  have hmem : i ∈ List.range (Fintype.card V / 2 + 1) := by
    rw [List.mem_range]; omega
  have hall := List.all_eq_true.mp h i hmem
  simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
    decide_eq_true_eq, not_le] at hall
  rcases hall with (hlt | hlt) | hconc
  · omega
  · exfalso
    rw [length_filter_degreeSequence G (fun d => decide (d ≤ i))] at hlt
    simp only [decide_eq_true_eq] at hlt
    omega
  · rw [length_filter_degreeSequence G (fun d => decide (Fintype.card V - i ≤ d))] at hconc
    simpa using hconc


/-- Generalised: the count agrees for ANY list whose multiset is the degree multiset,
not just the ascending `degreeSequence`. The enumeration lemmas in
`WOWII217Bridge/DegreeEnum.lean` produce the DESCENDING sort, so this is the form
needed to consume them. -/
theorem length_filter_of_perm (G : SimpleGraph V) [DecidableRel G.Adj]
    (p : ℕ → Bool) (l : List ℕ)
    (hl : (Multiset.ofList l) = Multiset.map (fun v : V => G.degree v) univ.val) :
    (l.filter p).length = #(univ.filter fun v : V => p (G.degree v) = true) := by
  classical
  have h1 : (l.filter p).length
      = Multiset.card (Multiset.filter (fun d => p d = true) (Multiset.ofList l)) := by
    simp [Multiset.filter_coe, List.countP_eq_length_filter]
  rw [h1, hl, Multiset.filter_map, Multiset.card_map]
  rfl

/-- The descending sort has the degree multiset. -/
theorem descSort_multiset (G : SimpleGraph V) [DecidableRel G.Adj] :
    (Multiset.ofList ((univ.val.map fun v : V => G.degree v).sort (· ≥ ·)))
      = Multiset.map (fun v : V => G.degree v) univ.val :=
  Multiset.sort_eq _ _

/-- Consume an enumeration result directly: the descending degree list satisfying
`chvatalPathList` gives `MeetsChvatalPath`. -/
theorem meetsChvatalPath_of_descList (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : chvatalPathList (Fintype.card V)
          ((univ.val.map fun v : V => G.degree v).sort (· ≥ ·)) = true) :
    MeetsChvatalPath G := by
  classical
  intro i hi1 hi2 hprem
  have hmem : i ∈ List.range (Fintype.card V / 2 + 1) := by
    rw [List.mem_range]; omega
  have hall := List.all_eq_true.mp h i hmem
  simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
    decide_eq_true_eq, not_le] at hall
  rcases hall with (hlt | hlt) | hconc
  · omega
  · exfalso
    rw [length_filter_of_perm G (fun d => decide (d ≤ i)) _ (descSort_multiset G)] at hlt
    simp only [decide_eq_true_eq] at hlt
    omega
  · rw [length_filter_of_perm G (fun d => decide (Fintype.card V - i ≤ d)) _
      (descSort_multiset G)] at hconc
    simpa using hconc

end ChvBridge


