import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Residue
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Finset.Card
import Mathlib.Data.Multiset.Sort

/-!
# Residue bounds under maximum degree ≤ 6

Exhaustive classification of **nonincreasing** sequences with entries `≤ 6`
and Havel–Hakimi `residueAux = 2`:

* length `≥ 16` — impossible;
* length `15` — sum is always odd (contradicts handshaking);
* length `14` — the only even-sum sequence is `List.replicate 14 6`.

Applied to simple graphs this yields `Fintype.card V ≤ 14` under
`residue G = 2` and `maxDegree ≤ 6`, and six-regularity at order 14.
-/

namespace WOWII217ResidueBound

open SimpleGraph List

variable {V : Type*}

/-! ## `residueAux` equations -/

theorem residueAux_nil : residueAux [] = 0 := by
  unfold residueAux; rfl

theorem residueAux_zero_cons (t : List ℕ) : residueAux (0 :: t) = 1 + t.length := by
  unfold residueAux; rfl

theorem residueAux_succ_cons (d : ℕ) (rest : List ℕ) :
    residueAux ((d + 1) :: rest) =
      residueAux (havelHakimiStep ((d + 1) :: rest)) := by
  conv_lhs => unfold residueAux
  show residueAux (havelHakimiStep ((d + 1) :: rest)) =
      residueAux (havelHakimiStep ((d + 1) :: rest))
  rfl

/-! ## Exhaustive enumeration tables -/

/-- Depth-first enumeration of nonincreasing sequences. -/
def forallNoninc (remaining maxAllowed : ℕ) (acc : List ℕ)
    (p : List ℕ → Bool) : Bool :=
  match remaining with
  | 0 => p acc
  | r + 1 =>
    (range (maxAllowed + 1)).all fun i =>
      let d := maxAllowed - i
      forallNoninc r d (acc ++ [d]) p

def noResidueTwoLen16 : Bool :=
  forallNoninc 16 6 [] fun s => !decide (residueAux s = 2)

theorem noResidueTwoLen16_eq_true : noResidueTwoLen16 = true := by
  native_decide

def residueTwoLen15ImpliesOddSum : Bool :=
  forallNoninc 15 6 [] fun s =>
    !decide (residueAux s = 2) || decide (s.sum % 2 = 1)

theorem residueTwoLen15ImpliesOddSum_eq_true :
    residueTwoLen15ImpliesOddSum = true := by
  native_decide

def residueTwoLen14EvenSumImpliesSixRegular : Bool :=
  forallNoninc 14 6 [] fun s =>
    !decide (residueAux s = 2) ||
      decide (s.sum % 2 = 1) || decide (s = replicate 14 6)

theorem residueTwoLen14EvenSumImpliesSixRegular_eq_true :
    residueTwoLen14EvenSumImpliesSixRegular = true := by
  native_decide

/-- Allowed even-sum residue-2 sequences of length 13 with max ≤ 6. -/
def allowedDegreeSeq13 (s : List ℕ) : Bool :=
  decide (
    s = [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ∨
    s = [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 4] ∨
    s = [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 5, 5] ∨
    s = [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 4, 4] ∨
    s = [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 5, 5, 4] ∨
    s = [6, 6, 6, 6, 6, 6, 6, 6, 6, 5, 5, 5, 5] ∨
    s = [6, 6, 6, 6, 6, 6, 6, 5, 5, 5, 5, 5, 5])

/-- Length-13 + residue 2 + max ≤ 6 ⇒ odd sum or one of the seven sequences. -/
def residueTwoLen13EvenSumImpliesAllowed : Bool :=
  forallNoninc 13 6 [] fun s =>
    !decide (residueAux s = 2) ||
      decide (s.sum % 2 = 1) || allowedDegreeSeq13 s

theorem residueTwoLen13EvenSumImpliesAllowed_eq_true :
    residueTwoLen13EvenSumImpliesAllowed = true := by
  native_decide

/-! ## Soundness of enumeration -/

theorem forall_mem_le_of_pairwise_cons {d : ℕ} {rest : List ℕ}
    (h : Pairwise (· ≥ ·) (d :: rest)) : ∀ x ∈ rest, x ≤ d :=
  fun x hx => rel_of_pairwise_cons h hx

/-- Soundness of `forallNoninc` with a fixed prefix. -/
theorem forallNoninc_sound (remaining maxAllowed : ℕ) (acc : List ℕ)
    (p : List ℕ → Bool) (h : forallNoninc remaining maxAllowed acc p = true)
    (tail : List ℕ) (hlen : tail.length = remaining)
    (hmax : ∀ x ∈ tail, x ≤ maxAllowed)
    (hpair : Pairwise (· ≥ ·) (acc ++ tail)) :
    p (acc ++ tail) = true := by
  induction remaining generalizing maxAllowed acc tail with
  | zero =>
    have : tail = [] := eq_nil_of_length_eq_zero hlen
    subst tail
    simpa [forallNoninc, List.append_nil] using h
  | succ r ih =>
    match tail with
    | [] => simp at hlen
    | d :: rest =>
      have hlen' : rest.length = r := by simp at hlen ⊢; omega
      have hd : d ≤ maxAllowed := hmax d (by simp)
      have hpair_suf : Pairwise (· ≥ ·) (d :: rest) :=
        (List.pairwise_append.mp hpair).2.1
      have hrest_le : ∀ x ∈ rest, x ≤ d := forall_mem_le_of_pairwise_cons hpair_suf
      have hall :
          (range (maxAllowed + 1)).all (fun i =>
              forallNoninc r (maxAllowed - i) (acc ++ [maxAllowed - i]) p) =
            true := by
        simpa [forallNoninc] using h
      have hi_mem : maxAllowed - d ∈ range (maxAllowed + 1) :=
        List.mem_range.mpr (Nat.lt_succ_of_le (Nat.sub_le _ _))
      have hbranch : forallNoninc r d (acc ++ [d]) p = true := by
        have := (List.all_eq_true.mp hall) (maxAllowed - d) hi_mem
        have hdi : maxAllowed - (maxAllowed - d) = d := Nat.sub_sub_self hd
        simpa [hdi] using this
      have hpair_ext : Pairwise (· ≥ ·) ((acc ++ [d]) ++ rest) := by
        simpa [List.append_assoc, List.singleton_append] using hpair
      simpa [List.append_assoc, List.singleton_append] using
        ih d (acc ++ [d]) hbranch rest hlen' hrest_le hpair_ext

theorem forallNoninc_sound_nil (n maxD : ℕ) (p : List ℕ → Bool)
    (h : forallNoninc n maxD [] p = true)
    (s : List ℕ) (hlen : s.length = n)
    (hmax : ∀ x ∈ s, x ≤ maxD)
    (hpair : Pairwise (· ≥ ·) s) :
    p s = true := by
  simpa using forallNoninc_sound n maxD [] p h s hlen hmax (by simpa using hpair)

/-! ## Degree-list helpers -/

theorem degreeList_length (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj] :
    ((Finset.univ.val.map fun v : V => G.degree v).sort (· ≥ ·)).length =
      Fintype.card V := by
  classical
  rw [Multiset.length_sort (· ≥ ·)]
  simp [Multiset.card_map, Finset.card_univ]

theorem degreeList_forall_le_maxDegree (G : SimpleGraph V) [Fintype V]
    [DecidableRel G.Adj] :
    ∀ x ∈ (Finset.univ.val.map fun v : V => G.degree v).sort (· ≥ ·),
      x ≤ G.maxDegree := by
  classical
  intro x hx
  have : x ∈ Multiset.map (fun v : V => G.degree v) Finset.univ.val :=
    (Multiset.mem_sort (· ≥ ·)).mp hx
  rcases Multiset.mem_map.mp this with ⟨v, _, rfl⟩
  exact G.degree_le_maxDegree v

theorem degreeList_pairwise (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj] :
    Pairwise (· ≥ ·)
      ((Finset.univ.val.map fun v : V => G.degree v).sort (· ≥ ·)) := by
  classical
  exact Multiset.pairwise_sort _ _

theorem degreeList_sum (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj] :
    List.sum ((Finset.univ.val.map fun v : V => G.degree v).sort (· ≥ ·)) =
      ∑ v : V, G.degree v := by
  classical
  let s : Multiset ℕ := Finset.univ.val.map fun v : V => G.degree v
  have h1 : List.sum (s.sort (· ≥ ·)) =
      Multiset.sum (↑(s.sort (· ≥ ·)) : Multiset ℕ) := rfl
  have h2 : (↑(s.sort (· ≥ ·)) : Multiset ℕ) = s := Multiset.sort_eq s (· ≥ ·)
  rw [h1, h2]
  change Multiset.sum (Multiset.map (fun v : V => G.degree v) Finset.univ.val) =
    ∑ v : V, G.degree v
  rw [Finset.sum_eq_multiset_sum]

theorem degree_sum_even (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj] :
    Even (∑ v : V, G.degree v) := by
  classical
  rw [sum_degrees_eq_twice_card_edges]
  exact even_two_mul _

/-! ## Havel–Hakimi step preserves bounds and order -/

theorem havelHakimiStep_forall_le {M : ℕ} :
    ∀ s : List ℕ, (∀ x ∈ s, x ≤ M) → ∀ x ∈ havelHakimiStep s, x ≤ M := by
  intro s hs x hx
  match s with
  | [] => simp [havelHakimiStep] at hx
  | d :: rest =>
    simp only [havelHakimiStep, mem_mergeSort, splitAt_eq] at hx
    rcases mem_append.mp hx with h | h
    · rcases mem_map.mp h with ⟨y, hy, rfl⟩
      have hy' : y ∈ rest := List.mem_of_mem_take hy
      exact (Nat.sub_le y 1).trans (hs y (mem_cons_of_mem _ hy'))
    · have hx' : x ∈ rest := List.mem_of_mem_drop h
      exact hs x (mem_cons_of_mem _ hx')

theorem havelHakimiStep_pairwise (s : List ℕ) :
    Pairwise (· ≥ ·) (havelHakimiStep s) := by
  match s with
  | [] => simp [havelHakimiStep]
  | d :: rest =>
    simp only [havelHakimiStep]
    have hp : Pairwise (fun a b : ℕ => decide (a ≥ b) = true)
        (((rest.splitAt d).1.map (· - 1) ++ (rest.splitAt d).2).mergeSort
          fun a b => decide (a ≥ b)) := by
      apply pairwise_mergeSort
      · intro a b c hab hbc
        simp only [decide_eq_true_eq] at hab hbc ⊢
        exact Nat.le_trans hbc hab
      · intro a b
        simp only [Bool.or_eq_true, decide_eq_true_eq]
        exact Nat.le_total b a
    refine Pairwise.imp ?_ hp
    intro a b h
    exact of_decide_eq_true h

/-! ## Length ≥ 16 ⇒ residue ≠ 2 -/

theorem residueAux_ne_two_of_length_ge_sixteen
    (s : List ℕ) (hlen : 16 ≤ s.length) (hmax : ∀ x ∈ s, x ≤ 6)
    (hpair : Pairwise (· ≥ ·) s) : residueAux s ≠ 2 := by
  suffices ∀ n, ∀ t : List ℕ, t.length = n → 16 ≤ t.length →
      (∀ x ∈ t, x ≤ 6) → Pairwise (· ≥ ·) t → residueAux t ≠ 2 by
    exact this s.length s rfl hlen hmax hpair
  intro n
  refine Nat.strong_induction_on n ?_
  intro n ihn t htlen hlen hmax hpair
  subst htlen
  match t with
  | [] => simp at hlen
  | d :: rest =>
    cases d with
    | zero =>
      intro hres
      rw [residueAux_zero_cons] at hres
      have : 16 ≤ rest.length + 1 := hlen
      omega
    | succ d' =>
      intro hres
      rw [residueAux_succ_cons] at hres
      set u := havelHakimiStep ((d' + 1) :: rest)
      have ulen : u.length = rest.length :=
        havelHakimiStep_length_cons (d' + 1) rest
      have u_lt : u.length < ((d' + 1) :: rest).length := by
        simp [ulen]
      have umax : ∀ x ∈ u, x ≤ 6 := havelHakimiStep_forall_le _ hmax
      have upair : Pairwise (· ≥ ·) u := havelHakimiStep_pairwise _
      by_cases hu16 : 16 ≤ u.length
      · exact ihn u.length u_lt u rfl hu16 umax upair hres
      · have ht16 : ((d' + 1) :: rest).length = 16 := by
          have : u.length ≤ 15 := by omega
          have : 16 ≤ rest.length + 1 := hlen
          simp [ulen] at this ⊢
          omega
        have hbool := noResidueTwoLen16_eq_true
        have hp :
            (!decide (residueAux ((d' + 1) :: rest) = 2)) = true :=
          forallNoninc_sound_nil 16 6
            (fun s => !decide (residueAux s = 2))
            (by simpa [noResidueTwoLen16] using hbool)
            ((d' + 1) :: rest) ht16 hmax hpair
        have : residueAux ((d' + 1) :: rest) ≠ 2 := by simpa using hp
        exact this (by
          rw [residueAux_succ_cons]
          exact hres)

/-! ## Graph-level conclusions -/

/-- Under `residue = 2` and `maxDegree ≤ 6`, there are at most 14 vertices. -/
theorem card_le_fourteen_of_residue_eq_two_of_maxDegree_le_six
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hRes : residue G = 2) (hMax : G.maxDegree ≤ 6) :
    Fintype.card V ≤ 14 := by
  classical
  let s := (Finset.univ.val.map fun v : V => G.degree v).sort (· ≥ ·)
  have hres : residueAux s = 2 := by
    change residueAux s = 2
    simpa [residue] using hRes
  have hlen : s.length = Fintype.card V := degreeList_length G
  have hmax : ∀ x ∈ s, x ≤ 6 := by
    intro x hx
    exact (degreeList_forall_le_maxDegree G x hx).trans hMax
  have hpair : Pairwise (· ≥ ·) s := degreeList_pairwise G
  by_contra hgt
  have : 15 ≤ Fintype.card V := by omega
  by_cases h16 : 16 ≤ Fintype.card V
  · have : residueAux s ≠ 2 :=
      residueAux_ne_two_of_length_ge_sixteen s
        (by rw [hlen]; exact h16) hmax hpair
    exact this hres
  · have hcard15 : Fintype.card V = 15 := by omega
    have hlen15 : s.length = 15 := by rw [hlen, hcard15]
    have hbool := residueTwoLen15ImpliesOddSum_eq_true
    have hp :
        (!decide (residueAux s = 2) || decide (s.sum % 2 = 1)) = true :=
      forallNoninc_sound_nil 15 6 _
        (by simpa [residueTwoLen15ImpliesOddSum] using hbool)
        s hlen15 hmax hpair
    have hodd : s.sum % 2 = 1 := by
      simp only [hres, decide_true, Bool.not_true, Bool.false_or,
        decide_eq_true_eq] at hp
      exact hp
    have heven : Even s.sum := by
      have := degree_sum_even G
      simpa [degreeList_sum G, s] using this
    rcases heven with ⟨k, hk⟩
    omega

/-- Under `residue = 2`, `maxDegree ≤ 6` and `card = 14`, the graph is 6-regular. -/
theorem six_regular_of_card_eq_fourteen_of_residue_eq_two_of_maxDegree_le_six
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : Fintype.card V = 14)
    (hRes : residue G = 2) (hMax : G.maxDegree ≤ 6) :
    ∀ v : V, G.degree v = 6 := by
  classical
  let s := (Finset.univ.val.map fun v : V => G.degree v).sort (· ≥ ·)
  have hres : residueAux s = 2 := by
    change residueAux s = 2
    simpa [residue] using hRes
  have hlen : s.length = 14 := by
    rw [degreeList_length G, hcard]
  have hmax : ∀ x ∈ s, x ≤ 6 := by
    intro x hx
    exact (degreeList_forall_le_maxDegree G x hx).trans hMax
  have hpair : Pairwise (· ≥ ·) s := degreeList_pairwise G
  have hbool := residueTwoLen14EvenSumImpliesSixRegular_eq_true
  have hp :
      (!decide (residueAux s = 2) || decide (s.sum % 2 = 1) ||
          decide (s = replicate 14 6)) =
        true :=
    forallNoninc_sound_nil 14 6 _
      (by simpa [residueTwoLen14EvenSumImpliesSixRegular] using hbool)
      s hlen hmax hpair
  have hdisj : s.sum % 2 = 1 ∨ s = replicate 14 6 := by
    simp only [hres, decide_true, Bool.not_true, Bool.false_or,
      Bool.or_eq_true, decide_eq_true_eq] at hp
    exact hp
  have heven : Even s.sum := by
    have := degree_sum_even G
    simpa [degreeList_sum G, s] using this
  have hs6 : s = replicate 14 6 := by
    rcases hdisj with hodd | hs6
    · rcases heven with ⟨k, hk⟩
      omega
    · exact hs6
  intro v
  have hv : G.degree v ∈ s := by
    have : G.degree v ∈
        Multiset.map (fun w : V => G.degree w) Finset.univ.val :=
      Multiset.mem_map.mpr ⟨v, by simp, rfl⟩
    exact (Multiset.mem_sort (· ≥ ·)).mpr this
  have hv6 : G.degree v ∈ replicate 14 6 := hs6 ▸ hv
  exact List.eq_of_mem_replicate hv6

/-- Under `residue = 2`, `maxDegree ≤ 6` and `card = 13`, the descending degree
list is one of the seven even-sum residue-2 sequences. -/
theorem degreeList_eq_allowed_of_card_eq_thirteen_of_residue_eq_two_of_maxDegree_le_six
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : Fintype.card V = 13)
    (hRes : residue G = 2) (hMax : G.maxDegree ≤ 6) :
    let s := (Finset.univ.val.map fun v : V => G.degree v).sort (· ≥ ·)
    s = [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ∨
    s = [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 4] ∨
    s = [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 5, 5] ∨
    s = [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 4, 4] ∨
    s = [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 5, 5, 4] ∨
    s = [6, 6, 6, 6, 6, 6, 6, 6, 6, 5, 5, 5, 5] ∨
    s = [6, 6, 6, 6, 6, 6, 6, 5, 5, 5, 5, 5, 5] := by
  classical
  let s := (Finset.univ.val.map fun v : V => G.degree v).sort (· ≥ ·)
  have hres : residueAux s = 2 := by
    change residueAux s = 2
    simpa [residue] using hRes
  have hlen : s.length = 13 := by
    rw [degreeList_length G, hcard]
  have hmax : ∀ x ∈ s, x ≤ 6 := by
    intro x hx
    exact (degreeList_forall_le_maxDegree G x hx).trans hMax
  have hpair : Pairwise (· ≥ ·) s := degreeList_pairwise G
  have hbool := residueTwoLen13EvenSumImpliesAllowed_eq_true
  have hp :
      (!decide (residueAux s = 2) || decide (s.sum % 2 = 1) ||
          allowedDegreeSeq13 s) =
        true :=
    forallNoninc_sound_nil 13 6 _
      (by simpa [residueTwoLen13EvenSumImpliesAllowed] using hbool)
      s hlen hmax hpair
  have hdisj : s.sum % 2 = 1 ∨ allowedDegreeSeq13 s = true := by
    simp only [hres, decide_true, Bool.not_true, Bool.false_or,
      Bool.or_eq_true, decide_eq_true_eq] at hp
    -- hp : False ∨ s.sum % 2 = 1 ∨ allowedDegreeSeq13 s = true
    simpa using hp
  have heven : Even s.sum := by
    have := degree_sum_even G
    simpa [degreeList_sum G, s] using this
  have hallowed : allowedDegreeSeq13 s = true := by
    rcases hdisj with hodd | hallowed
    · rcases heven with ⟨k, hk⟩
      omega
    · exact hallowed
  -- Unfold the Bool disjunction into a Prop disjunction.
  have hdec : allowedDegreeSeq13 s = true ↔
      (s = [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ∨
        s = [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 4] ∨
        s = [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 5, 5] ∨
        s = [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 4, 4] ∨
        s = [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 5, 5, 4] ∨
        s = [6, 6, 6, 6, 6, 6, 6, 6, 6, 5, 5, 5, 5] ∨
        s = [6, 6, 6, 6, 6, 6, 6, 5, 5, 5, 5, 5, 5]) := by
    simp [allowedDegreeSeq13, decide_eq_true_eq]
  exact hdec.mp hallowed

end WOWII217ResidueBound


