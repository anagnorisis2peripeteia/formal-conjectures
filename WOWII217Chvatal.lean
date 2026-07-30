import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Card
import WOWII217BondyChvatal
import WOWII217ClosureSemantics
import WOWII217Ore

/-!
# Bondy–Chvátal path-closure and Chvátal’s path condition

Chvátal’s path condition is stated with finset order-statistics (no sorted lists):
the `i`-th ascending degree is `≤ B` iff at least `i` vertices have degree `≤ B`.
-/

namespace WOWII217Chvatal

open Classical SimpleGraph Finset
open WOWII217BondyChvatal
open WOWII217ClosureSemantics
open WOWII217Ore

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Path-closed: every missing edge has degree-sum `< n - 1`. -/
def IsPathClosed (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∀ ⦃u v : V⦄, u ≠ v → ¬ G.Adj u v →
    G.degree u + G.degree v < Fintype.card V - 1

noncomputable def pathClosureRound (G : SimpleGraph V) : SimpleGraph V := by
  classical
  exact addEligibleEdgesFrom G allDistinctPairs G

theorem le_pathClosureRound (G : SimpleGraph V) : G ≤ pathClosureRound G := by
  classical
  exact base_le_addEligibleEdgesFrom G G allDistinctPairs le_rfl

theorem traceable_pathClosureRound_iff [Nontrivial V] (G : SimpleGraph V) :
    Traceable (pathClosureRound G) ↔ Traceable G := by
  classical
  exact traceable_addEligibleEdgesFrom_iff G G allDistinctPairs le_rfl

noncomputable def pathClosureIter (G : SimpleGraph V) : Nat → SimpleGraph V
  | 0 => G
  | k + 1 => pathClosureRound (pathClosureIter G k)

theorem le_pathClosureIter (G : SimpleGraph V) : ∀ k, G ≤ pathClosureIter G k
  | 0 => le_rfl
  | k + 1 =>
      (le_pathClosureIter G k).trans (le_pathClosureRound (pathClosureIter G k))

theorem traceable_pathClosureIter_iff [Nontrivial V] (G : SimpleGraph V) :
    ∀ k, Traceable (pathClosureIter G k) ↔ Traceable G
  | 0 => Iff.rfl
  | k + 1 => by
      rw [pathClosureIter, traceable_pathClosureRound_iff,
        traceable_pathClosureIter_iff G k]

theorem eq_top_of_isPathClosed_of_ore (G : SimpleGraph V) [DecidableRel G.Adj]
    (hClosed : IsPathClosed G)
    (hOre : ∀ u v : V, u ≠ v → ¬ G.Adj u v →
      Fintype.card V - 1 ≤ G.degree u + G.degree v) :
    G = (⊤ : SimpleGraph V) := by
  ext u v
  constructor
  · exact fun h => Adj.ne h
  · intro hne
    have hne' : u ≠ v := by simpa [top_adj] using hne
    by_contra hnot
    exact absurd (hOre u v hne' hnot) (not_le.mpr (hClosed hne' hnot))

theorem traceable_of_isPathClosed_of_ore [Nontrivial V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hClosed : IsPathClosed G)
    (hOre : ∀ u v : V, u ≠ v → ¬ G.Adj u v →
      Fintype.card V - 1 ≤ G.degree u + G.degree v) :
    Traceable G := by
  rw [eq_top_of_isPathClosed_of_ore G hClosed hOre]
  exact traceable_top

/-- Enough rounds that edge-count cannot strictly increase on every step
(`binom(n,2)` undirected edges ≤ `n^2`, so `n^2+1` steps forces a path-closed iterate). -/
noncomputable def pathClosure (G : SimpleGraph V) : SimpleGraph V :=
  pathClosureIter G (Fintype.card V * Fintype.card V + 1)

theorem traceable_pathClosure_iff [Nontrivial V] (G : SimpleGraph V) :
    Traceable (pathClosure G) ↔ Traceable G :=
  traceable_pathClosureIter_iff G _

/-! ## Chvátal path condition via finset counts -/

/--
Chvátal path condition, order-statistic form:
for all `i` with `1 ≤ i ≤ n/2`, if at least `i` vertices have degree `≤ i`
(i.e. the `i`-th ascending degree is `≤ i`), then at least `i` vertices have
degree `≥ n - i`.
-/
def MeetsChvatalPath (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∀ i : ℕ, 1 ≤ i → i ≤ Fintype.card V / 2 →
    i ≤ card (univ.filter fun v : V => G.degree v ≤ i) →
      -- `dᵢ ≤ i → dₙ₋ᵢ ≥ n-i` is `card{deg ≤ n-i-1} ≤ n-i-1`,
      -- i.e. `card{deg ≥ n-i} ≥ i+1`.
      i + 1 ≤ card (univ.filter fun v : V => Fintype.card V - i ≤ G.degree v)

theorem degree_le_of_not_adj_of_isPathClosed (G : SimpleGraph V) [DecidableRel G.Adj]
    (hClosed : IsPathClosed G) {u w : V} (hne : u ≠ w) (hnot : ¬ G.Adj u w) :
    G.degree w ≤ Fintype.card V - 2 - G.degree u := by
  have := hClosed hne hnot
  omega

theorem card_not_adj (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) :
    card (univ.filter fun w => ¬ G.Adj x w) = Fintype.card V - G.degree x := by
  have hpart :
      card (univ.filter fun w => G.Adj x w) +
        card (univ.filter fun w => ¬ G.Adj x w) = Fintype.card V := by
    simpa [card_univ] using
      (card_filter_add_card_filter_not
        (s := (univ : Finset V)) (p := fun w : V => G.Adj x w))
  have hdeg : card (univ.filter fun w => G.Adj x w) = G.degree x := by
    rw [← G.neighborFinset_eq_filter (v := x)]
    exact G.card_neighborFinset_eq_degree x
  omega

theorem degree_eq_card_sub_one_iff (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) :
    G.degree x = Fintype.card V - 1 ↔ ∀ y : V, x ≠ y → G.Adj x y := by
  classical
  constructor
  · intro hdeg y hy
    have hN : G.neighborFinset x = univ.erase x := by
      apply Finset.eq_of_subset_of_card_le
      · intro z hz
        exact mem_erase.mpr ⟨by
          intro hzx; subst z; exact (G.loopless x) (by simpa [mem_neighborFinset] using hz),
          mem_univ z⟩
      · rw [G.card_neighborFinset_eq_degree, hdeg, card_erase_of_mem (mem_univ x), card_univ]
    have : y ∈ G.neighborFinset x := by
      rw [hN]; exact mem_erase.mpr ⟨hy.symm, mem_univ y⟩
    simpa [mem_neighborFinset] using this
  · intro hAdj
    have hN : G.neighborFinset x = univ.erase x := by
      ext y
      constructor
      · intro hy
        have hadj : G.Adj x y := by simpa [mem_neighborFinset] using hy
        exact mem_erase.mpr ⟨(G.ne_of_adj hadj).symm, mem_univ y⟩
      · intro hy
        have hne : y ≠ x := (mem_erase.mp hy).1
        simpa [mem_neighborFinset] using hAdj y (Ne.symm hne)
    calc
      G.degree x = card (G.neighborFinset x) := (G.card_neighborFinset_eq_degree x).symm
      _ = card (univ.erase x) := by rw [hN]
      _ = Fintype.card V - 1 := by simp [card_erase_of_mem (mem_univ x), card_univ]

theorem exists_not_adj_of_degree_le_card_sub_two
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V)
    (hx : G.degree x ≤ Fintype.card V - 2)
    (hn : 2 ≤ Fintype.card V) :
    ∃ w : V, x ≠ w ∧ ¬ G.Adj x w := by
  classical
  by_contra h
  push_neg at h
  have hAdj : ∀ y : V, x ≠ y → G.Adj x y := fun y hy => h y hy
  have hdeg : G.degree x = Fintype.card V - 1 :=
    (degree_eq_card_sub_one_iff G x).2 hAdj
  have hlt : G.degree x < G.degree x := by
    calc
      G.degree x ≤ Fintype.card V - 2 := hx
      _ < Fintype.card V - 1 := Nat.sub_lt_sub_left hn (by omega : (1 : ℕ) < 2)
      _ = G.degree x := hdeg.symm
  exact (lt_irrefl _ hlt).elim

/-- Path-closed + Chvátal path ⇒ complete. -/
theorem eq_top_of_isPathClosed_of_chvatal [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hClosed : IsPathClosed G) (hChv : MeetsChvatalPath G) :
    G = (⊤ : SimpleGraph V) := by
  classical
  let n := Fintype.card V
  by_cases hAll : ∀ v : V, n - 1 ≤ G.degree v
  · ext u v
    constructor
    · exact fun h => Adj.ne h
    · intro hTop
      have hne : u ≠ v := by simpa [top_adj] using hTop
      by_contra hnot
      have hsum : n - 1 ≤ G.degree u + G.degree v := by
        have hu := hAll u; have hv := hAll v; omega
      have := hClosed hne hnot
      omega
  · -- Not every vertex is universal ⇒ contradiction with path-closed + Chvátal.
    have hfalse : False := by
      push_neg at hAll
      obtain ⟨x0, hx0⟩ := hAll
      have hx0' : G.degree x0 ≤ n - 2 := by
        have := G.degree_lt_card_verts x0; omega
      let U : Finset V := univ.filter fun v => G.degree v ≤ n - 2
      have hx0U : x0 ∈ U := mem_filter.mpr ⟨mem_univ _, hx0'⟩
      obtain ⟨x, hxU, hxmax⟩ := U.exists_max_image (fun v => G.degree v) ⟨x0, hx0U⟩
      have hx_le : G.degree x ≤ n - 2 := (mem_filter.mp hxU).2
      let k := G.degree x
      have hk_le : k ≤ n - 2 := hx_le
      have hn2 : 2 ≤ n := by
        have hlt := G.degree_lt_card_verts x0
        omega
      have hne_univ : ∃ w : V, x ≠ w ∧ ¬ G.Adj x w :=
        exists_not_adj_of_degree_le_card_sub_two G x (by simpa [n] using hk_le)
          (by simpa [n] using hn2)
      let low : Finset V := univ.filter fun w => ¬ G.Adj x w
      have hlow_card : card low = n - k := by
        simpa [low, n, k] using card_not_adj G x
      have hx_low : x ∈ low := by simp [low, G.loopless]
      have hall_le_k : ∀ w ∈ low, G.degree w ≤ k := by
        intro w hw
        by_cases hwx : w = x
        · subst w; rfl
        · have hnot : ¬ G.Adj x w := (mem_filter.mp hw).2
          have hwU : w ∈ U := by
            refine mem_filter.mpr ⟨mem_univ w, ?_⟩
            by_contra hge
            push_neg at hge
            have hdeg : G.degree w = n - 1 := by
              have := G.degree_lt_card_verts w; omega
            have hadj : G.Adj x w := by
              have hwx' : w ≠ x := hwx
              have := (degree_eq_card_sub_one_iff G w).1 hdeg x hwx'
              simpa [G.adj_comm] using this
            exact absurd hadj hnot
          exact hxmax w hwU
      have hlow_closed : ∀ w ∈ low, w ≠ x → G.degree w ≤ n - 2 - k := by
        intro w hw hwx
        have hnot : ¬ G.Adj x w := (mem_filter.mp hw).2
        simpa [n, k] using
          degree_le_of_not_adj_of_isPathClosed G hClosed (Ne.symm hwx)
            (by simpa [G.adj_comm] using hnot)
      have hpool_k : n - k ≤ card (univ.filter fun v => G.degree v ≤ k) := by
        have hsub : low ⊆ univ.filter fun v => G.degree v ≤ k := by
          intro w hw; exact mem_filter.mpr ⟨mem_univ w, hall_le_k w hw⟩
        calc n - k = card low := hlow_card.symm
          _ ≤ _ := card_le_card hsub
      have hM := hChv
      by_cases hk0 : k = 0
      · have hall0 : ∀ v : V, G.degree v = 0 := by
          intro v
          have hv : v ∈ low := by
            simp only [low, mem_filter, mem_univ, true_and]
            intro hadj
            have hpos : 0 < G.degree x := by
              rw [← G.card_neighborFinset_eq_degree]
              exact card_pos.mpr ⟨v, by simpa [mem_neighborFinset] using hadj⟩
            simp [k, hk0] at hpos
          have hle := hall_le_k v hv
          have : G.degree v ≤ 0 := by simpa [hk0] using hle
          exact Nat.eq_zero_of_le_zero this
        have hn2 : 2 ≤ n := by
          obtain ⟨w, hwne, _⟩ := hne_univ
          have : 1 < n := Fintype.one_lt_card_iff_nontrivial.mpr ⟨x, w, hwne⟩
          omega
        have hprem : 1 ≤ card (univ.filter fun v => G.degree v ≤ 1) := by
          have : x ∈ univ.filter fun v => G.degree v ≤ 1 := by
            simp [show G.degree x = 0 by simpa [k, hk0] using rfl]
          exact Nat.succ_le_of_lt (card_pos.mpr ⟨x, this⟩)
        have hcon := hM 1 (by omega) (by simpa [n] using (by omega : 1 ≤ n / 2)) hprem
        -- hcon: 2 ≤ card {deg ≥ n-1}, but all degrees are 0
        have hempty : card (univ.filter fun v => n - 1 ≤ G.degree v) = 0 := by
          have hnone : ∀ v, v ∉ univ.filter fun v => n - 1 ≤ G.degree v := by
            intro v hv
            have hge : n - 1 ≤ G.degree v := (mem_filter.mp hv).2
            have := hall0 v
            omega
          simpa using card_eq_zero.mpr (eq_empty_iff_forall_notMem.mpr hnone)
        have hcon' : 2 ≤ card (univ.filter fun v => n - 1 ≤ G.degree v) := by
          simpa [n] using hcon
        exact absurd hcon' (by omega)
      · have hk1 : 1 ≤ k := Nat.pos_of_ne_zero hk0
        by_cases hbd : 2 * k ≤ n - 2
        · -- Case A
          have hkn : k ≤ n / 2 := by
            have : 2 * k ≤ n := by omega
            omega
          have hprem : k ≤ card (univ.filter fun v => G.degree v ≤ k) := by
            have : k ≤ n - k := by omega
            exact this.trans hpool_k
          have hcon := hM k hk1 (by simpa [n] using hkn) hprem
          have hhigh_le : card (univ.filter fun v => n - k ≤ G.degree v) ≤ k := by
            let high : Finset V := univ.filter fun v => n - k ≤ G.degree v
            have hgap : k + 1 ≤ n - k := by omega
            have hdisj : Disjoint low high := by
              refine disjoint_left.mpr ?_
              intro w hwlow hwhigh
              have hle : G.degree w ≤ k := hall_le_k w hwlow
              have hge : n - k ≤ G.degree w := (mem_filter.mp hwhigh).2
              have : n - k ≤ k := le_trans hge hle
              omega
            have hcard_union : card (low ∪ high) ≤ n := by
              simpa [card_univ, n] using card_le_card (subset_univ (low ∪ high))
            have hsum : card low + card high ≤ n := by
              rw [← card_union_of_disjoint hdisj]; exact hcard_union
            have hsum' : n - k + card high ≤ n := by simpa [hlow_card] using hsum
            have hk_le_n : k ≤ n := by omega
            have : n - k + card high ≤ n - k + k := by
              rw [Nat.sub_add_cancel hk_le_n]; exact hsum'
            exact Nat.add_le_add_iff_left.mp this
          have hcon' : k + 1 ≤ card (univ.filter fun v => n - k ≤ G.degree v) := by
            simpa [n] using hcon
          exact Nat.not_succ_le_self k (hcon'.trans hhigh_le)
        · -- Case B: 2k > n-2
          push_neg at hbd
          have hbd' : n - 1 ≤ 2 * k := by omega
          let B : ℕ := n - 2 - k
          have hBdef : B = n - 2 - k := rfl
          have hpool_B : B + 1 ≤ card (univ.filter fun v => G.degree v ≤ B) := by
            have hsub : low.erase x ⊆ univ.filter fun v => G.degree v ≤ B := by
              intro w hw
              obtain ⟨hwx, hwlow⟩ := mem_erase.mp hw
              exact mem_filter.mpr ⟨mem_univ w, by
                have := hlow_closed w hwlow hwx
                simpa [B] using this⟩
            have hce : card (low.erase x) = card low - 1 := card_erase_of_mem hx_low
            have hB1 : B + 1 = n - k - 1 := by omega
            calc B + 1 = n - k - 1 := hB1
              _ = card low - 1 := by omega
              _ = card (low.erase x) := hce.symm
              _ ≤ _ := card_le_card hsub
          have hi1 : 1 ≤ B + 1 := Nat.succ_le_succ (Nat.zero_le _)
          have h2B : 2 * (B + 1) ≤ n := by
            have : B + 1 = n - 1 - k := by omega
            rw [this]; omega
          have hi2 : B + 1 ≤ n / 2 :=
            (Nat.le_div_iff_mul_le (by decide : (0 : ℕ) < 2)).2
              (by simpa [mul_comm] using h2B)
          have hprem : B + 1 ≤ card (univ.filter fun v => G.degree v ≤ B + 1) := by
            have hsub :
                univ.filter (fun v => G.degree v ≤ B) ⊆
                  univ.filter fun v => G.degree v ≤ B + 1 := by
              intro v hv
              exact mem_filter.mpr ⟨mem_univ v, Nat.le_succ_of_le (mem_filter.mp hv).2⟩
            exact hpool_B.trans (card_le_card hsub)
          have hcon := hM (B + 1) hi1 (by simpa [n] using hi2) hprem
          have hneed :
              B + 2 ≤
                card (univ.filter fun v => Fintype.card V - (B + 1) ≤ G.degree v) :=
            hcon
          have hthr : Fintype.card V - (B + 1) = k + 1 := by
            have hB : B + 1 = n - 1 - k := by
              have := hBdef
              omega
            rw [show Fintype.card V = n from rfl, hB]
            have hk : k + 1 ≤ n := by omega
            calc
              n - (n - 1 - k) = n - (n - (k + 1)) := by omega
              _ = k + 1 := Nat.sub_sub_self (by simpa [add_comm] using hk)
          have hneed' : B + 2 ≤ card (univ.filter fun v => k + 1 ≤ G.degree v) := by
            rwa [hthr] at hneed
          -- Any vertex of degree ≥ k+1 cannot be non-universal (x maximises degree on U),
          -- so it is universal: degree = n-1.
          have hhi_sub :
              univ.filter (fun v => k + 1 ≤ G.degree v) ⊆
                univ.filter fun v => G.degree v = n - 1 := by
            intro v hv
            have hge : k + 1 ≤ G.degree v := (mem_filter.mp hv).2
            by_cases hU : G.degree v ≤ n - 2
            · have hvU : v ∈ U := mem_filter.mpr ⟨mem_univ v, hU⟩
              have hle : G.degree v ≤ G.degree x := hxmax v hvU
              have hge' : G.degree x + 1 ≤ G.degree v := by simpa [k] using hge
              exact (lt_irrefl _ (lt_of_le_of_lt hle (Nat.lt_of_succ_le hge'))).elim
            · have hlt : n - 2 < G.degree v := lt_of_not_ge hU
              have hlt_n : G.degree v < n := by
                simpa [n] using G.degree_lt_card_verts v
              have hge : n - 1 ≤ G.degree v := by
                cases hn : n with
                | zero => omega
                | succ n' =>
                  simp only [hn] at hlt hlt_n ⊢
                  omega
              have : G.degree v = n - 1 := le_antisymm (Nat.le_of_lt_succ (by
                cases hn : n with
                | zero => omega
                | succ n' =>
                  simp only [hn] at hlt_n ⊢
                  exact hlt_n)) hge
              exact mem_filter.mpr ⟨mem_univ v, this⟩
          obtain ⟨w, hwne, hwnot⟩ := hne_univ
          have hwlow : w ∈ low := mem_filter.mpr ⟨mem_univ w, hwnot⟩
          have hdegw : G.degree w ≤ B := by
            have := hlow_closed w hwlow (Ne.symm hwne)
            simpa [B] using this
          have hmeet :
              card (univ.filter fun v => G.degree v = n - 1) ≤ G.degree w := by
            have hsub :
                univ.filter (fun v => G.degree v = n - 1) ⊆ G.neighborFinset w := by
              intro v hv
              have hdeg : G.degree v = n - 1 := (mem_filter.mp hv).2
              have hne : v ≠ w := by intro rfl; omega
              have := (degree_eq_card_sub_one_iff G v).1 hdeg w hne
              simpa [mem_neighborFinset, G.adj_comm] using this
            have := card_le_card hsub
            simpa [G.card_neighborFinset_eq_degree] using this
          have hleB : B + 2 ≤ B :=
            hneed'.trans <| (card_le_card hhi_sub).trans <| hmeet.trans hdegw
          have hleB' : B + 1 ≤ B := Nat.le_of_succ_le hleB
          exact Nat.not_succ_le_self B hleB'
    exact hfalse.elim


/-! ## Path-closure is eventually path-closed -/

theorem pathClosureRound_eq_self_of_isPathClosed
    (G : SimpleGraph V) [DecidableRel G.Adj] (h : IsPathClosed G) :
    pathClosureRound G = G := by
  classical
  ext u v
  constructor
  · intro hadj
    simp only [pathClosureRound] at hadj
    rw [adj_addEligibleEdgesFrom_iff] at hadj
    rcases hadj with hG | ⟨e, _hmem, hsum, hedge⟩
    · exact hG
    · by_cases hGadj : G.Adj u v
      · exact hGadj
      · have hedge' : ((u, v) = e ∨ (u, v) = e.swap) ∧ u ≠ v := by
          simpa [SimpleGraph.edge, SimpleGraph.fromEdgeSet_adj] using hedge
        have hne : u ≠ v := hedge'.2
        have hsum' : Fintype.card V - 1 ≤ G.degree u + G.degree v := by
          rcases hedge'.1 with he | he
          · -- (u, v) = e
            have hu : u = e.1 := congrArg Prod.fst he
            have hv : v = e.2 := congrArg Prod.snd he
            rw [hu, hv]; convert hsum
          · -- (u, v) = e.swap, so e.1 = v and e.2 = u
            have hu : u = e.2 := by
              simpa [Prod.swap] using congrArg Prod.fst he
            have hv : v = e.1 := by
              simpa [Prod.swap] using congrArg Prod.snd he
            rw [hu, hv, add_comm]; convert hsum
        have := h hne hGadj
        omega
  · exact fun hG => (le_pathClosureRound G) hG

noncomputable def orderedAdjCard (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  card ((univ : Finset (V × V)).filter fun p => p.1 ≠ p.2 ∧ G.Adj p.1 p.2)

theorem orderedAdjCard_le (G : SimpleGraph V) [DecidableRel G.Adj] :
    orderedAdjCard G ≤ Fintype.card V * Fintype.card V := by
  classical
  have hle :
      card ((univ : Finset (V × V)).filter fun p => p.1 ≠ p.2 ∧ G.Adj p.1 p.2) ≤
        card (univ : Finset (V × V)) :=
    card_filter_le _ _
  have hcard : card (univ : Finset (V × V)) = Fintype.card V * Fintype.card V := by
    simp [card_univ, Fintype.card_prod]
  simpa [orderedAdjCard] using hle.trans_eq hcard

theorem orderedAdjCard_lt_of_not_isPathClosed
    (G : SimpleGraph V) [DecidableRel G.Adj] (h : ¬ IsPathClosed G) :
    orderedAdjCard G < orderedAdjCard (pathClosureRound G) := by
  classical
  unfold IsPathClosed at h
  push_neg at h
  obtain ⟨a, b, hne, hnot, hsum⟩ := h
  have hadd : (pathClosureRound G).Adj a b := by
    simp only [pathClosureRound]
    rw [adj_addEligibleEdgesFrom_iff]
    refine Or.inr ⟨(a, b), mem_allDistinctPairs hne, ?_, ?_⟩
    · convert hsum
    · simp [SimpleGraph.edge, SimpleGraph.fromEdgeSet_adj, hne]
  have hsub :
      (univ : Finset (V × V)).filter (fun p => p.1 ≠ p.2 ∧ G.Adj p.1 p.2) ⊆
        (univ : Finset (V × V)).filter fun p =>
          p.1 ≠ p.2 ∧ (pathClosureRound G).Adj p.1 p.2 := by
    intro p hp
    obtain ⟨hp1, hp2⟩ := (mem_filter.mp hp).2
    exact mem_filter.mpr ⟨mem_univ p, hp1, (le_pathClosureRound G) hp2⟩
  have hss :
      (univ : Finset (V × V)).filter (fun p => p.1 ≠ p.2 ∧ G.Adj p.1 p.2) ⊂
        (univ : Finset (V × V)).filter fun p =>
          p.1 ≠ p.2 ∧ (pathClosureRound G).Adj p.1 p.2 :=
    (ssubset_iff_of_subset hsub).2
      ⟨(a, b), mem_filter.mpr ⟨mem_univ _, hne, hadd⟩, by simp [hnot]⟩
  simpa [orderedAdjCard] using card_lt_card hss

theorem isPathClosed_pathClosure (G : SimpleGraph V) :
    IsPathClosed (pathClosure G) := by
  classical
  let n := Fintype.card V
  let N := n * n + 1
  let e : ℕ → ℕ := fun t => orderedAdjCard (pathClosureIter G t)
  have he_le : ∀ t, e t ≤ n * n := fun t => by
    simpa [e, n] using orderedAdjCard_le (pathClosureIter G t)
  have hstep : ∀ t, ¬ IsPathClosed (pathClosureIter G t) → e t < e (t + 1) := by
    intro t ht
    simpa [e, pathClosureIter] using
      orderedAdjCard_lt_of_not_isPathClosed (pathClosureIter G t) ht
  by_contra hnot
  have hn2 : 2 ≤ n := by
    by_contra hle
    push_neg at hle
    have : IsPathClosed (pathClosure G) := by
      intro u v hne
      have : 1 < n := Fintype.one_lt_card_iff_nontrivial.mpr ⟨u, v, hne⟩
      omega
    exact hnot this
  have hprev : ∀ t ≤ N, ¬ IsPathClosed (pathClosureIter G t) := by
    intro t ht
    by_contra hC
    have hfix : ∀ s, pathClosureIter G (t + s) = pathClosureIter G t := by
      intro s
      induction s with
      | zero => rfl
      | succ s ih =>
        rw [show t + (s + 1) = (t + s) + 1 from Nat.add_succ t s, pathClosureIter, ih]
        have hC' : IsPathClosed (pathClosureIter G t) := hC
        simpa [ih] using pathClosureRound_eq_self_of_isPathClosed (pathClosureIter G t) hC'
    have heq : pathClosure G = pathClosureIter G t := by
      unfold pathClosure
      have hN : Fintype.card V * Fintype.card V + 1 = N := by simp [n, N]
      have hsplit : N = t + (N - t) := by omega
      rw [hN, hsplit, hfix]
    exact hnot (heq ▸ hC)
  have hdecr : ∀ t < N, e t < e (t + 1) := fun t ht =>
    hstep t (hprev t (Nat.le_of_lt ht))
  have hchain : e 0 + N ≤ e N := by
    have step : ∀ t ≤ N, e 0 + t ≤ e t := by
      intro t
      induction t with
      | zero => intro; simp
      | succ t ih =>
        intro ht
        have := hdecr t (by omega)
        have := ih (by omega)
        omega
    simpa using step N le_rfl
  have hle : e N ≤ n * n := he_le N
  have hge : N ≤ e N := (Nat.le_add_left N (e 0)).trans hchain
  have hstrict : n * n < N := by simp [N]
  exact (not_le_of_gt hstrict) (hge.trans hle)

theorem degree_le_pathClosure (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    G.degree v ≤ (pathClosure G).degree v :=
  G.degree_le_of_le (le_pathClosureIter G _)

/-- Chvátal is preserved under pointwise degree increase. -/
theorem meetsChvatalPath_of_degree_le
    (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hdeg : ∀ v, G.degree v ≤ H.degree v)
    (hG : MeetsChvatalPath G) : MeetsChvatalPath H := by
  classical
  intro i hi1 hi2 hprem
  let n := Fintype.card V
  -- Premise for H: i ≤ card {H.deg ≤ i}. Then {H.deg ≤ i} ⊆ {G.deg ≤ i},
  -- so i ≤ card {G.deg ≤ i}, and Chvátal on G gives i ≤ card {G.deg ≥ n-i}.
  -- And {G.deg ≥ n-i} ⊆ {H.deg ≥ n-i}.
  have hsub_low :
      univ.filter (fun v => H.degree v ≤ i) ⊆
        univ.filter fun v => G.degree v ≤ i := by
    intro v hv
    exact mem_filter.mpr ⟨mem_univ v, (hdeg v).trans (mem_filter.mp hv).2⟩
  have hpremG : i ≤ card (univ.filter fun v => G.degree v ≤ i) :=
    hprem.trans (card_le_card hsub_low)
  have hGout := hG i hi1 hi2 hpremG
  have hsub_high :
      univ.filter (fun v => Fintype.card V - i ≤ G.degree v) ⊆
        univ.filter fun v => Fintype.card V - i ≤ H.degree v := by
    intro v hv
    exact mem_filter.mpr ⟨mem_univ v, (mem_filter.mp hv).2.trans (hdeg v)⟩
  exact hGout.trans (card_le_card hsub_high)

/-- Chvátal’s theorem for Hamiltonian paths. -/
theorem traceable_of_chvatal [Nontrivial V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hChv : MeetsChvatalPath G) : Traceable G := by
  classical
  by_cases hδ : Fintype.card V - 1 ≤ 2 * G.minDegree
  · exact traceable_of_minDegree_half G hδ
  · let H := pathClosure G
    letI : DecidableRel H.Adj := Classical.decRel _
    have hClosed : IsPathClosed H := isPathClosed_pathClosure G
    have hdeg : ∀ v, G.degree v ≤ H.degree v := degree_le_pathClosure G
    have hChvH : MeetsChvatalPath H := meetsChvatalPath_of_degree_le G H hdeg hChv
    have hTop : H = (⊤ : SimpleGraph V) :=
      eq_top_of_isPathClosed_of_chvatal (V := V) H hClosed hChvH
    have hTraceH : Traceable H := by rw [hTop]; exact traceable_top
    exact (traceable_pathClosure_iff G).mp hTraceH


end WOWII217Chvatal
