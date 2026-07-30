import FormalConjecturesUtil
import Mathlib.Combinatorics.SimpleGraph.Hamiltonian

/-! Foundational maximum-leaf lemmas for WOWII Graph Conjecture 217. -/

namespace WOWII217SpanningTree

open Classical SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def spanningLeafCount {G : SimpleGraph V} (T : G.Subgraph) : Nat :=
  (T.verts.toFinset.filter fun v => T.degree v = 1).card

/-- Arithmetic core of the leaf bound: a positive integer degree sequence with
tree degree sum has at least as many entries equal to one as the value of any
single entry. -/
theorem degreeSequence_le_leafCount
    (d : V → ℕ)
    (hpos : ∀ v, 0 < d v)
    (hsum : (∑ v, d v) + 2 = 2 * Fintype.card V)
    (v : V) :
    d v ≤ (Finset.univ.filter fun w => d w = 1).card := by
  classical
  let L : Finset V := Finset.univ.filter fun w => d w = 1
  let N : Finset V := Finset.univ.filter fun w => ¬d w = 1
  have hpartition : L.card + N.card = Fintype.card V := by
    simpa [L, N] using
      (Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset V))
        (p := fun w => d w = 1))
  by_cases hv : d v = 1
  · have hvL : v ∈ L := by simp [L, hv]
    have : 0 < L.card := Finset.card_pos.mpr ⟨v, hvL⟩
    simpa [L, hv] using this
  · have hvN : v ∈ N := by simp [N, hv]
    have hleafsum : ∑ w ∈ L, d w = L.card := by
      calc
        ∑ w ∈ L, d w = ∑ _w ∈ L, 1 := by
          apply Finset.sum_congr rfl
          intro w hw
          exact (Finset.mem_filter.mp hw).2
        _ = L.card := by simp
    have hrest : 2 * (N.erase v).card ≤ ∑ w ∈ N.erase v, d w := by
      calc
        2 * (N.erase v).card = ∑ _w ∈ N.erase v, 2 := by simp [Nat.mul_comm]
        _ ≤ ∑ w ∈ N.erase v, d w := by
          apply Finset.sum_le_sum
          intro w hw
          have hwN : w ∈ N := Finset.mem_of_mem_erase hw
          have hwne : ¬ d w = 1 := by simpa [N] using hwN
          have hwpos := hpos w
          omega
    have heraseCard : (N.erase v).card = N.card - 1 :=
      Finset.card_erase_of_mem hvN
    have heraseSum : (∑ w ∈ N.erase v, d w) + d v = ∑ w ∈ N, d w :=
      Finset.sum_erase_add N d hvN
    have hnonleaf : d v + 2 * (N.card - 1) ≤ ∑ w ∈ N, d w := by
      omega
    have hsplit : (∑ w ∈ L, d w) + ∑ w ∈ N, d w = ∑ w, d w := by
      simpa [L, N] using
        (Finset.sum_filter_add_sum_filter_not (s := (Finset.univ : Finset V))
          (p := fun w => d w = 1) d)
    change d v ≤ L.card
    omega

/-- Any positive integer degree sequence with the degree sum of a nontrivial
tree has at least two entries equal to one. -/
theorem two_le_leafCount_of_degreeSequence
    [Nontrivial V]
    (d : V → ℕ)
    (hpos : ∀ v, 0 < d v)
    (hsum : (∑ v, d v) + 2 = 2 * Fintype.card V) :
    2 ≤ (Finset.univ.filter fun w => d w = 1).card := by
  classical
  by_cases hall : ∀ v, d v = 1
  · have hfilter : (Finset.univ.filter fun w => d w = 1) =
        (Finset.univ : Finset V) := by
      ext w
      simp [hall]
    rw [hfilter, Finset.card_univ]
    have hcard := Fintype.one_lt_card (α := V)
    omega
  · push_neg at hall
    obtain ⟨v, hv⟩ := hall
    have hdv : 2 ≤ d v := by
      have := hpos v
      omega
    exact hdv.trans (degreeSequence_le_leafCount d hpos hsum v)

/-- In a finite nontrivial tree, the degree of every vertex is at most the
number of leaves. -/
theorem tree_degree_le_leafCount (T : SimpleGraph V) [DecidableRel T.Adj]
    [Nontrivial V] (tree : IsTree T) (v : V) :
    T.degree v ≤ (Finset.univ.filter fun w => T.degree w = 1).card := by
  apply degreeSequence_le_leafCount (fun w => T.degree w)
  · exact fun w => tree.isConnected.preconnected.degree_pos_of_nontrivial w
  · have hedge := tree.card_edgeFinset
    have hsum := T.sum_degrees_eq_twice_card_edges
    omega

/-- A finite nontrivial tree has at least two leaves. -/
theorem tree_two_le_leafCount (T : SimpleGraph V) [DecidableRel T.Adj]
    [Nontrivial V] (tree : IsTree T) :
    2 ≤ (Finset.univ.filter fun w => T.degree w = 1).card := by
  apply two_le_leafCount_of_degreeSequence (fun w => T.degree w)
  · exact fun w => tree.isConnected.preconnected.degree_pos_of_nontrivial w
  · have hedge := tree.card_edgeFinset
    have hsum := T.sum_degrees_eq_twice_card_edges
    omega

/-- For a spanning tree represented as a subgraph, every subgraph degree is at
most its number of leaves. -/
theorem spanningTree_degree_le_leafCount {G : SimpleGraph V}
    [DecidableRel G.Adj] [Nontrivial V]
    (T : G.Subgraph) (spanning : T.IsSpanning) (tree : IsTree T.coe) (v : V) :
    T.degree v ≤ spanningLeafCount T := by
  have tree' : IsTree T.spanningCoe :=
    (T.spanningCoeEquivCoeOfSpanning spanning).isTree_iff.mpr tree
  have h := tree_degree_le_leafCount T.spanningCoe tree' v
  have hverts : T.verts = Set.univ := Subgraph.isSpanning_iff.mp spanning
  simpa [spanningLeafCount, hverts] using h

/-- A spanning tree of a finite nontrivial graph has at least two leaves. -/
theorem spanningTree_two_le_leafCount {G : SimpleGraph V}
    [DecidableRel G.Adj] [Nontrivial V]
    (T : G.Subgraph) (spanning : T.IsSpanning) (tree : IsTree T.coe) :
    2 ≤ spanningLeafCount T := by
  have tree' : IsTree T.spanningCoe :=
    (T.spanningCoeEquivCoeOfSpanning spanning).isTree_iff.mpr tree
  have h := tree_two_le_leafCount T.spanningCoe tree'
  have hverts : T.verts = Set.univ := Subgraph.isSpanning_iff.mp spanning
  simpa [spanningLeafCount, hverts] using h

/-- The graph consisting of all edges of `G` incident to one fixed vertex is
acyclic. -/
theorem incidenceStar_isAcyclic (G : SimpleGraph V) (v : V) :
    (fromEdgeSet (G.incidenceSet v)).IsAcyclic := by
  rw [isAcyclic_iff_forall_adj_isBridge]
  intro x y hxy
  rw [isBridge_iff]
  refine ⟨hxy, ?_⟩
  have hinc : s(x, y) ∈ G.incidenceSet v :=
    (fromEdgeSet_adj _).mp hxy |>.1
  have hvxy : v = x ∨ v = y := (G.mk'_mem_incidenceSet_iff.mp hinc).2
  rcases hvxy with rfl | rfl
  · intro hr
    have hvy : v ≠ y := hxy.ne
    have hysupp : y ∈
        (fromEdgeSet (G.incidenceSet v) \ fromEdgeSet {s(v, y)}).support :=
      mem_support_of_reachable hvy.symm hr.symm
    obtain ⟨z, hyz⟩ := (mem_support _).mp hysupp
    have hyzStar : (fromEdgeSet (G.incidenceSet v)).Adj y z :=
      (sdiff_adj _ _ _ _).mp hyz |>.1
    have hyzNotDeleted : ¬(fromEdgeSet {s(v, y)}).Adj y z :=
      (sdiff_adj _ _ _ _).mp hyz |>.2
    have hvyz : v = y ∨ v = z :=
      (G.mk'_mem_incidenceSet_iff.mp ((fromEdgeSet_adj _).mp hyzStar).1).2
    have hvz : v = z := hvyz.resolve_left hvy
    apply hyzNotDeleted
    subst z
    exact (fromEdgeSet_adj _).mpr ⟨by simp [Sym2.eq_swap], hyzStar.ne⟩
  · intro hr
    have hxv : x ≠ v := hxy.ne
    have hxsupp : x ∈
        (fromEdgeSet (G.incidenceSet v) \ fromEdgeSet {s(x, v)}).support :=
      mem_support_of_reachable hxv hr
    obtain ⟨z, hxz⟩ := (mem_support _).mp hxsupp
    have hxzStar : (fromEdgeSet (G.incidenceSet v)).Adj x z :=
      (sdiff_adj _ _ _ _).mp hxz |>.1
    have hxzNotDeleted : ¬(fromEdgeSet {s(x, v)}).Adj x z :=
      (sdiff_adj _ _ _ _).mp hxz |>.2
    have hvxz : v = x ∨ v = z :=
      (G.mk'_mem_incidenceSet_iff.mp ((fromEdgeSet_adj _).mp hxzStar).1).2
    have hvz : v = z := hvxz.resolve_left hxv.symm
    apply hxzNotDeleted
    subst z
    exact (fromEdgeSet_adj _).mpr ⟨by simp, hxzStar.ne⟩

/-- A connected finite graph has a spanning tree that preserves every edge
incident to a prescribed vertex, and therefore preserves that vertex's
degree. -/
theorem exists_spanningTree_preserving_degree
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (connected : G.Connected) (v : V) :
    ∃ T : G.Subgraph,
      T.IsSpanning ∧ IsTree T.coe ∧ T.degree v = G.degree v := by
  classical
  let S : SimpleGraph V := fromEdgeSet (G.incidenceSet v)
  have hSG : S ≤ G := by
    intro x y hxy
    exact (G.mk'_mem_incidenceSet_iff.mp ((fromEdgeSet_adj _).mp hxy).1).1
  have hSAcyclic : S.IsAcyclic := incidenceStar_isAcyclic G v
  obtain ⟨H, hSH, hmax⟩ :=
    exists_maximal_isAcyclic_of_le_isAcyclic hSG hSAcyclic
  have hHG : H ≤ G := hmax.prop.1
  have htreeH : H.IsTree :=
    (connected.maximal_le_isAcyclic_iff_isTree hHG).mp hmax
  let T : G.Subgraph := G.toSubgraph H hHG
  have hspanning : T.IsSpanning := SimpleGraph.toSubgraph.isSpanning H hHG
  have htreeT : IsTree T.coe := by
    have := (T.spanningCoeEquivCoeOfSpanning hspanning).isTree_iff.mp htreeH
    simpa [T] using this
  have hAdj : ∀ w, H.Adj v w ↔ G.Adj v w := by
    intro w
    constructor
    · exact fun h => hHG h
    · intro h
      apply hSH
      exact (fromEdgeSet_adj _).mpr
        ⟨G.mk'_mem_incidenceSet_left_iff.mpr h, h.ne⟩
  have hneighbor : H.neighborSet v = G.neighborSet v := by
    ext w
    simp only [mem_neighborSet, hAdj]
  have hdegree : H.degree v = G.degree v := by
    unfold SimpleGraph.degree
    congr 1
    ext w
    simp only [mem_neighborFinset, hAdj]
  refine ⟨T, hspanning, htreeT, ?_⟩
  simpa [T, hdegree]

theorem spanningTree_leafCount_le_Ls (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : G.Subgraph) (spanning : T.IsSpanning) (tree : IsTree T.coe) :
    (spanningLeafCount T : ℝ) ≤ Ls G := by
  classical
  unfold Ls spanningLeafCount
  apply le_csSup
  · refine ⟨(Fintype.card V : ℝ), ?_⟩
    rintro _ ⟨S, _, rfl⟩
    change ((S.verts.toFinset.filter fun v => S.degree v = 1).card : ℝ) ≤
      (Fintype.card V : ℝ)
    exact_mod_cast Finset.card_le_univ
      (S.verts.toFinset.filter fun v => S.degree v = 1)
  · exact ⟨T, ⟨spanning, tree⟩, rfl⟩

theorem spanningTree_leafCount_le_of_Ls_le (G : SimpleGraph V)
    [DecidableRel G.Adj] (bound : ℝ) (hL : Ls G ≤ bound)
    (T : G.Subgraph) (spanning : T.IsSpanning) (tree : IsTree T.coe) :
    (spanningLeafCount T : ℝ) ≤ bound :=
  (spanningTree_leafCount_le_Ls G T spanning tree).trans hL

/-- The maximum-leaf invariant dominates every vertex degree of a connected
finite nontrivial graph. -/
theorem degree_le_Ls (G : SimpleGraph V) [DecidableRel G.Adj]
    [Nontrivial V] (connected : G.Connected) (v : V) :
    (G.degree v : ℝ) ≤ Ls G := by
  obtain ⟨T, spanning, tree, hdegree⟩ :=
    exists_spanningTree_preserving_degree G connected v
  calc
    (G.degree v : ℝ) = T.degree v := by exact_mod_cast hdegree.symm
    _ ≤ spanningLeafCount T := by
      exact_mod_cast spanningTree_degree_le_leafCount T spanning tree v
    _ ≤ Ls G := spanningTree_leafCount_le_Ls G T spanning tree

/-- A connected graph whose maximum-leaf invariant is at most six has maximum
degree at most six. -/
theorem maxDegree_le_six_of_Ls_le_six (G : SimpleGraph V)
    [DecidableRel G.Adj] [Nontrivial V]
    (connected : G.Connected) (hL : Ls G ≤ 6) :
    G.maxDegree ≤ 6 := by
  apply G.maxDegree_le_of_forall_degree_le
  intro v
  have h : (G.degree v : ℝ) ≤ 6 := (degree_le_Ls G connected v).trans hL
  exact_mod_cast h

lemma ncard_neighborSet_eq_degree (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    (G.neighborSet v).ncard = G.degree v := by
  rw [Set.ncard_eq_toFinset_card']
  rfl

lemma ncard_subgraph_neighborSet_eq_degree {G : SimpleGraph V}
    [DecidableRel G.Adj] (H : G.Subgraph) (v : V) :
    (H.neighborSet v).ncard = H.degree v := by
  rw [Set.ncard_eq_toFinset_card']
  exact Subgraph.finset_card_neighborSet_eq_degree (G' := H) (v := v)

lemma path_neighborSet_eq_of_degree_le_two
    (T : SimpleGraph V) [DecidableRel T.Adj]
    {a b : V} {p : T.Walk a b}
    (hp : p.IsPath) (hab : a ≠ b)
    (ha : T.degree a = 1) (hb : T.degree b = 1)
    (hdeg : ∀ v, T.degree v ≤ 2)
    {x : V} (hx : x ∈ p.support) :
    p.toSubgraph.neighborSet x = T.neighborSet x := by
  apply Set.eq_of_subset_of_ncard_le (p.toSubgraph.neighborSet_subset x)
  by_cases hxa : x = a
  · subst x
    rw [ncard_neighborSet_eq_degree, ha,
      hp.neighborSet_toSubgraph_startpoint (Walk.not_nil_of_ne hab)]
    simp
  · by_cases hxb : x = b
    · subst x
      rw [ncard_neighborSet_eq_degree, hb,
        hp.neighborSet_toSubgraph_endpoint (Walk.not_nil_of_ne hab)]
      simp
    · obtain ⟨i, hix, hi⟩ := Walk.mem_support_iff_exists_getVert.mp hx
      have hi0 : i ≠ 0 := by
        intro h
        subst i
        simp only [Walk.getVert_zero] at hix
        exact hxa hix.symm
      have hilt : i < p.length := by
        apply lt_of_le_of_ne hi
        intro hil
        have : x = b := by
          rw [← hix, hil, Walk.getVert_length]
        exact hxb this
      calc
        (T.neighborSet x).ncard = T.degree x := ncard_neighborSet_eq_degree T x
        _ ≤ 2 := hdeg x
        _ = (p.toSubgraph.neighborSet x).ncard := by
          rw [← hix]
          exact (hp.ncard_neighborSet_toSubgraph_internal_eq_two hi0 hilt).symm

lemma mem_support_of_adj_of_path_degree_le_two
    (T : SimpleGraph V) [DecidableRel T.Adj]
    {a b : V} {p : T.Walk a b}
    (hp : p.IsPath) (hab : a ≠ b)
    (ha : T.degree a = 1) (hb : T.degree b = 1)
    (hdeg : ∀ v, T.degree v ≤ 2)
    {x y : V} (hx : x ∈ p.support) (hxy : T.Adj x y) :
    y ∈ p.support := by
  have heq := path_neighborSet_eq_of_degree_le_two T hp hab ha hb hdeg hx
  have h_in_T : y ∈ T.neighborSet x := hxy
  rw [← heq] at h_in_T
  exact p.mem_verts_toSubgraph.mp (Subgraph.neighborSet_subset_verts _ _ h_in_T)

lemma support_eq_univ_of_path_degree_le_two
    (T : SimpleGraph V) [DecidableRel T.Adj]
    (connected : T.Connected)
    {a b : V} {p : T.Walk a b}
    (hp : p.IsPath) (hab : a ≠ b)
    (ha : T.degree a = 1) (hb : T.degree b = 1)
    (hdeg : ∀ v, T.degree v ≤ 2) :
    ∀ y, y ∈ p.support := by
  intro y
  have hr : Relation.ReflTransGen T.Adj a y := by
    have hreach := connected.preconnected a y
    rw [reachable_eq_reflTransGen] at hreach
    exact hreach
  induction hr with
  | refl =>
    exact Walk.start_mem_support p
  | tail _ hxy ih =>
    exact mem_support_of_adj_of_path_degree_le_two T hp hab ha hb hdeg ih hxy

lemma isHamiltonian_of_path_degree_le_two
    (T : SimpleGraph V) [DecidableRel T.Adj]
    (connected : T.Connected)
    {a b : V} {p : T.Walk a b}
    (hp : p.IsPath) (hab : a ≠ b)
    (ha : T.degree a = 1) (hb : T.degree b = 1)
    (hdeg : ∀ v, T.degree v ≤ 2) :
    p.IsHamiltonian := by
  rw [hp.isHamiltonian_iff]
  exact support_eq_univ_of_path_degree_le_two T connected hp hab ha hb hdeg


theorem exists_hamiltonianPath_of_Ls_le_two (G : SimpleGraph V) [DecidableRel G.Adj]
    [Nontrivial V] (connected : G.Connected) (hL : Ls G ≤ 2) :
    ∃ a b, ∃ p : G.Walk a b, p.IsHamiltonian := by
  obtain ⟨v0, _⟩ := exists_pair_ne V
  have hT := exists_spanningTree_preserving_degree G connected v0
  obtain ⟨T, hspanning, htree, _hdeg⟩ := hT
  have hLsT : spanningLeafCount T ≤ 2 := by
    have h1 : (spanningLeafCount T : ℝ) ≤ Ls G := spanningTree_leafCount_le_Ls G T hspanning htree
    exact_mod_cast h1.trans hL
  have hTleaves_ge_2 : 2 ≤ spanningLeafCount T := spanningTree_two_le_leafCount T hspanning htree
  have hTleaves : spanningLeafCount T = 2 := by omega
  have hfilter : (T.verts.toFinset.filter fun (w : V) => T.degree w = 1).card = 2 := hTleaves
  rw [Finset.card_eq_two] at hfilter
  obtain ⟨a, b, hab, hset⟩ := hfilter
  have ha1 : T.degree a = 1 := by
    have ha_in : a ∈ ({a, b} : Finset V) := by simp
    rw [← hset, Finset.mem_filter] at ha_in
    exact ha_in.2
  have hb1 : T.degree b = 1 := by
    have hb_in : b ∈ ({a, b} : Finset V) := by simp
    rw [← hset, Finset.mem_filter] at hb_in
    exact hb_in.2
  have hTdeg : ∀ v : T.verts, T.coe.degree v ≤ 2 := by
    intro v
    have hd := spanningTree_degree_le_leafCount T hspanning htree v.val
    have h1 := hd.trans (by omega : spanningLeafCount T ≤ 2)
    rw [Subgraph.coe_degree T v]
    convert h1
  have Tconn : T.coe.Connected := htree.isConnected
  have ha_vert : a ∈ T.verts := by
    have ha_in : a ∈ ({a, b} : Finset V) := by simp
    rw [← hset, Finset.mem_filter, Set.mem_toFinset] at ha_in
    exact ha_in.1
  have hb_vert : b ∈ T.verts := by
    have hb_in : b ∈ ({a, b} : Finset V) := by simp
    rw [← hset, Finset.mem_filter, Set.mem_toFinset] at hb_in
    exact hb_in.1
  let a_v : T.verts := ⟨a, ha_vert⟩
  let b_v : T.verts := ⟨b, hb_vert⟩
  have hab_v : a_v ≠ b_v := fun h => hab (congr_arg Subtype.val h)
  have ha1_v : T.coe.degree a_v = 1 := by
    rw [Subgraph.coe_degree T a_v]
    convert ha1
  have hb1_v : T.coe.degree b_v = 1 := by
    rw [Subgraph.coe_degree T b_v]
    convert hb1
  obtain ⟨p', hp'⟩ := (Tconn.preconnected a_v b_v).exists_isPath
  have T_ham : p'.IsHamiltonian := by
    apply isHamiltonian_of_path_degree_le_two T.coe Tconn hp' hab_v
    · convert ha1_v
    · convert hb1_v
    · intro v; convert hTdeg v
  have h_bij : Function.Bijective T.hom := by
    constructor
    · intro x y hxy
      exact Subtype.ext hxy
    · intro y
      have hy : y ∈ T.verts := hspanning.verts_eq_univ ▸ Set.mem_univ y
      exact ⟨⟨y, hy⟩, rfl⟩
  have pG_ham := T_ham.map T.hom h_bij
  exact ⟨a, b, p'.map T.hom, pG_ham⟩

end WOWII217SpanningTree
