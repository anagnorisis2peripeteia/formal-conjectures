import FormalConjecturesUtil
import Mathlib.Logic.Equiv.Fin.Rotate

/-!
The graph-theoretic semantics behind the finite closure certificates used for
WOWII 217.  This file proves the reusable counting core of the
Bondy--Chvátal edge-closure argument before constructing the rotated cycle.
-/

namespace WOWII217BondyChvatal

open Finset Function SimpleGraph

variable {V ι : Type*} [Fintype V] [DecidableEq V]

def Traceable (G : SimpleGraph V) : Prop :=
  ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian

/-- Add one new universal vertex, represented by `none`. -/
def coneAdj (G : SimpleGraph V) : Option V → Option V → Prop
  | none, none => False
  | some v, some w => G.Adj v w
  | none, some _ => True
  | some _, none => True

def cone (G : SimpleGraph V) : SimpleGraph (Option V) where
  Adj := coneAdj G
  symm := by
    intro v w h
    cases v <;> cases w <;> simp_all [coneAdj, G.adj_symm]
  loopless := by
    intro v
    cases v <;> simp [coneAdj]

@[simp] theorem cone_adj_none_none (G : SimpleGraph V) :
    ¬ (cone G).Adj none none := by simp [cone, coneAdj]

@[simp] theorem cone_adj_none_some (G : SimpleGraph V) (v : V) :
    (cone G).Adj none (some v) := by simp [cone, coneAdj]

@[simp] theorem cone_adj_some_none (G : SimpleGraph V) (v : V) :
    (cone G).Adj (some v) none := by simp [cone, coneAdj]

@[simp] theorem cone_adj_some_some (G : SimpleGraph V) (v w : V) :
    (cone G).Adj (some v) (some w) ↔ G.Adj v w := by rfl

instance cone_decidableRel (G : SimpleGraph V) [DecidableRel G.Adj] :
    DecidableRel (cone G).Adj := by
  intro v w
  change Decidable (coneAdj G v w)
  cases v <;> cases w <;> simp only [coneAdj] <;> infer_instance

@[simp] theorem cone_degree_some {G : SimpleGraph V} [DecidableRel G.Adj]
    (v : V) : (cone G).degree (some v) = G.degree v + 1 := by
  classical
  let someEmbedding : V ↪ Option V := ⟨some, Option.some_injective V⟩
  have neighborEq :
      (cone G).neighborFinset (some v) =
        insert none ((G.neighborFinset v).map someEmbedding) := by
    ext w
    cases w <;> simp [someEmbedding]
  calc
    (cone G).degree (some v) = #((cone G).neighborFinset (some v)) := rfl
    _ = #(insert none ((G.neighborFinset v).map someEmbedding)) :=
      congrArg Finset.card neighborEq
    _ = G.degree v + 1 := by simp [someEmbedding]

def toConeHom (G : SimpleGraph V) : G →g cone G where
  toFun := some
  map_rel' := by simp

@[simp] theorem toConeHom_apply (G : SimpleGraph V) (v : V) :
    toConeHom G v = some v := rfl

theorem cone_sup_edge (G : SimpleGraph V) (u v : V) :
    cone (G ⊔ SimpleGraph.edge u v) =
      cone G ⊔ SimpleGraph.edge (some u) (some v) := by
  ext x y
  cases x <;> cases y <;>
    simp [cone, coneAdj, SimpleGraph.sup_adj, SimpleGraph.edge_adj]

def nonNoneEquiv : {x : Option V // x ≠ none} ≃ V where
  toFun
    | ⟨none, h⟩ => (h rfl).elim
    | ⟨some v, _⟩ => v
  invFun v := ⟨some v, by simp⟩
  left_inv
    | ⟨none, h⟩ => (h rfl).elim
    | ⟨some _, _⟩ => rfl
  right_inv _ := rfl

def coneInduceNonNoneIso (G : SimpleGraph V) :
    (cone G).induce {x | x ≠ none} ≃g G where
  toEquiv := nonNoneEquiv
  map_rel_iff' := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩
    simp only [Set.mem_setOf_eq] at hx hy
    cases x with
    | none => exact (hx rfl).elim
    | some x =>
      cases y with
      | none => exact (hy rfl).elim
      | some y => rfl

theorem Traceable.mono {G H : SimpleGraph V} (hGH : G ≤ H)
    (hG : Traceable G) : Traceable H := by
  rcases hG with ⟨a, b, p, hp⟩
  exact ⟨a, b, p.map (.ofLE hGH), hp.map _ bijective_id⟩

theorem card_filter_adj_equiv {G : SimpleGraph V} [DecidableRel G.Adj]
    [Fintype ι] [DecidableEq ι] (e : ι ≃ V) (v : V) :
    #(Finset.univ.filter fun i => G.Adj v (e i)) = G.degree v := by
  let s := Finset.univ.filter fun i => G.Adj v (e i)
  have hmap : s.map e.toEmbedding = G.neighborFinset v := by
    ext w
    simp [s, SimpleGraph.mem_neighborFinset]
  calc
    #s = #(s.map e.toEmbedding) := by simp
    _ = #(G.neighborFinset v) := congrArg Finset.card hmap
    _ = G.degree v := G.card_neighborFinset_eq_degree v

theorem exists_mem_inter_of_large_cards [Fintype ι] [DecidableEq ι]
    (s t : Finset ι) (exception : ι)
    (hs : s ⊆ Finset.univ.erase exception)
    (ht : t ⊆ Finset.univ.erase exception)
    (hlarge : Fintype.card ι ≤ #s + #t) :
    ∃ i, i ∈ s ∧ i ∈ t := by
  by_contra noIntersection
  push_neg at noIntersection
  have disjoint : Disjoint s t := Finset.disjoint_left.mpr fun i hiS hiT =>
    noIntersection i hiS hiT
  have unionSubset : s ∪ t ⊆ Finset.univ.erase exception :=
    Finset.union_subset hs ht
  have unionCard : #(s ∪ t) = #s + #t :=
    Finset.card_union_of_disjoint disjoint
  have upper := Finset.card_le_card unionSubset
  have exceptionMem : exception ∈ (Finset.univ : Finset ι) := Finset.mem_univ _
  have cardPositive : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr ⟨exception⟩
  rw [Finset.card_erase_of_mem exceptionMem, Finset.card_univ, unionCard] at upper
  omega

/-- The pigeonhole step in the Bondy--Chvátal proof.  Number the vertices
along a Hamiltonian `v`--`u` path.  If `deg u + deg v` is at least the graph
order and `u v` is absent, some index `i` has both the chord from `u` to
position `i` and the chord from `v` to the cyclic successor of `i`. -/
theorem exists_rotated_adj_pair {G : SimpleGraph V} [DecidableRel G.Adj]
    {u v : V} (p : G.Walk v u) (hp : p.IsHamiltonian)
    (degreeSum : Fintype.card V ≤ G.degree u + G.degree v) :
    ∃ i : Fin (p.length + 1),
      G.Adj u (p.getVert i) ∧
      G.Adj v (p.getVert (finRotate (p.length + 1) i)) := by
  let lengthEquiv : Fin (p.length + 1) ≃ Fin p.support.length :=
    finCongr (Walk.length_support p).symm
  let order : Fin (p.length + 1) ≃ V := lengthEquiv.trans hp.getVertEquiv
  let rotate : Equiv.Perm (Fin (p.length + 1)) := finRotate (p.length + 1)
  let last : Fin (p.length + 1) := Fin.last p.length
  let fromU := Finset.univ.filter fun i => G.Adj u (order i)
  let fromV := Finset.univ.filter fun i => G.Adj v (order (rotate i))
  have cardFromU : #fromU = G.degree u := by
    simpa [fromU, order] using card_filter_adj_equiv order u
  have cardFromV : #fromV = G.degree v := by
    simpa [fromV, order, rotate] using
      card_filter_adj_equiv (G := G) (rotate.trans order) v
  have orderLast : order last = u := by
    simp [order, lengthEquiv, last, Walk.IsHamiltonian.getVertEquiv]
  have rotateLast : rotate last = 0 := by
    simp [rotate, last, finRotate_last]
  have orderZero : order 0 = v := by
    simp [order, lengthEquiv, Walk.IsHamiltonian.getVertEquiv]
  have fromUException : last ∉ fromU := by
    simp [fromU, orderLast, G.loopless]
  have fromVException : last ∉ fromV := by
    simp [fromV, rotateLast, orderZero, G.loopless]
  have fromUSubset : fromU ⊆ Finset.univ.erase last := by
    intro i hi
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    exact fun equality => fromUException (equality ▸ hi)
  have fromVSubset : fromV ⊆ Finset.univ.erase last := by
    intro i hi
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    exact fun equality => fromVException (equality ▸ hi)
  have large : Fintype.card (Fin (p.length + 1)) ≤ #fromU + #fromV := by
    rw [Fintype.card_fin, cardFromU, cardFromV, hp.length_eq]
    have cardPositive : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨v⟩
    omega
  obtain ⟨i, hiU, hiV⟩ :=
    exists_mem_inter_of_large_cards fromU fromV last fromUSubset fromVSubset large
  refine ⟨i, ?_, ?_⟩
  · simpa [order, lengthEquiv] using (Finset.mem_filter.mp hiU).2
  · simpa [order, lengthEquiv, rotate] using (Finset.mem_filter.mp hiV).2

theorem exists_adj_pair_along_hamiltonian_path
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {u v : V} (p : G.Walk v u) (hp : p.IsHamiltonian)
    (degreeSum : Fintype.card V ≤ G.degree u + G.degree v) :
    ∃ k < p.length,
      G.Adj u (p.getVert k) ∧ G.Adj v (p.getVert (k + 1)) := by
  obtain ⟨i, adjacentU, adjacentV⟩ :=
    exists_rotated_adj_pair p hp degreeSum
  have notLast : i ≠ Fin.last p.length := by
    intro equalsLast
    subst i
    simpa using adjacentU
  refine ⟨i, Fin.val_lt_last notLast, adjacentU, ?_⟩
  rw [coe_finRotate_of_ne_last notLast] at adjacentV
  exact adjacentV

/-- A closed walk of length at least three is a cycle as soon as deleting its
first vertex leaves a path. -/
theorem isCycle_of_tail_isPath {G : SimpleGraph V} {v : V}
    (q : G.Walk v v) (tailPath : q.tail.IsPath) (lengthAtLeast : 3 ≤ q.length) :
    q.IsCycle := by
  have notNil : ¬ q.Nil := by
    rw [Walk.not_nil_iff_lt_length]
    omega
  rw [← q.cons_tail_eq notNil]
  rw [Walk.cons_isCycle_iff]
  refine ⟨tailPath, ?_⟩
  intro repeatedFirstEdge
  have startEqPenultimate : q.snd = q.tail.penultimate := by
    apply tailPath.eq_penultimate_of_mem_edges
    simpa [Sym2.eq_swap] using repeatedFirstEdge
  have tailLength : 2 ≤ q.tail.length := by
    rw [← Walk.length_tail_add_one notNil] at lengthAtLeast
    omega
  have equalIndices : 0 = q.tail.length - 1 := by
    apply tailPath.getVert_injOn (by simp) (by simp)
    simpa using startEqPenultimate
  omega

/-- The constructive heart of the Bondy--Chvátal argument: a Hamiltonian
`v`--`u` path can be closed without using the missing edge `uv` whenever the
endpoint degrees sum to at least the graph order. -/
theorem exists_hamiltonianCycle_of_hamiltonianPath_degreeSum
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {u v : V} (p : G.Walk v u) (hp : p.IsHamiltonian)
    (notAdjacent : ¬ G.Adj u v)
    (degreeSum : Fintype.card V ≤ G.degree u + G.degree v) :
    ∃ q : G.Walk u u, q.IsHamiltonianCycle := by
  obtain ⟨k, hk, adjacentU, adjacentV⟩ :=
    exists_adj_pair_along_hamiltonian_path p hp degreeSum
  have splitBound : k + 1 ≤ p.length := by omega
  let q : G.Walk u u :=
    (((adjacentU.toWalk.append (p.take k).reverse).concat adjacentV).append
      (p.drop (k + 1)))
  have qLength : q.length = p.length + 1 := by
    simp [q, Nat.min_eq_left hk.le]
    omega
  have qNotNil : ¬ q.Nil := by
    rw [Walk.not_nil_iff_lt_length, qLength]
    omega
  have tailSupport :
      q.tail.support =
        (p.support.take (k + 1)).reverse ++ p.support.drop (k + 1) := by
    rw [Walk.support_tail_of_not_nil q qNotNil]
    simp [q, Walk.support_append, Walk.take_support_eq_support_take_succ,
      Walk.drop_support_eq_support_drop_min, Nat.min_eq_left splitBound]
    rw [p.getVert_eq_support_getElem splitBound]
    exact List.cons_getElem_drop_succ
  have tailSupportPerm : q.tail.support.Perm p.support := by
    rw [tailSupport]
    simpa only [List.take_append_drop] using
      (p.support.take (k + 1)).reverse_perm.append_right
        (p.support.drop (k + 1))
  have tailHamiltonian : q.tail.IsHamiltonian := by
    intro w
    rw [tailSupportPerm.count_eq]
    exact hp w
  have pathLength : 2 ≤ p.length := by
    by_contra tooShort
    have kZero : k = 0 := by omega
    apply notAdjacent
    simpa [kZero] using adjacentU
  refine ⟨q, isCycle_of_tail_isPath q tailHamiltonian.isPath ?_, tailHamiltonian⟩
  rw [qLength]
  omega

/-- A cycle that visits every vertex is Hamiltonian.  This form is convenient
when a cycle has been rotated or transferred between graphs. -/
theorem isHamiltonianCycle_of_isCycle_of_forall_mem_support
    {G : SimpleGraph V} {u : V} (q : G.Walk u u) (hq : q.IsCycle)
    (allVertices : ∀ w, w ∈ q.support) : q.IsHamiltonianCycle := by
  have tailPath : q.tail.IsPath := by
    rw [Walk.isPath_def, Walk.support_tail_of_not_nil q hq.not_nil]
    exact hq.2
  refine ⟨hq, tailPath.isHamiltonian_of_mem ?_⟩
  intro w
  by_cases hwu : w = u
  · subst w
    rw [Walk.support_tail_of_not_nil q hq.not_nil]
    exact q.end_mem_tail_support hq.not_nil
  · have hw := allVertices w
    rw [← q.cons_support_tail hq.not_nil] at hw
    simpa [hwu] using hw

/-- Closing a Hamiltonian path through the new universal vertex produces a
Hamiltonian cycle in the cone. -/
theorem cone_isHamiltonian_of_traceable [Nontrivial V]
    {G : SimpleGraph V} (hG : Traceable G) : (cone G).IsHamiltonian := by
  intro _
  obtain ⟨a, b, p, hp⟩ := hG
  have aNeB : a ≠ b := by
    intro hab
    subst b
    have pNil : p = .nil := (Walk.isPath_iff_eq_nil p).mp hp.isPath
    obtain ⟨w, hwa⟩ := exists_ne a
    apply hwa
    simpa [pNil] using hp.mem_support w
  let mapped := p.map (toConeHom G)
  have mappedPath : mapped.IsPath := by
    exact Walk.map_isPath_of_injective (Option.some_injective V) hp.isPath
  have noneNotMem : none ∉ mapped.support := by
    simp [mapped]
  let tail := mapped.concat (cone_adj_some_none G b)
  have tailPath : tail.IsPath :=
    mappedPath.concat noneNotMem (cone_adj_some_none G b)
  let q : (cone G).Walk none none :=
    Walk.cons (cone_adj_none_some G a) tail
  have qCycle : q.IsCycle := by
    dsimp [q]
    rw [Walk.cons_isCycle_iff]
    refine ⟨tailPath, ?_⟩
    simp [tail, mapped, Sym2.eq_iff, aNeB]
    intro e _
    induction e using Sym2.ind with
    | h x y => simp [Sym2.map_pair_eq, Sym2.eq_iff]
  have tailHamiltonian : tail.IsHamiltonian := by
    apply tailPath.isHamiltonian_of_mem
    intro w
    cases w with
    | none => simp [tail, mapped]
    | some w => simp [tail, mapped, hp.mem_support w]
  refine ⟨none, q, qCycle, ?_⟩
  intro w
  simpa [q] using tailHamiltonian w

/-- Deleting the universal vertex from a Hamiltonian cycle in the cone leaves
a Hamiltonian path in the original graph. -/
theorem traceable_of_cone_isHamiltonian [Nontrivial V]
    {G : SimpleGraph V} (hCone : (cone G).IsHamiltonian) : Traceable G := by
  have optionCardNeOne : Fintype.card (Option V) ≠ 1 := by
    rw [Fintype.card_option]
    have := Fintype.one_lt_card (α := V)
    omega
  obtain ⟨a, c, hc⟩ := hCone optionCardNeOne
  have noneMem : none ∈ c.support := hc.mem_support none
  let r := c.rotate noneMem
  have rCycle : r.IsCycle := by
    simpa [r] using hc.isCycle.rotate noneMem
  have rAllVertices : ∀ w, w ∈ r.support := by
    intro w
    simpa [r] using (c.mem_support_rotate_iff noneMem).mpr (hc.mem_support w)
  have rHamiltonian : r.IsHamiltonianCycle :=
    isHamiltonianCycle_of_isCycle_of_forall_mem_support r rCycle rAllVertices
  have tailLength : 2 ≤ r.tail.length := by
    have lengthEq := r.length_tail_add_one rCycle.not_nil
    have := rCycle.three_le_length
    omega
  let pOpt := r.tail.dropLast
  have pOptPath : pOpt.IsPath := by
    apply Walk.IsPath.of_append_left (q := r.tail.drop (r.tail.length - 1))
    simpa [pOpt, Walk.dropLast] using rHamiltonian.isHamiltonian_tail.isPath
  have pOptSupport : pOpt.support = r.tail.support.dropLast := by
    dsimp [pOpt]
    rw [Walk.dropLast, Walk.take_support_eq_support_take_succ,
      List.dropLast_eq_take, Walk.length_support]
    congr 1
    omega
  have noneNotMemDropLast : none ∉ r.tail.support.dropLast := by
    have decomposition : r.tail.support.dropLast ++ [none] = r.tail.support := by
      simpa using List.dropLast_append_getLast r.tail.support_ne_nil
    have nodup := rHamiltonian.isHamiltonian_tail.isPath.support_nodup
    rw [← decomposition] at nodup
    have disjoint := List.disjoint_of_nodup_append nodup
    simpa using disjoint
  have pOptNonNone : ∀ x ∈ pOpt.support, x ∈ {x : Option V | x ≠ none} := by
    intro x hx
    show x ≠ none
    intro hxNone
    subst x
    exact noneNotMemDropLast (pOptSupport ▸ hx)
  have someMemPOpt (v : V) : some v ∈ pOpt.support := by
    rw [pOptSupport]
    apply List.mem_dropLast_of_mem_of_ne_getLast
    · simp
    · exact rHamiltonian.isHamiltonian_tail.mem_support (some v)
  let pInduced := pOpt.induce {x : Option V | x ≠ none} pOptNonNone
  have pInducedPath : pInduced.IsPath := by
    rw [Walk.isPath_def]
    dsimp [pInduced]
    rw [Walk.support_induce, ← List.nodup_map_iff Subtype.val_injective,
      List.attachWith_map_subtype_val]
    exact pOptPath.support_nodup
  have pInducedHamiltonian : pInduced.IsHamiltonian := by
    apply pInducedPath.isHamiltonian_of_mem
    rintro ⟨x, hx⟩
    cases x with
    | none => exact (hx rfl).elim
    | some v =>
      dsimp [pInduced]
      rw [Walk.support_induce, List.mem_attachWith]
      exact someMemPOpt v
  let pG := pInduced.map (coneInduceNonNoneIso G).toHom
  refine ⟨_, _, pG, ?_⟩
  exact pInducedHamiltonian.map _ (coneInduceNonNoneIso G).bijective

/-- If a walk in `G` with one extra edge does not use that edge, all of its
edges already belong to `G`. -/
theorem edges_subset_left_of_not_mem_extra_edge
    {G : SimpleGraph V} {u v a b : V}
    (p : (G ⊔ SimpleGraph.edge u v).Walk a b)
    (hnot : s(u, v) ∉ p.edges) :
    ∀ e, e ∈ p.edges → e ∈ G.edgeSet := by
  intro e he
  have heSup := p.edges_subset_edgeSet he
  rw [SimpleGraph.edgeSet_sup] at heSup
  rcases heSup with heG | heExtra
  · exact heG
  · have edgeEq : e = s(u, v) := by
      have edgeInfo : e = s(u, v) ∧ ¬ e.IsDiag := by
        simpa [SimpleGraph.edge] using heExtra
      exact edgeInfo.1
    exact (hnot (edgeEq ▸ he)).elim

/-- The hard direction of the Bondy--Chvátal single-edge closure theorem. -/
theorem isHamiltonian_of_sup_edge_isHamiltonian
    {G : SimpleGraph V} [DecidableRel G.Adj] {u v : V}
    (notAdjacent : ¬ G.Adj u v)
    (degreeSum : Fintype.card V ≤ G.degree u + G.degree v)
    (hSup : (G ⊔ SimpleGraph.edge u v).IsHamiltonian) :
    G.IsHamiltonian := by
  by_cases huv : u = v
  · subst v
    simpa using hSup
  intro cardNeOne
  obtain ⟨a, c, hc⟩ := hSup cardNeOne
  by_cases usesExtra : s(u, v) ∈ c.edges
  · have huSupport : u ∈ c.support :=
      c.fst_mem_support_of_mem_edges usesExtra
    let r := c.rotate huSupport
    have rCycle : r.IsCycle := by
      simpa [r] using hc.isCycle.rotate huSupport
    have usesExtraR : s(u, v) ∈ r.edges := by
      simpa [r] using (c.rotate_edges huSupport).mem_iff.mpr usesExtra
    have rAdjacent : r.toSubgraph.Adj u v := by
      rw [← Subgraph.mem_edgeSet, r.mem_edges_toSubgraph]
      exact usesExtraR
    obtain ⟨d, dCycle, dSnd, dVerts⟩ :=
      rCycle.exists_isCycle_snd_verts_eq rAdjacent
    have dAllVertices : ∀ w, w ∈ d.support := by
      intro w
      rw [← d.mem_verts_toSubgraph, dVerts, r.mem_verts_toSubgraph]
      simpa [r] using hc.mem_support w
    have dHamiltonian : d.IsHamiltonianCycle :=
      isHamiltonianCycle_of_isCycle_of_forall_mem_support d dCycle dAllVertices
    have dNotNil : ¬ d.Nil := dCycle.not_nil
    have firstAdjacent : (G ⊔ SimpleGraph.edge u v).Adj u d.snd :=
      d.adj_snd dNotNil
    have noFirstEdgeInTail : s(u, d.snd) ∉ d.tail.edges := by
      have consCycle : (Walk.cons firstAdjacent d.tail).IsCycle := by
        rw [d.cons_tail_eq dNotNil]
        exact dCycle
      exact (Walk.cons_isCycle_iff d.tail firstAdjacent).mp consCycle |>.2
    have noExtraInTail : s(u, v) ∉ d.tail.edges := by
      simpa [dSnd] using noFirstEdgeInTail
    have tailEdgesG :=
      edges_subset_left_of_not_mem_extra_edge d.tail noExtraInTail
    let pG0 := d.tail.transfer G tailEdgesG
    let pG : G.Walk v u := pG0.copy dSnd rfl
    have pGHamiltonian : pG.IsHamiltonian := by
      intro w
      simpa [pG, pG0] using dHamiltonian.isHamiltonian_tail w
    obtain ⟨q, hq⟩ :=
      exists_hamiltonianCycle_of_hamiltonianPath_degreeSum
        pG pGHamiltonian notAdjacent degreeSum
    exact ⟨u, q, hq⟩
  · have edgesG :=
      edges_subset_left_of_not_mem_extra_edge c usesExtra
    let cG := c.transfer G edgesG
    have cGCycle : cG.IsCycle := by
      simpa [cG] using hc.isCycle.transfer edgesG
    refine ⟨a, cG,
      isHamiltonianCycle_of_isCycle_of_forall_mem_support cG cGCycle ?_⟩
    intro w
    simpa [cG] using hc.mem_support w

/-- Adding a nonedge whose endpoint degrees sum to at least the graph order
preserves Hamiltonicity. -/
theorem isHamiltonian_sup_edge_iff
    {G : SimpleGraph V} [DecidableRel G.Adj] {u v : V}
    (notAdjacent : ¬ G.Adj u v)
    (degreeSum : Fintype.card V ≤ G.degree u + G.degree v) :
    (G ⊔ SimpleGraph.edge u v).IsHamiltonian ↔ G.IsHamiltonian := by
  constructor
  · exact isHamiltonian_of_sup_edge_isHamiltonian notAdjacent degreeSum
  · exact fun hG => hG.mono le_sup_left

theorem traceable_iff_cone_isHamiltonian [Nontrivial V]
    {G : SimpleGraph V} : Traceable G ↔ (cone G).IsHamiltonian :=
  ⟨cone_isHamiltonian_of_traceable, traceable_of_cone_isHamiltonian⟩

/-- The Hamiltonian-path version of Bondy--Chvátal closure.  Its threshold is
`|V| - 1`, exactly the rule used by the finite WOWII 217 certificates. -/
theorem traceable_sup_edge_iff [Nontrivial V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {u v : V}
    (notAdjacent : ¬ G.Adj u v)
    (degreeSum : Fintype.card V - 1 ≤ G.degree u + G.degree v) :
    Traceable (G ⊔ SimpleGraph.edge u v) ↔ Traceable G := by
  have coneNotAdjacent : ¬ (cone G).Adj (some u) (some v) := by
    simpa using notAdjacent
  have coneDegreeSum :
      Fintype.card (Option V) ≤
        (cone G).degree (some u) + (cone G).degree (some v) := by
    rw [Fintype.card_option, cone_degree_some, cone_degree_some]
    have := Fintype.one_lt_card (α := V)
    omega
  rw [traceable_iff_cone_isHamiltonian,
    traceable_iff_cone_isHamiltonian, cone_sup_edge]
  exact isHamiltonian_sup_edge_iff coneNotAdjacent coneDegreeSum

end WOWII217BondyChvatal
