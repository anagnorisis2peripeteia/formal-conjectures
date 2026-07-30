import FormalConjecturesUtil

/-!
Semantic soundness and completeness of the 14-vertex Held--Karp bit-vector
encoding used by the WOWII Graph Conjecture 217 finite certificate.
-/

namespace WOWII217Semantics

open SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] {G : SimpleGraph α}

/-- Reachability of an endpoint by a duplicate-free path with exactly the
vertices in `support`. This is the propositional meaning of a Held--Karp DP
state bit. -/
inductive EndpointReachable (G : SimpleGraph α) : Finset α → α → Prop
  | singleton (v : α) : EndpointReachable G {v} v
  | extend {support : Finset α} {u v : α} (fresh : v ∉ support)
      (previous : EndpointReachable G support u) (adj : G.Adj u v) :
      EndpointReachable G (insert v support) v

theorem EndpointReachable.exists_vertex_order {support : Finset α} {v : α}
    (h : EndpointReachable G support v) :
    ∃ tail : List α,
      (v :: tail).IsChain G.Adj ∧
      (v :: tail).Nodup ∧
      (v :: tail).toFinset = support := by
  induction h with
  | singleton v => exact ⟨[], by simp, by simp, by simp⟩
  | @extend support u v fresh previous adj ih =>
      obtain ⟨tail, chain, nodup, vertices⟩ := ih
      refine ⟨u :: tail, ?_, ?_, ?_⟩
      · simpa only [List.isChain_cons_cons] using And.intro adj.symm chain
      · rw [List.nodup_cons]
        refine ⟨?_, nodup⟩
        intro hv
        apply fresh
        rw [← vertices]
        simpa using hv
      · simp [vertices]

/-- A nonempty list whose consecutive vertices are adjacent is the support of
a graph walk. -/
theorem exists_walk_support_eq_of_isChain (l : List α) (hl : l ≠ [])
    (hchain : l.IsChain G.Adj) :
    ∃ a b : α, ∃ p : G.Walk a b, p.support = l := by
  induction l with
  | nil => exact (hl rfl).elim
  | cons a l ih =>
      cases l with
      | nil => exact ⟨a, a, .nil, rfl⟩
      | cons b t =>
          rw [List.isChain_cons_cons] at hchain
          obtain ⟨c, d, p, hp⟩ := ih (by simp) hchain.2
          have hbc : b = c := by
            simpa [hp] using p.head_support
          subst c
          exact ⟨a, d, .cons hchain.1 p, by simp [hp]⟩

theorem exists_hamiltonian_walk_of_vertex_order (l : List α) (hl : l ≠ [])
    (hchain : l.IsChain G.Adj) (hnodup : l.Nodup) (hcover : ∀ v : α, v ∈ l) :
    ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian := by
  obtain ⟨a, b, p, hp⟩ := exists_walk_support_eq_of_isChain l hl hchain
  refine ⟨a, b, p, ?_⟩
  apply Walk.IsPath.isHamiltonian_of_mem (Walk.IsPath.mk' ?_) ?_
  · simpa [hp] using hnodup
  · simpa [hp] using hcover

/-- A full-set Held--Karp state has the exact graph-theoretic meaning required
by Conjecture 217: an actual Hamiltonian walk. -/
theorem EndpointReachable.exists_hamiltonian_walk {v : α}
    (h : EndpointReachable G Finset.univ v) :
    ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian := by
  obtain ⟨tail, chain, nodup, vertices⟩ := h.exists_vertex_order
  apply exists_hamiltonian_walk_of_vertex_order (v :: tail) (by simp) chain nodup
  intro x
  have : x ∈ (v :: tail).toFinset := by simp [vertices]
  simpa using this

/-- The mathematical recurrence implemented by the Held--Karp bitvectors. -/
def EndpointRecurrence (G : SimpleGraph α)
    (table : Finset α → α → Prop) : Prop :=
  ∀ support v,
    table support v ↔
      support = {v} ∨
      (v ∈ support ∧ ∃ u, table (support.erase v) u ∧ G.Adj u v)

theorem EndpointReachable.recurrence :
    EndpointRecurrence G (EndpointReachable G) := by
  intro support v
  constructor
  · intro h
    cases h with
    | singleton v => exact Or.inl rfl
    | @extend previousSupport u v fresh previous adj =>
        refine Or.inr ⟨by simp, u, ?_, adj⟩
        simpa [Finset.erase_insert fresh] using previous
  · rintro (rfl | ⟨hv, u, previous, adj⟩)
    · exact .singleton v
    · rw [← Finset.insert_erase hv]
      exact .extend (Finset.notMem_erase v support) previous adj

/-- Any table satisfying the exact recurrence is sound: every marked state
has a duplicate-free path witnessing it. -/
theorem EndpointRecurrence.sound {table : Finset α → α → Prop}
    (recurrence : EndpointRecurrence G table) {support : Finset α} {v : α}
    (marked : table support v) : EndpointReachable G support v := by
  induction support using Finset.strongInductionOn generalizing v with
  | _ support ih =>
      rcases (recurrence support v).mp marked with singleton | extend
      · simpa [singleton] using EndpointReachable.singleton (G := G) v
      · obtain ⟨hv, u, previous, adj⟩ := extend
        have smaller : support.erase v ⊂ support :=
          Finset.ssubset_iff_subset_ne.mpr
            ⟨Finset.erase_subset _ _, by
              intro equality
              have : v ∈ support.erase v := by rw [equality]; exact hv
              exact Finset.notMem_erase v support this⟩
        have previousReachable := ih (support.erase v) smaller previous
        rw [← Finset.insert_erase hv]
        exact EndpointReachable.extend (Finset.notMem_erase v support)
          previousReachable adj

def maskHas (mask v : Nat) : Bool :=
  decide (mask / 2 ^ v % 2 = 1)

def verticesOfMask14 (mask : Nat) : Finset (Fin 14) :=
  Finset.univ.filter fun v => maskHas mask v = true

def maskOfVertices14 (support : Finset (Fin 14)) : Nat :=
  support.sum fun v => 2 ^ (v : Nat)

theorem maskOfVertices14_lt :
    ∀ support : Finset (Fin 14), maskOfVertices14 support < 16384 := by
  native_decide

def maskOfVertices14Fin (support : Finset (Fin 14)) : Fin 16384 :=
  ⟨maskOfVertices14 support, maskOfVertices14_lt support⟩

theorem verticesOfMask14_maskOfVertices14 :
    ∀ support : Finset (Fin 14),
      verticesOfMask14 (maskOfVertices14 support) = support := by
  native_decide

theorem maskOfVertices14_verticesOfMask14 :
    ∀ mask : Fin 16384,
      maskOfVertices14 (verticesOfMask14 mask) = mask := by
  native_decide

theorem maskHas_maskOfVertices14 :
    ∀ (support : Finset (Fin 14)) (v : Fin 14),
      maskHas (maskOfVertices14 support) v = decide (v ∈ support) := by
  native_decide

theorem maskHas_eq_true_iff_mem (mask : Fin 16384) (v : Fin 14) :
    maskHas mask v = true ↔ v ∈ verticesOfMask14 mask := by
  simp [verticesOfMask14]

theorem maskOfVertices14_singleton :
    ∀ v : Fin 14, maskOfVertices14 {v} = 2 ^ (v : Nat) := by
  native_decide

theorem maskOfVertices14_univ :
    maskOfVertices14 (Finset.univ : Finset (Fin 14)) = 16383 := by
  native_decide

theorem maskOfVertices14_eq_twoPow_iff :
    ∀ (support : Finset (Fin 14)) (v : Fin 14),
      maskOfVertices14 support = 2 ^ (v : Nat) ↔ support = {v} := by
  native_decide

theorem maskOfVertices14_erase :
    ∀ (support : Finset (Fin 14)) (v : Fin 14),
      v ∈ support →
      maskOfVertices14 (support.erase v) =
        maskOfVertices14 support - 2 ^ (v : Nat) := by
  native_decide

theorem verticesOfMask14_full :
    verticesOfMask14 16383 = Finset.univ := by
  native_decide

theorem verticesOfMask14_singleton :
    ∀ v : Fin 14, verticesOfMask14 (2 ^ (v : Nat)) = {v} := by
  native_decide

theorem verticesOfMask14_erase_present :
    ∀ (mask : Fin 16384) (v : Fin 14),
      maskHas mask v = true →
      verticesOfMask14 (mask - 2 ^ (v : Nat)) = (verticesOfMask14 mask).erase v := by
  native_decide

theorem verticesOfMask14_fresh_after_subtract :
    ∀ (mask : Fin 16384) (v : Fin 14),
      maskHas mask v = true → v ∉ verticesOfMask14 (mask - 2 ^ (v : Nat)) := by
  native_decide

theorem getLsbD_foldl_or {w : Nat} {β : Type*} (xs : List β)
    (f : β → BitVec w) (initial : BitVec w) (i : Nat) :
    (xs.foldl (fun states x => states ||| f x) initial).getLsbD i =
      (initial.getLsbD i || xs.any fun x => (f x).getLsbD i) := by
  induction xs generalizing initial with
  | nil => simp
  | cons x xs ih =>
      simp only [List.foldl_cons, ih, BitVec.getLsbD_or, List.any_cons]
      simp only [Bool.or_assoc]

def bitMask {w : Nat} (b : Bool) : BitVec w :=
  BitVec.cast (by simp) (BitVec.replicate w (BitVec.ofBool b))

def absentMask : (n v : Nat) → BitVec (2 ^ n)
  | 0, _ => 1#1
  | n + 1, v =>
      if v = n then
        BitVec.cast (by simp [pow_succ, Nat.mul_two])
          (BitVec.append (BitVec.zero (2 ^ n)) (BitVec.allOnes (2 ^ n)))
      else
        BitVec.cast (by simp [pow_succ, Nat.mul_two])
          (BitVec.append (absentMask n v) (absentMask n v))

theorem absentMask14_getLsbD :
    ∀ (mask : Fin 16384) (v : Fin 14),
      (absentMask 14 v).getLsbD mask = !maskHas mask v := by
  native_decide

theorem shifted_fresh_control14 :
    ∀ (mask : Fin 16384) (v : Fin 14) (b : Bool),
      (!decide ((mask : Nat) < 2 ^ (v : Nat)) &&
          (b && (absentMask 14 v).getLsbD ((mask : Nat) - 2 ^ (v : Nat)))) =
        (maskHas mask v && b) := by
  native_decide

theorem shifted_fresh_block_getLsbD (block : BitVec 16384)
    (mask : Fin 16384) (v : Fin 14) :
    (((block &&& absentMask 14 v) <<< (2 ^ (v : Nat))).getLsbD mask) =
      (maskHas mask v && block.getLsbD (mask - 2 ^ (v : Nat))) := by
  simp only [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_and]
  have width : (mask : Nat) < 16384 := mask.isLt
  simp only [width, decide_true, Bool.true_and]
  exact shifted_fresh_control14 mask v
    (block.getLsbD ((mask : Nat) - 2 ^ (v : Nat)))

def edgeCount (n : Nat) : Nat := n * (n - 1) / 2

def adjUpper {n : Nat} (g : BitVec (edgeCount n)) (u v : Nat) : Bool :=
  if u < v then g.getLsbD (v * (v - 1) / 2 + u)
  else if v < u then g.getLsbD (u * (u - 1) / 2 + v)
  else false

theorem adjUpper_comm {n : Nat} (g : BitVec (edgeCount n)) (u v : Nat) :
    adjUpper g u v = adjUpper g v u := by
  by_cases huv : u < v
  · have hvu : ¬ v < u := Nat.not_lt_of_ge (Nat.le_of_lt huv)
    simp [adjUpper, huv, hvu]
  · by_cases hvu : v < u
    · simp [adjUpper, huv, hvu]
    · have huvEq : u = v :=
        Nat.le_antisymm (Nat.le_of_not_gt hvu) (Nat.le_of_not_gt huv)
      subst v
      simp [adjUpper]

def graphOfUpper14 (g : BitVec 91) : SimpleGraph (Fin 14) where
  Adj u v := adjUpper (n := 14) g u v = true
  symm u v h := by
    change adjUpper (n := 14) g (u : Nat) (v : Nat) = true at h
    change adjUpper (n := 14) g (v : Nat) (u : Nat) = true
    rw [adjUpper_comm]
    exact h
  loopless v := by simp [adjUpper]

noncomputable def endpointBlock14 (g : BitVec 91) (v : Fin 14) : BitVec 16384 := by
  classical
  let f := fun mask : Fin 16384 =>
    decide (EndpointReachable (graphOfUpper14 g) (verticesOfMask14 mask) v)
  exact BitVec.cast List.length_ofFn (BitVec.ofBoolListLE (List.ofFn f))

theorem endpointBlock14_getLsbD_eq_true_iff (g : BitVec 91) (v : Fin 14)
    (mask : Fin 16384) :
    (endpointBlock14 g v).getLsbD mask = true ↔
      EndpointReachable (graphOfUpper14 g) (verticesOfMask14 mask) v := by
  classical
  unfold endpointBlock14
  simp only [BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE]
  let f := fun index : Fin 16384 =>
    decide (EndpointReachable (graphOfUpper14 g) (verticesOfMask14 index) v)
  change (List.ofFn f).getD (mask : Nat) false = true ↔
    EndpointReachable (graphOfUpper14 g) (verticesOfMask14 mask) v
  have hmask : (mask : Nat) < (List.ofFn f).length := by
    rw [List.length_ofFn]
    exact mask.isLt
  rw [List.getD_eq_getElem (l := List.ofFn f) (d := false) hmask]
  rw [List.getElem_ofFn]
  change decide (EndpointReachable (graphOfUpper14 g)
    (verticesOfMask14 mask) v) = true ↔ _
  exact decide_eq_true_iff

def dpAt14
    (d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 : BitVec 16384) :
    Nat → BitVec 16384
  | 0 => d0
  | 1 => d1
  | 2 => d2
  | 3 => d3
  | 4 => d4
  | 5 => d5
  | 6 => d6
  | 7 => d7
  | 8 => d8
  | 9 => d9
  | 10 => d10
  | 11 => d11
  | 12 => d12
  | _ => d13

def dpNextBlock14 (g : BitVec 91)
    (d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 : BitVec 16384) :
    Nat → BitVec 16384 := fun v =>
  let extended := (List.range 14).foldl (fun states u =>
    states ||| (bitMask (w := 16384) (adjUpper (n := 14) g u v) &&&
      ((dpAt14 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 u &&&
        absentMask 14 v) <<< (2 ^ v)))) 0#16384
  BitVec.twoPow 16384 (2 ^ v) ||| extended

def hamiltonianDPConsistent14Split (g : BitVec 91)
    (d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 : BitVec 16384) : Bool :=
  (List.range 14).all fun v =>
    dpAt14 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 v ==
      dpNextBlock14 g d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 v

def hamiltonianDPHasFullPath14Split
    (d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 : BitVec 16384) : Bool :=
  d0.getLsbD 16383 || d1.getLsbD 16383 || d2.getLsbD 16383 ||
  d3.getLsbD 16383 || d4.getLsbD 16383 || d5.getLsbD 16383 ||
  d6.getLsbD 16383 || d7.getLsbD 16383 || d8.getLsbD 16383 ||
  d9.getLsbD 16383 || d10.getLsbD 16383 || d11.getLsbD 16383 ||
  d12.getLsbD 16383 || d13.getLsbD 16383

def dpTable14
    (d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 : BitVec 16384)
    (support : Finset (Fin 14)) (v : Fin 14) : Prop :=
  (dpAt14 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 v).getLsbD
      (maskOfVertices14 support) = true

theorem bitMask16384_getLsbD :
    ∀ (b : Bool) (i : Fin 16384),
      (bitMask (w := 16384) b).getLsbD i = b := by
  intro b i
  simp only [bitMask, BitVec.getLsbD_cast, BitVec.getLsbD_replicate,
    Nat.one_mul, i.isLt, decide_true, Bool.true_and, Nat.mod_one,
    BitVec.getLsbD_ofBool, Bool.and_self]

theorem twoPowIndex14_lt :
    ∀ v : Fin 14, 2 ^ (v : Nat) < 16384 := by
  native_decide

theorem twoPow16384_getLsbD :
    ∀ (mask : Fin 16384) (v : Fin 14),
      (BitVec.twoPow 16384 (2 ^ (v : Nat))).getLsbD mask =
        decide ((mask : Nat) = 2 ^ (v : Nat)) := by
  intro mask v
  simp [BitVec.getLsbD_twoPow, twoPowIndex14_lt v, eq_comm]

theorem extensionBlock_getLsbD (g : BitVec 91) (block : BitVec 16384)
    (mask : Fin 16384) (u : Nat) (v : Fin 14) :
    (bitMask (w := 16384) (adjUpper (n := 14) g u v) &&&
        ((block &&& absentMask 14 v) <<< (2 ^ (v : Nat)))).getLsbD mask =
      (adjUpper (n := 14) g u v && maskHas mask v &&
        block.getLsbD (mask - 2 ^ (v : Nat))) := by
  rw [BitVec.getLsbD_and, bitMask16384_getLsbD,
    shifted_fresh_block_getLsbD]
  simp only [Bool.and_assoc]

theorem dpNextBlock14_getLsbD (g : BitVec 91)
    (d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 : BitVec 16384)
    (mask : Fin 16384) (v : Fin 14) :
    (dpNextBlock14 g d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 v).getLsbD
        mask =
      (decide ((mask : Nat) = 2 ^ (v : Nat)) ||
        (List.range 14).any fun u =>
          adjUpper (n := 14) g u v && maskHas mask v &&
            (dpAt14 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 u).getLsbD
              ((mask : Nat) - 2 ^ (v : Nat))) := by
  simp only [dpNextBlock14, BitVec.getLsbD_or, twoPow16384_getLsbD,
    getLsbD_foldl_or, BitVec.getLsbD_zero, Bool.false_or,
    extensionBlock_getLsbD]

theorem dpLookupOfConsistent14Split (g : BitVec 91)
    (d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 : BitVec 16384)
    (consistent : hamiltonianDPConsistent14Split g
      d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 = true)
    (mask : Fin 16384) (v : Fin 14) :
    (dpAt14 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 v).getLsbD mask =
      (decide ((mask : Nat) = 2 ^ (v : Nat)) ||
        (List.range 14).any fun u =>
          adjUpper (n := 14) g u v && maskHas mask v &&
            (dpAt14 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 u).getLsbD
              ((mask : Nat) - 2 ^ (v : Nat))) := by
  have blockEqualityBool :=
    (List.all_eq_true.mp consistent) (v : Nat) (List.mem_range.mpr v.isLt)
  have blockEquality := beq_iff_eq.mp blockEqualityBool
  have lookupEquality := congrArg
    (fun block : BitVec 16384 => block.getLsbD mask) blockEquality
  change (dpAt14 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 v).getLsbD
    mask =
    (dpNextBlock14 g d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 v).getLsbD
      mask at lookupEquality
  rw [dpNextBlock14_getLsbD] at lookupEquality
  exact lookupEquality

theorem dpTable14_recurrence (g : BitVec 91)
    (d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 : BitVec 16384)
    (consistent : hamiltonianDPConsistent14Split g
      d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 = true) :
    EndpointRecurrence (graphOfUpper14 g)
      (dpTable14 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13) := by
  intro support v
  have lookup := dpLookupOfConsistent14Split g
    d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 consistent
    (maskOfVertices14Fin support) v
  simp only [maskOfVertices14Fin] at lookup
  constructor
  · intro marked
    change (dpAt14 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 v).getLsbD
      (maskOfVertices14 support) = true at marked
    rw [lookup] at marked
    rcases Bool.or_eq_true_iff.mp marked with singleton | extended
    · left
      apply (maskOfVertices14_eq_twoPow_iff support v).mp
      exact of_decide_eq_true singleton
    · obtain ⟨u, huRange, hu⟩ := List.any_eq_true.mp extended
      simp only [Bool.and_eq_true] at hu
      rcases hu with ⟨⟨adjacent, present⟩, previous⟩
      have hv : v ∈ support := by
        rw [maskHas_maskOfVertices14] at present
        exact of_decide_eq_true present
      let uFin : Fin 14 := ⟨u, List.mem_range.mp huRange⟩
      refine Or.inr ⟨hv, uFin, ?_, ?_⟩
      · change (dpAt14 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13
          u).getLsbD (maskOfVertices14 (support.erase v)) = true
        rw [maskOfVertices14_erase support v hv]
        exact previous
      · exact adjacent
  · intro recurrence
    change (dpAt14 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 v).getLsbD
      (maskOfVertices14 support) = true
    rw [lookup]
    apply Bool.or_eq_true_iff.mpr
    rcases recurrence with singleton | ⟨present, u, previous, adjacent⟩
    · left
      apply decide_eq_true
      exact (maskOfVertices14_eq_twoPow_iff support v).mpr singleton
    · right
      apply List.any_eq_true.mpr
      refine ⟨(u : Nat), List.mem_range.mpr u.isLt, ?_⟩
      simp only [Bool.and_eq_true]
      refine ⟨⟨adjacent, ?_⟩, ?_⟩
      · rw [maskHas_maskOfVertices14]
        exact decide_eq_true present
      · change (dpAt14 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13
          u).getLsbD (maskOfVertices14 (support.erase v)) = true at previous
        rw [maskOfVertices14_erase support v present] at previous
        exact previous

theorem dpConsistent14Split_of_recurrence (g : BitVec 91)
    (d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 : BitVec 16384)
    (recurrence : EndpointRecurrence (graphOfUpper14 g)
      (dpTable14 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13)) :
    hamiltonianDPConsistent14Split g
      d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 = true := by
  apply List.all_eq_true.mpr
  intro v hvRange
  have hvlt : v < 14 := List.mem_range.mp hvRange
  let vFin : Fin 14 := ⟨v, hvlt⟩
  apply beq_iff_eq.mpr
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro mask hmask
  let maskFin : Fin 16384 := ⟨mask, hmask⟩
  change
    (dpAt14 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 vFin).getLsbD
        maskFin =
      (dpNextBlock14 g d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13
        vFin).getLsbD maskFin
  rw [dpNextBlock14_getLsbD]
  apply Bool.eq_iff_iff.mpr
  change
    ((dpAt14 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 v).getLsbD
        mask = true) ↔
      ((decide (mask = 2 ^ v) ||
        (List.range 14).any fun u =>
          adjUpper (n := 14) g u v && maskHas mask v &&
            (dpAt14 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 u).getLsbD
              (mask - 2 ^ v)) = true)
  let support := verticesOfMask14 maskFin
  have supportMask : maskOfVertices14 support = mask := by
    exact maskOfVertices14_verticesOfMask14 maskFin
  constructor
  · intro marked
    have tableMarked : dpTable14 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13
        support vFin := by
      change (dpAt14 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 v).getLsbD
        (maskOfVertices14 support) = true
      rw [supportMask]
      exact marked
    rcases (recurrence support vFin).mp tableMarked with singleton | extended
    · apply Bool.or_eq_true_iff.mpr
      left
      apply decide_eq_true
      calc
        mask = maskOfVertices14 support := supportMask.symm
        _ = maskOfVertices14 {vFin} := congrArg maskOfVertices14 singleton
        _ = 2 ^ v := maskOfVertices14_singleton vFin
    · obtain ⟨present, u, previous, adjacent⟩ := extended
      apply Bool.or_eq_true_iff.mpr
      right
      apply List.any_eq_true.mpr
      refine ⟨(u : Nat), List.mem_range.mpr u.isLt, ?_⟩
      simp only [Bool.and_eq_true]
      refine ⟨⟨adjacent, ?_⟩, ?_⟩
      · exact (maskHas_eq_true_iff_mem maskFin vFin).mpr present
      · change (dpAt14 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13
          u).getLsbD (maskOfVertices14 (support.erase vFin)) = true at previous
        rw [maskOfVertices14_erase support vFin present, supportMask] at previous
        exact previous
  · intro encoded
    rcases Bool.or_eq_true_iff.mp encoded with singleton | extended
    · have maskEq : mask = 2 ^ v := of_decide_eq_true singleton
      have supportEq : support = {vFin} := by
        dsimp only [support]
        change verticesOfMask14 mask = {vFin}
        rw [maskEq]
        exact verticesOfMask14_singleton vFin
      have tableMarked := (recurrence support vFin).mpr (Or.inl supportEq)
      change (dpAt14 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 v).getLsbD
        (maskOfVertices14 support) = true at tableMarked
      rw [supportMask] at tableMarked
      exact tableMarked
    · obtain ⟨u, huRange, hu⟩ := List.any_eq_true.mp extended
      simp only [Bool.and_eq_true] at hu
      rcases hu with ⟨⟨adjacent, present⟩, previous⟩
      let uFin : Fin 14 := ⟨u, List.mem_range.mp huRange⟩
      have hvPresent : vFin ∈ support :=
        (maskHas_eq_true_iff_mem maskFin vFin).mp present
      have tablePrevious : dpTable14 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13
          (support.erase vFin) uFin := by
        change (dpAt14 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13
          u).getLsbD (maskOfVertices14 (support.erase vFin)) = true
        rw [maskOfVertices14_erase support vFin hvPresent, supportMask]
        exact previous
      have tableMarked := (recurrence support vFin).mpr
        (Or.inr ⟨hvPresent, uFin, tablePrevious, adjacent⟩)
      change (dpAt14 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 v).getLsbD
        (maskOfVertices14 support) = true at tableMarked
      rw [supportMask] at tableMarked
      exact tableMarked

theorem dpAt14_endpointBlocks (g : BitVec 91) (u : Nat) (hu : u < 14) :
    dpAt14 (endpointBlock14 g 0) (endpointBlock14 g 1) (endpointBlock14 g 2)
      (endpointBlock14 g 3) (endpointBlock14 g 4) (endpointBlock14 g 5)
      (endpointBlock14 g 6) (endpointBlock14 g 7) (endpointBlock14 g 8)
      (endpointBlock14 g 9) (endpointBlock14 g 10) (endpointBlock14 g 11)
      (endpointBlock14 g 12) (endpointBlock14 g 13) u =
        endpointBlock14 g ⟨u, hu⟩ := by
  interval_cases u <;> rfl

theorem endpointBlocks_dpTable_iff (g : BitVec 91)
    (support : Finset (Fin 14)) (v : Fin 14) :
    dpTable14 (endpointBlock14 g 0) (endpointBlock14 g 1) (endpointBlock14 g 2)
      (endpointBlock14 g 3) (endpointBlock14 g 4) (endpointBlock14 g 5)
      (endpointBlock14 g 6) (endpointBlock14 g 7) (endpointBlock14 g 8)
      (endpointBlock14 g 9) (endpointBlock14 g 10) (endpointBlock14 g 11)
      (endpointBlock14 g 12) (endpointBlock14 g 13) support v ↔
        EndpointReachable (graphOfUpper14 g) support v := by
  change
    (dpAt14 (endpointBlock14 g 0) (endpointBlock14 g 1) (endpointBlock14 g 2)
      (endpointBlock14 g 3) (endpointBlock14 g 4) (endpointBlock14 g 5)
      (endpointBlock14 g 6) (endpointBlock14 g 7) (endpointBlock14 g 8)
      (endpointBlock14 g 9) (endpointBlock14 g 10) (endpointBlock14 g 11)
      (endpointBlock14 g 12) (endpointBlock14 g 13) v).getLsbD
        (maskOfVertices14 support) = true ↔ _
  rw [dpAt14_endpointBlocks g v v.isLt]
  have lookup := endpointBlock14_getLsbD_eq_true_iff g v
    (maskOfVertices14Fin support)
  simp only [maskOfVertices14Fin, verticesOfMask14_maskOfVertices14] at lookup
  exact lookup

theorem endpointBlocks_recurrence (g : BitVec 91) :
    EndpointRecurrence (graphOfUpper14 g)
      (dpTable14 (endpointBlock14 g 0) (endpointBlock14 g 1) (endpointBlock14 g 2)
        (endpointBlock14 g 3) (endpointBlock14 g 4) (endpointBlock14 g 5)
        (endpointBlock14 g 6) (endpointBlock14 g 7) (endpointBlock14 g 8)
        (endpointBlock14 g 9) (endpointBlock14 g 10) (endpointBlock14 g 11)
        (endpointBlock14 g 12) (endpointBlock14 g 13)) := by
  intro support v
  simpa only [endpointBlocks_dpTable_iff] using
    (EndpointReachable.recurrence (G := graphOfUpper14 g) support v)

theorem endpointBlocks_consistent (g : BitVec 91) :
    hamiltonianDPConsistent14Split g
      (endpointBlock14 g 0) (endpointBlock14 g 1) (endpointBlock14 g 2)
      (endpointBlock14 g 3) (endpointBlock14 g 4) (endpointBlock14 g 5)
      (endpointBlock14 g 6) (endpointBlock14 g 7) (endpointBlock14 g 8)
      (endpointBlock14 g 9) (endpointBlock14 g 10) (endpointBlock14 g 11)
      (endpointBlock14 g 12) (endpointBlock14 g 13) = true := by
  exact dpConsistent14Split_of_recurrence g
    (endpointBlock14 g 0) (endpointBlock14 g 1) (endpointBlock14 g 2)
    (endpointBlock14 g 3) (endpointBlock14 g 4) (endpointBlock14 g 5)
    (endpointBlock14 g 6) (endpointBlock14 g 7) (endpointBlock14 g 8)
    (endpointBlock14 g 9) (endpointBlock14 g 10) (endpointBlock14 g 11)
    (endpointBlock14 g 12) (endpointBlock14 g 13) (endpointBlocks_recurrence g)

theorem existsHamiltonianWalkOfMarkedFull14 (g : BitVec 91)
    (d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 : BitVec 16384)
    (consistent : hamiltonianDPConsistent14Split g
      d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 = true)
    (v : Fin 14)
    (full : (dpAt14 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 v).getLsbD
      16383 = true) :
    ∃ a b : Fin 14, ∃ p : (graphOfUpper14 g).Walk a b, p.IsHamiltonian := by
  have marked : dpTable14 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13
      Finset.univ v := by
    change (dpAt14 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 v).getLsbD
      (maskOfVertices14 Finset.univ) = true
    rw [maskOfVertices14_univ]
    exact full
  have reachable := EndpointRecurrence.sound
    (dpTable14_recurrence g d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13
      consistent) marked
  exact reachable.exists_hamiltonian_walk

theorem existsHamiltonianWalkOfDP14 (g : BitVec 91)
    (d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 : BitVec 16384)
    (consistent : hamiltonianDPConsistent14Split g
      d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 = true)
    (full : hamiltonianDPHasFullPath14Split
      d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 = true) :
    ∃ a b : Fin 14, ∃ p : (graphOfUpper14 g).Walk a b, p.IsHamiltonian := by
  simp only [hamiltonianDPHasFullPath14Split, Bool.or_eq_true] at full
  rcases full with ((((((((((((h0 | h1) | h2) | h3) | h4) | h5) | h6) | h7) |
    h8) | h9) | h10) | h11) | h12) | h13
  · exact existsHamiltonianWalkOfMarkedFull14 g
      d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 consistent 0 h0
  · exact existsHamiltonianWalkOfMarkedFull14 g
      d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 consistent 1 h1
  · exact existsHamiltonianWalkOfMarkedFull14 g
      d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 consistent 2 h2
  · exact existsHamiltonianWalkOfMarkedFull14 g
      d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 consistent 3 h3
  · exact existsHamiltonianWalkOfMarkedFull14 g
      d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 consistent 4 h4
  · exact existsHamiltonianWalkOfMarkedFull14 g
      d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 consistent 5 h5
  · exact existsHamiltonianWalkOfMarkedFull14 g
      d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 consistent 6 h6
  · exact existsHamiltonianWalkOfMarkedFull14 g
      d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 consistent 7 h7
  · exact existsHamiltonianWalkOfMarkedFull14 g
      d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 consistent 8 h8
  · exact existsHamiltonianWalkOfMarkedFull14 g
      d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 consistent 9 h9
  · exact existsHamiltonianWalkOfMarkedFull14 g
      d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 consistent 10 h10
  · exact existsHamiltonianWalkOfMarkedFull14 g
      d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 consistent 11 h11
  · exact existsHamiltonianWalkOfMarkedFull14 g
      d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 consistent 12 h12
  · exact existsHamiltonianWalkOfMarkedFull14 g
      d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 consistent 13 h13

end WOWII217Semantics
