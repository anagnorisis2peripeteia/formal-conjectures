import WOWII217BondyChvatal
import WOWII217Closure
import WOWII217Finite13ClosureSharedDeg

/-!
Semantic bridge from the upper-triangle bit-vector graphs and their
Bondy--Chvatal path-closure rounds to `SimpleGraph` traceability.
-/

namespace WOWII217ClosureSemantics

open Finset SimpleGraph
open WOWII217BondyChvatal WOWII217Closure WOWII217FiniteBase
open WOWII217Finite13ClosureSharedDeg

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

def graphOfUpper {n : Nat} (g : BitVec (edgeCount n)) : SimpleGraph (Fin n) where
  Adj u v := adjUpper g u v = true
  symm := by
    intro u v h
    rw [← adjUpper_comm]
    exact h
  loopless := by
    intro u
    simp [adjUpper]

instance graphOfUpper_decidableRel {n : Nat} (g : BitVec (edgeCount n)) :
    DecidableRel (graphOfUpper g).Adj := by
  intro u v
  change Decidable (adjUpper g u v = true)
  infer_instance

instance graphOfUpper13_decidableRel (g : BitVec 78) :
    DecidableRel (graphOfUpper (n := 13) g).Adj := by
  intro u v
  change Decidable (adjUpper (n := 13) g u v = true)
  infer_instance

theorem foldl_bool_count (p : Nat → Bool) :
    ∀ (xs : List Nat), xs.Nodup → ∀ initial,
      xs.foldl (fun count x => count + if p x then 1 else 0) initial =
        initial + #(xs.toFinset.filter fun x => p x = true) := by
  intro xs nodup
  induction xs with
  | nil => simp
  | cons x xs ih =>
      rw [List.nodup_cons] at nodup
      intro initial
      simp only [List.foldl_cons]
      rw [ih nodup.2]
      rw [List.toFinset_cons]
      by_cases hx : p x = true
      · rw [Finset.filter_insert]
        simp [hx, nodup.1, Nat.add_assoc, Nat.add_comm]
      · have hxFalse : p x = false := Bool.eq_false_of_not_eq_true hx
        rw [Finset.filter_insert]
        simp [hxFalse]

def boolFourValue (x : BoolFour) : Nat :=
  (if x.b0 then 1 else 0) +
  2 * (if x.b1 then 1 else 0) +
  4 * (if x.b2 then 1 else 0) +
  8 * (if x.b3 then 1 else 0)

theorem boolFourValue_increment_of_lt_fifteen (x : BoolFour) (b : Bool)
    (hx : boolFourValue x < 15) :
    boolFourValue (x.increment b) =
      boolFourValue x + if b then 1 else 0 := by
  rcases x with ⟨b0, b1, b2, b3⟩
  fin_cases b0 <;> fin_cases b1 <;> fin_cases b2 <;> fin_cases b3 <;>
    fin_cases b <;> simp [boolFourValue, BoolFour.increment] at hx ⊢

theorem boolFourValue_foldl_increment {α : Type*} (f : α → Bool) :
    ∀ (xs : List α) (initial : BoolFour),
      boolFourValue initial + xs.length < 16 →
      boolFourValue (xs.foldl (fun bits x => bits.increment (f x)) initial) =
        xs.foldl (fun count x => count + if f x then 1 else 0)
          (boolFourValue initial) := by
  intro xs
  induction xs with
  | nil => simp
  | cons x xs ih =>
      intro initial bound
      simp only [List.foldl_cons]
      simp only [List.length_cons] at bound
      have initialLt : boolFourValue initial < 15 := by
        omega
      have incrementValue :=
        boolFourValue_increment_of_lt_fifteen initial (f x) initialLt
      have bitBound : (if f x then 1 else 0) ≤ 1 := by split <;> simp
      have nextBound :
          boolFourValue (initial.increment (f x)) + xs.length < 16 := by
        rw [incrementValue]
        omega
      rw [ih _ nextBound, incrementValue]

theorem boolFourValue_degreeBitsUpper_eq {n : Nat} (hn : n < 16)
    (g : BitVec (edgeCount n)) (u : Nat) :
    boolFourValue (degreeBitsUpper g u) = degreeUpperNat g u := by
  unfold degreeBitsUpper degreeUpperNat
  have folded := boolFourValue_foldl_increment
    (fun v => adjUpper g u v) (List.range n)
      { b0 := false, b1 := false, b2 := false, b3 := false }
  simpa [boolFourValue] using folded (by simpa [boolFourValue] using hn)

theorem boolFourSumAtLeast12_iff (x y : BoolFour) :
    boolFourSumAtLeast12 x y = true ↔
      12 ≤ boolFourValue x + boolFourValue y := by
  rcases x with ⟨x0, x1, x2, x3⟩
  rcases y with ⟨y0, y1, y2, y3⟩
  fin_cases x0 <;> fin_cases x1 <;> fin_cases x2 <;> fin_cases x3 <;>
    fin_cases y0 <;> fin_cases y1 <;> fin_cases y2 <;> fin_cases y3 <;>
    decide

def degreeTableOfUpper13 (g : BitVec 78) : BitVec 52 :=
  BitVec.ofFnLE fun i =>
    let degree := degreeBitsUpper (n := 13) g (i.val / 4)
    match i.val % 4 with
    | 0 => degree.b0
    | 1 => degree.b1
    | 2 => degree.b2
    | _ => degree.b3

theorem degreeTableAt13_ofUpper (g : BitVec 78) (v : Nat) (hv : v < 13) :
    degreeTableAt13 (degreeTableOfUpper13 g) v =
      degreeBitsUpper (n := 13) g v := by
  rcases hdegree : degreeBitsUpper (n := 13) g v with ⟨b0, b1, b2, b3⟩
  have h1 : (4 * v + 1) / 4 = v := by omega
  have h2 : (4 * v + 2) / 4 = v := by omega
  have h3 : (4 * v + 3) / 4 = v := by omega
  simp [degreeTableAt13, degreeTableOfUpper13, BitVec.getLsbD_ofFnLE,
    hdegree, h1, h2, h3, show 4 * v < 52 by omega,
    show 4 * v + 1 < 52 by omega,
    show 4 * v + 2 < 52 by omega, show 4 * v + 3 < 52 by omega]

theorem degreeTableOfUpper13_consistent (g : BitVec 78) :
    degreeTableConsistent13 g (degreeTableOfUpper13 g) = true := by
  norm_num [degreeTableConsistent13, degreeTableAt13_ofUpper, BoolFour.same]
  intro v hv
  rw [degreeTableAt13_ofUpper g v hv]
  simp [BoolFour.same]

theorem boolFourSame_eq_true_iff (x y : BoolFour) :
    x.same y = true ↔ x = y := by
  rcases x with ⟨x0, x1, x2, x3⟩
  rcases y with ⟨y0, y1, y2, y3⟩
  fin_cases x0 <;> fin_cases x1 <;> fin_cases x2 <;> fin_cases x3 <;>
    fin_cases y0 <;> fin_cases y1 <;> fin_cases y2 <;> fin_cases y3 <;>
    simp [BoolFour.same]

theorem degreeTableAt13_eq_of_consistent (g : BitVec 78) (degrees : BitVec 52)
    (consistent : degreeTableConsistent13 g degrees = true)
    (v : Nat) (hv : v < 13) :
    degreeTableAt13 degrees v = degreeBitsUpper (n := 13) g v := by
  have allConsistent :
      ∀ w ∈ List.range 13,
        (degreeBitsUpper (n := 13) g w).same
          (degreeTableAt13 degrees w) = true := by
    simpa only [degreeTableConsistent13, List.all_eq_true] using consistent
  have atV := allConsistent v (List.mem_range.mpr hv)
  exact (boolFourSame_eq_true_iff _ _).mp atV |>.symm

theorem mem_upperPairs_iff {n u v : Nat} :
    (u, v) ∈ upperPairs n ↔ v < n ∧ u < v := by
  simp [upperPairs]

theorem boolNotXor_eq_true_iff (a b : Bool) :
    Bool.not (a ^^ b) = true ↔ a = b := by
  cases a <;> cases b <;> decide

theorem adjUpper_eq_of_pathClosureParallelRel13
    (g next : BitVec 78) (degrees : BitVec 52)
    (consistent : degreeTableConsistent13 g degrees = true)
    (related : pathClosureParallelRel13 g next degrees = true)
    {u v : Nat} (huv : u < v) (hv : v < 13) :
    adjUpper (n := 13) next u v =
      (adjUpper (n := 13) g u v ||
        decide (12 ≤ degreeUpperNat (n := 13) g u +
          degreeUpperNat (n := 13) g v)) := by
  rw [pathClosureParallelRel13] at related
  have atPair := (List.all_eq_true.mp related) (u, v)
    (mem_upperPairs_iff.mpr ⟨hv, huv⟩)
  have relation := (boolNotXor_eq_true_iff _ _).mp atPair
  have hu : u < 13 := Nat.lt_trans huv hv
  have degreeU := degreeTableAt13_eq_of_consistent g degrees consistent u hu
  have degreeV := degreeTableAt13_eq_of_consistent g degrees consistent v hv
  have threshold :
      boolFourSumAtLeast12 (degreeTableAt13 degrees u)
          (degreeTableAt13 degrees v) =
        decide (12 ≤ degreeUpperNat (n := 13) g u +
          degreeUpperNat (n := 13) g v) := by
    apply Bool.eq_iff_iff.mpr
    simpa [degreeU, degreeV,
      boolFourValue_degreeBitsUpper_eq (n := 13) (by decide)] using
      (boolFourSumAtLeast12_iff (degreeTableAt13 degrees u)
        (degreeTableAt13 degrees v))
  simpa [threshold] using relation

theorem degree_graphOfUpper_eq {n : Nat} (g : BitVec (edgeCount n))
    (u : Fin n) : (graphOfUpper g).degree u = degreeUpperNat g u := by
  let valEmbedding : Fin n ↪ Nat := ⟨Fin.val, Fin.val_injective⟩
  have neighborMap :
      ((graphOfUpper g).neighborFinset u).map valEmbedding =
        (Finset.range n).filter fun v => adjUpper g u v = true := by
    ext v
    simp [valEmbedding, graphOfUpper]
    constructor
    · rintro ⟨a, adjacent, rfl⟩
      exact ⟨a.isLt, adjacent⟩
    · rintro ⟨hv, adjacent⟩
      exact ⟨⟨v, hv⟩, adjacent, rfl⟩
  have countRange := foldl_bool_count (fun v => adjUpper g u v)
    (List.range n) (List.nodup_range : (List.range n).Nodup) 0
  rw [Nat.zero_add] at countRange
  have rangeToFinset : (List.range n).toFinset = Finset.range n := by
    ext v
    simp
  rw [rangeToFinset] at countRange
  have countRange' :
      (List.range n).foldl
          (fun count v => count + if adjUpper g u v then 1 else 0) 0 =
        #((Finset.range n).filter fun v => adjUpper g u v = true) := by
    simpa using countRange
  calc
    (graphOfUpper g).degree u = #((graphOfUpper g).neighborFinset u) := rfl
    _ = #(((graphOfUpper g).neighborFinset u).map valEmbedding) := by simp
    _ = #((Finset.range n).filter fun v => adjUpper g u v = true) :=
      congrArg Finset.card neighborMap
    _ = degreeUpperNat g u := by
      rw [← countRange']
      rfl

section SemanticClosure

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Starting from `current`, add every listed pair whose degree sum in the
fixed graph `base` meets the Hamiltonian-path closure threshold.  The fixed
degree test matches one parallel round of the Boolean certificate. -/
def addEligibleEdgesFrom (base : SimpleGraph V) [DecidableRel base.Adj] :
    List (V × V) → SimpleGraph V → SimpleGraph V
  | [], current => current
  | (u, v) :: edges, current =>
      addEligibleEdgesFrom base edges
        (if Fintype.card V - 1 ≤ base.degree u + base.degree v then
          current ⊔ SimpleGraph.edge u v
        else current)

theorem adj_addEligibleEdgesFrom_iff (base current : SimpleGraph V)
    [DecidableRel base.Adj] (edges : List (V × V)) (x y : V) :
    (addEligibleEdgesFrom base edges current).Adj x y ↔
      current.Adj x y ∨
        ∃ edge ∈ edges,
          Fintype.card V - 1 ≤
              base.degree edge.1 + base.degree edge.2 ∧
            (SimpleGraph.edge edge.1 edge.2).Adj x y := by
  induction edges generalizing current with
  | nil => simp [addEligibleEdgesFrom]
  | cons edge edges ih =>
      rcases edge with ⟨u, v⟩
      by_cases hdegree :
          Fintype.card V - 1 ≤ base.degree u + base.degree v
      · simp only [addEligibleEdgesFrom, if_pos hdegree, ih,
          SimpleGraph.sup_adj]
        constructor
        · rintro ((adjacent | added) | ⟨edge, member, degreeSum, edgeAdj⟩)
          · exact Or.inl adjacent
          · exact Or.inr ⟨(u, v), by simp, hdegree, added⟩
          · exact Or.inr ⟨edge, by simp [member], degreeSum, edgeAdj⟩
        · rintro (adjacent | ⟨edge, member, degreeSum, edgeAdj⟩)
          · exact Or.inl (Or.inl adjacent)
          · rcases List.mem_cons.mp member with rfl | member
            · exact Or.inl (Or.inr edgeAdj)
            · exact Or.inr ⟨edge, member, degreeSum, edgeAdj⟩
      · simp only [addEligibleEdgesFrom, if_neg hdegree, ih]
        constructor
        · rintro (adjacent | ⟨edge, member, degreeSum, edgeAdj⟩)
          · exact Or.inl adjacent
          · exact Or.inr ⟨edge, by simp [member], degreeSum, edgeAdj⟩
        · rintro (adjacent | ⟨edge, member, degreeSum, edgeAdj⟩)
          · exact Or.inl adjacent
          · rcases List.mem_cons.mp member with rfl | member
            · exact (hdegree degreeSum).elim
            · exact Or.inr ⟨edge, member, degreeSum, edgeAdj⟩

def allPairs13 : List (Fin 13 × Fin 13) :=
  (List.finRange 13).flatMap fun u =>
    (List.finRange 13).map fun v => (u, v)

@[simp] theorem pair_mem_allPairs13 (u v : Fin 13) :
    (u, v) ∈ allPairs13 := by
  simp [allPairs13]

theorem adj_addEligibleEdges13_iff (base : SimpleGraph (Fin 13))
    [DecidableRel base.Adj] (x y : Fin 13) :
    (addEligibleEdgesFrom base allPairs13 base).Adj x y ↔
      base.Adj x y ∨
        (x ≠ y ∧ 12 ≤ base.degree x + base.degree y) := by
  rw [adj_addEligibleEdgesFrom_iff]
  simp only [Fintype.card_fin]
  constructor
  · rintro (adjacent | ⟨⟨u, v⟩, _, degreeSum, added⟩)
    · exact Or.inl adjacent
    · rw [SimpleGraph.edge_adj] at added
      rcases added with ⟨⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, hne⟩
      · exact Or.inr ⟨hne, degreeSum⟩
      · exact Or.inr ⟨hne, by simpa [Nat.add_comm] using degreeSum⟩
  · rintro (adjacent | ⟨hne, degreeSum⟩)
    · exact Or.inl adjacent
    · exact Or.inr ⟨(x, y), pair_mem_allPairs13 x y, degreeSum,
        (SimpleGraph.edge_adj (s := x) (t := y) x y).mpr
          ⟨Or.inl ⟨rfl, rfl⟩, hne⟩⟩

theorem graphOfUpper_eq_addEligibleEdges13_of_rel
    (g next : BitVec 78) (degrees : BitVec 52)
    (consistent : degreeTableConsistent13 g degrees = true)
    (related : pathClosureParallelRel13 g next degrees = true) :
    graphOfUpper (n := 13) next =
      addEligibleEdgesFrom (graphOfUpper (n := 13) g) allPairs13
        (graphOfUpper (n := 13) g) := by
  ext x y
  rw [adj_addEligibleEdges13_iff]
  have hDegreeX := degree_graphOfUpper_eq (n := 13) g x
  have hDegreeY := degree_graphOfUpper_eq (n := 13) g y
  by_cases hxy : x = y
  · subst y
    simp [graphOfUpper]
  · have hvalne : x.val ≠ y.val := fun h => hxy (Fin.ext h)
    have relationXY :
        adjUpper (n := 13) next x y =
          (adjUpper (n := 13) g x y ||
            decide (12 ≤ degreeUpperNat (n := 13) g x +
              degreeUpperNat (n := 13) g y)) := by
      by_cases hlt : x.val < y.val
      · exact adjUpper_eq_of_pathClosureParallelRel13 g next degrees
          consistent related hlt y.isLt
      · have hyx : y.val < x.val := by omega
        have reverse := adjUpper_eq_of_pathClosureParallelRel13 g next degrees
          consistent related hyx x.isLt
        rw [adjUpper_comm (n := 13) next x y, reverse,
          adjUpper_comm (n := 13) g x y,
          Nat.add_comm]
    change adjUpper (n := 13) next x y = true ↔
      adjUpper (n := 13) g x y = true ∨
        (x ≠ y ∧ 12 ≤ (graphOfUpper (n := 13) g).degree x +
          (graphOfUpper (n := 13) g).degree y)
    rw [relationXY]
    simp [hxy, hDegreeX, hDegreeY]

theorem base_le_addEligibleEdgesFrom (base current : SimpleGraph V)
    [DecidableRel base.Adj]
    (edges : List (V × V)) (hbase : base ≤ current) :
    base ≤ addEligibleEdgesFrom base edges current := by
  induction edges generalizing current with
  | nil => simpa [addEligibleEdgesFrom] using hbase
  | cons edge edges ih =>
      rcases edge with ⟨u, v⟩
      simp only [addEligibleEdgesFrom]
      split
      · exact ih _ (hbase.trans le_sup_left)
      · exact ih _ hbase

/-- A parallel round is sound when sequentialized: because degrees only
increase while its eligible edges are inserted, each insertion remains a
legal Bondy--Chvátal path-closure step. -/
theorem traceable_addEligibleEdgesFrom_iff [Nontrivial V]
    (base current : SimpleGraph V) [DecidableRel base.Adj]
    (edges : List (V × V))
    (hbase : base ≤ current) :
    Traceable (addEligibleEdgesFrom base edges current) ↔ Traceable current := by
  classical
  induction edges generalizing current with
  | nil => simp [addEligibleEdgesFrom]
  | cons edge edges ih =>
      rcases edge with ⟨u, v⟩
      simp only [addEligibleEdgesFrom]
      by_cases hdegree :
          Fintype.card V - 1 ≤ base.degree u + base.degree v
      · rw [if_pos hdegree, ih _ (hbase.trans le_sup_left)]
        by_cases hadj : current.Adj u v
        · rw [current.sup_edge_of_adj hadj]
        · have hu : base.degree u ≤ current.degree u :=
            base.degree_le_of_le hbase
          have hv : base.degree v ≤ current.degree v :=
            base.degree_le_of_le hbase
          have currentDegree :
              Fintype.card V - 1 ≤ current.degree u + current.degree v := by
            omega
          exact WOWII217BondyChvatal.traceable_sup_edge_iff hadj currentDegree
      · rw [if_neg hdegree, ih _ hbase]

theorem traceable_graphOfUpper_rel13_iff
    (g next : BitVec 78) (degrees : BitVec 52)
    (consistent : degreeTableConsistent13 g degrees = true)
    (related : pathClosureParallelRel13 g next degrees = true) :
    Traceable (graphOfUpper (n := 13) next) ↔
      Traceable (graphOfUpper (n := 13) g) := by
  rw [graphOfUpper_eq_addEligibleEdges13_of_rel g next degrees
    consistent related]
  exact traceable_addEligibleEdgesFrom_iff
    (graphOfUpper (n := 13) g) (graphOfUpper (n := 13) g)
      allPairs13 le_rfl

end SemanticClosure

def completeWalk13 :
    (⊤ : SimpleGraph (Fin 13)).Walk (0 : Fin 13) (12 : Fin 13) :=
  .cons (show (⊤ : SimpleGraph (Fin 13)).Adj 0 1 by simp) <|
  .cons (show (⊤ : SimpleGraph (Fin 13)).Adj 1 2 by simp) <|
  .cons (show (⊤ : SimpleGraph (Fin 13)).Adj 2 3 by simp) <|
  .cons (show (⊤ : SimpleGraph (Fin 13)).Adj 3 4 by simp) <|
  .cons (show (⊤ : SimpleGraph (Fin 13)).Adj 4 5 by simp) <|
  .cons (show (⊤ : SimpleGraph (Fin 13)).Adj 5 6 by simp) <|
  .cons (show (⊤ : SimpleGraph (Fin 13)).Adj 6 7 by simp) <|
  .cons (show (⊤ : SimpleGraph (Fin 13)).Adj 7 8 by simp) <|
  .cons (show (⊤ : SimpleGraph (Fin 13)).Adj 8 9 by simp) <|
  .cons (show (⊤ : SimpleGraph (Fin 13)).Adj 9 10 by simp) <|
  .cons (show (⊤ : SimpleGraph (Fin 13)).Adj 10 11 by simp) <|
  .cons (show (⊤ : SimpleGraph (Fin 13)).Adj 11 12 by simp) <| .nil

theorem completeWalk13_isHamiltonian : completeWalk13.IsHamiltonian := by
  intro v
  fin_cases v <;> simp [completeWalk13]

theorem traceable_top13 : Traceable (⊤ : SimpleGraph (Fin 13)) :=
  ⟨0, 12, completeWalk13, completeWalk13_isHamiltonian⟩

theorem adjUpper_true_of_completeUpper13 (g : BitVec 78)
    (complete : completeUpper (n := 13) g = true)
    {u v : Nat} (huv : u < v) (hv : v < 13) :
    adjUpper (n := 13) g u v = true := by
  rw [completeUpper] at complete
  exact (List.all_eq_true.mp complete) (u, v)
    (mem_upperPairs_iff.mpr ⟨hv, huv⟩)

theorem graphOfUpper_eq_top_of_completeUpper13 (g : BitVec 78)
    (complete : completeUpper (n := 13) g = true) :
    graphOfUpper (n := 13) g = ⊤ := by
  ext x y
  change adjUpper (n := 13) g x y = true ↔
    (⊤ : SimpleGraph (Fin 13)).Adj x y
  rw [SimpleGraph.top_adj]
  constructor
  · intro adjacent hxy
    subst y
    simp [adjUpper] at adjacent
  · intro hxy
    have hvalne : x.val ≠ y.val := fun h => hxy (Fin.ext h)
    by_cases hlt : x.val < y.val
    · exact adjUpper_true_of_completeUpper13 g complete hlt y.isLt
    · have hyx : y.val < x.val := by omega
      rw [adjUpper_comm (n := 13) g x y]
      exact adjUpper_true_of_completeUpper13 g complete hyx x.isLt

theorem traceable_graphOfUpper_of_completeUpper13 (g : BitVec 78)
    (complete : completeUpper (n := 13) g = true) :
    Traceable (graphOfUpper (n := 13) g) := by
  rw [graphOfUpper_eq_top_of_completeUpper13 g complete]
  exact traceable_top13

end WOWII217ClosureSemantics
