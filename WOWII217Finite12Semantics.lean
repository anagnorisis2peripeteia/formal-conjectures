import WOWII217Semantics
import WOWII217Finite12Regular
import WOWII217ClosureSemantics

/-!
Semantic interpretation of the split Held--Karp table in the certified
connected 5-regular order-12 case.
-/

namespace WOWII217Finite12Semantics

open SimpleGraph
open WOWII217FiniteBase WOWII217Finite12Regular
open WOWII217ClosureSemantics
open WOWII217BondyChvatal

def verticesOfMask12 (mask : Nat) : Finset (Fin 12) :=
  Finset.univ.filter fun v => maskHas mask v = true

def maskOfVertices12 (support : Finset (Fin 12)) : Nat :=
  support.sum fun v => 2 ^ (v : Nat)

theorem maskOfVertices12_lt :
    ∀ support : Finset (Fin 12), maskOfVertices12 support < 4096 := by
  native_decide

def maskOfVertices12Fin (support : Finset (Fin 12)) : Fin 4096 :=
  ⟨maskOfVertices12 support, maskOfVertices12_lt support⟩

theorem verticesOfMask12_maskOfVertices12 :
    ∀ support : Finset (Fin 12),
      verticesOfMask12 (maskOfVertices12 support) = support := by
  native_decide

theorem maskOfVertices12_verticesOfMask12 :
    ∀ mask : Fin 4096,
      maskOfVertices12 (verticesOfMask12 mask) = mask := by
  native_decide

theorem maskHas_maskOfVertices12 :
    ∀ (support : Finset (Fin 12)) (v : Fin 12),
      maskHas (maskOfVertices12 support) v = decide (v ∈ support) := by
  native_decide

theorem maskOfVertices12_singleton :
    ∀ v : Fin 12, maskOfVertices12 {v} = 2 ^ (v : Nat) := by
  native_decide

theorem maskOfVertices12_univ :
    maskOfVertices12 (Finset.univ : Finset (Fin 12)) = 4095 := by
  native_decide

theorem maskOfVertices12_eq_twoPow_iff :
    ∀ (support : Finset (Fin 12)) (v : Fin 12),
      maskOfVertices12 support = 2 ^ (v : Nat) ↔ support = {v} := by
  native_decide

theorem maskOfVertices12_erase :
    ∀ (support : Finset (Fin 12)) (v : Fin 12),
      v ∈ support →
      maskOfVertices12 (support.erase v) =
        maskOfVertices12 support - 2 ^ (v : Nat) := by
  native_decide

theorem verticesOfMask12_full :
    verticesOfMask12 4095 = Finset.univ := by
  native_decide

theorem verticesOfMask12_singleton :
    ∀ v : Fin 12, verticesOfMask12 (2 ^ (v : Nat)) = {v} := by
  native_decide

theorem maskHas_eq_true_iff_mem12 (mask : Fin 4096) (v : Fin 12) :
    maskHas mask v = true ↔ v ∈ verticesOfMask12 mask := by
  simp [verticesOfMask12]

noncomputable def endpointBlock12 (g : BitVec 66) (v : Fin 12) : BitVec 4096 := by
  classical
  let f := fun mask : Fin 4096 =>
    decide (WOWII217Semantics.EndpointReachable
      (graphOfUpper (n := 12) g) (verticesOfMask12 mask) v)
  exact BitVec.cast List.length_ofFn (BitVec.ofBoolListLE (List.ofFn f))

theorem endpointBlock12_getLsbD_eq_true_iff (g : BitVec 66) (v : Fin 12)
    (mask : Fin 4096) :
    (endpointBlock12 g v).getLsbD mask = true ↔
      WOWII217Semantics.EndpointReachable
        (graphOfUpper (n := 12) g) (verticesOfMask12 mask) v := by
  classical
  unfold endpointBlock12
  simp only [BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE]
  let f := fun index : Fin 4096 =>
    decide (WOWII217Semantics.EndpointReachable
      (graphOfUpper (n := 12) g) (verticesOfMask12 index) v)
  change (List.ofFn f).getD (mask : Nat) false = true ↔
    WOWII217Semantics.EndpointReachable
      (graphOfUpper (n := 12) g) (verticesOfMask12 mask) v
  have hmask : (mask : Nat) < (List.ofFn f).length := by
    rw [List.length_ofFn]
    exact mask.isLt
  rw [List.getD_eq_getElem (l := List.ofFn f) (d := false) hmask]
  rw [List.getElem_ofFn]
  exact decide_eq_true_iff

theorem getLsbD_foldl_or12 {w : Nat} {β : Type*} (xs : List β)
    (f : β → BitVec w) (initial : BitVec w) (i : Nat) :
    (xs.foldl (fun states x => states ||| f x) initial).getLsbD i =
      (initial.getLsbD i || xs.any fun x => (f x).getLsbD i) := by
  induction xs generalizing initial with
  | nil => simp
  | cons x xs ih =>
      simp only [List.foldl_cons, ih, BitVec.getLsbD_or, List.any_cons]
      simp only [Bool.or_assoc]

theorem absentMask12_getLsbD :
    ∀ (mask : Fin 4096) (v : Fin 12),
      (absentMask 12 v).getLsbD mask = !maskHas mask v := by
  native_decide

theorem shiftedFreshControl12 :
    ∀ (mask : Fin 4096) (v : Fin 12) (b : Bool),
      (!decide ((mask : Nat) < 2 ^ (v : Nat)) &&
          (b && (absentMask 12 v).getLsbD
            ((mask : Nat) - 2 ^ (v : Nat)))) =
        (maskHas mask v && b) := by
  native_decide

theorem shiftedFreshBlock_getLsbD12 (block : BitVec 4096)
    (mask : Fin 4096) (v : Fin 12) :
    (((block &&& absentMask 12 v) <<< (2 ^ (v : Nat))).getLsbD mask) =
      (maskHas mask v && block.getLsbD (mask - 2 ^ (v : Nat))) := by
  simp only [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_and]
  have width : (mask : Nat) < 4096 := mask.isLt
  simp only [width, decide_true, Bool.true_and]
  exact shiftedFreshControl12 mask v
    (block.getLsbD ((mask : Nat) - 2 ^ (v : Nat)))

theorem bitMask4096_getLsbD :
    ∀ (b : Bool) (i : Fin 4096),
      (bitMask (w := 4096) b).getLsbD i = b := by
  intro b i
  simp only [bitMask, BitVec.getLsbD_cast, BitVec.getLsbD_replicate,
    Nat.one_mul, i.isLt, decide_true, Bool.true_and, Nat.mod_one,
    BitVec.getLsbD_ofBool, Bool.and_self]

theorem twoPowIndex12_lt :
    ∀ v : Fin 12, 2 ^ (v : Nat) < 4096 := by
  native_decide

theorem twoPow4096_getLsbD :
    ∀ (mask : Fin 4096) (v : Fin 12),
      (BitVec.twoPow 4096 (2 ^ (v : Nat))).getLsbD mask =
        decide ((mask : Nat) = 2 ^ (v : Nat)) := by
  intro mask v
  simp [BitVec.getLsbD_twoPow, twoPowIndex12_lt v, eq_comm]

def dpNextBlock12 (g : BitVec 66)
    (d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 : BitVec 4096) :
    Nat → BitVec 4096 := fun v =>
  let extended := (List.range 12).foldl (fun states u =>
    states ||| (bitMask (w := 4096) (adjUpper (n := 12) g u v) &&&
      ((dpAt12 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 u &&&
        absentMask 12 v) <<< (2 ^ v)))) 0#4096
  BitVec.twoPow 4096 (2 ^ v) ||| extended

theorem extensionBlock12_getLsbD (g : BitVec 66) (block : BitVec 4096)
    (mask : Fin 4096) (u : Nat) (v : Fin 12) :
    (bitMask (w := 4096) (adjUpper (n := 12) g u v) &&&
        ((block &&& absentMask 12 v) <<< (2 ^ (v : Nat)))).getLsbD mask =
      (adjUpper (n := 12) g u v && maskHas mask v &&
        block.getLsbD (mask - 2 ^ (v : Nat))) := by
  rw [BitVec.getLsbD_and, bitMask4096_getLsbD,
    shiftedFreshBlock_getLsbD12]
  simp only [Bool.and_assoc]

theorem dpNextBlock12_getLsbD (g : BitVec 66)
    (d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 : BitVec 4096)
    (mask : Fin 4096) (v : Fin 12) :
    (dpNextBlock12 g d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 v).getLsbD
        mask =
      (decide ((mask : Nat) = 2 ^ (v : Nat)) ||
        (List.range 12).any fun u =>
          adjUpper (n := 12) g u v && maskHas mask v &&
            (dpAt12 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 u).getLsbD
              ((mask : Nat) - 2 ^ (v : Nat))) := by
  simp only [dpNextBlock12, BitVec.getLsbD_or, twoPow4096_getLsbD,
    getLsbD_foldl_or12, BitVec.getLsbD_zero, Bool.false_or,
    extensionBlock12_getLsbD]

theorem dpLookupOfConsistent12Split (g : BitVec 66)
    (d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 : BitVec 4096)
    (consistent : hamiltonianDPConsistent12Split g
      d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 = true)
    (mask : Fin 4096) (v : Fin 12) :
    (dpAt12 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 v).getLsbD mask =
      (decide ((mask : Nat) = 2 ^ (v : Nat)) ||
        (List.range 12).any fun u =>
          adjUpper (n := 12) g u v && maskHas mask v &&
            (dpAt12 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 u).getLsbD
              ((mask : Nat) - 2 ^ (v : Nat))) := by
  have blockEqualityBool :=
    (List.all_eq_true.mp consistent) (v : Nat) (List.mem_range.mpr v.isLt)
  have blockEquality := beq_iff_eq.mp blockEqualityBool
  have lookupEquality := congrArg
    (fun block : BitVec 4096 => block.getLsbD mask) blockEquality
  change (dpAt12 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 v).getLsbD
    mask =
    (dpNextBlock12 g d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 v).getLsbD
      mask at lookupEquality
  rw [dpNextBlock12_getLsbD] at lookupEquality
  exact lookupEquality

def dpTable12
    (d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 : BitVec 4096)
    (support : Finset (Fin 12)) (v : Fin 12) : Prop :=
  (dpAt12 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 v).getLsbD
      (maskOfVertices12 support) = true

theorem dpTable12_recurrence (g : BitVec 66)
    (d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 : BitVec 4096)
    (consistent : hamiltonianDPConsistent12Split g
      d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 = true) :
    WOWII217Semantics.EndpointRecurrence (graphOfUpper (n := 12) g)
      (dpTable12 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11) := by
  intro support v
  have lookup := dpLookupOfConsistent12Split g
    d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 consistent
    (maskOfVertices12Fin support) v
  simp only [maskOfVertices12Fin] at lookup
  constructor
  · intro marked
    change (dpAt12 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 v).getLsbD
      (maskOfVertices12 support) = true at marked
    rw [lookup] at marked
    rcases Bool.or_eq_true_iff.mp marked with singleton | extended
    · left
      apply (maskOfVertices12_eq_twoPow_iff support v).mp
      exact of_decide_eq_true singleton
    · obtain ⟨u, huRange, hu⟩ := List.any_eq_true.mp extended
      simp only [Bool.and_eq_true] at hu
      rcases hu with ⟨⟨adjacent, present⟩, previous⟩
      have hv : v ∈ support := by
        rw [maskHas_maskOfVertices12] at present
        exact of_decide_eq_true present
      let uFin : Fin 12 := ⟨u, List.mem_range.mp huRange⟩
      refine Or.inr ⟨hv, uFin, ?_, ?_⟩
      · change (dpAt12 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11
          u).getLsbD (maskOfVertices12 (support.erase v)) = true
        rw [maskOfVertices12_erase support v hv]
        exact previous
      · exact adjacent
  · intro recurrence
    change (dpAt12 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 v).getLsbD
      (maskOfVertices12 support) = true
    rw [lookup]
    apply Bool.or_eq_true_iff.mpr
    rcases recurrence with singleton | ⟨present, u, previous, adjacent⟩
    · left
      apply decide_eq_true
      exact (maskOfVertices12_eq_twoPow_iff support v).mpr singleton
    · right
      apply List.any_eq_true.mpr
      refine ⟨(u : Nat), List.mem_range.mpr u.isLt, ?_⟩
      simp only [Bool.and_eq_true]
      refine ⟨⟨adjacent, ?_⟩, ?_⟩
      · rw [maskHas_maskOfVertices12]
        exact decide_eq_true present
      · change (dpAt12 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11
          u).getLsbD (maskOfVertices12 (support.erase v)) = true at previous
        rw [maskOfVertices12_erase support v present] at previous
        exact previous

theorem dpConsistent12Split_of_recurrence (g : BitVec 66)
    (d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 : BitVec 4096)
    (recurrence : WOWII217Semantics.EndpointRecurrence
      (graphOfUpper (n := 12) g)
      (dpTable12 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11)) :
    hamiltonianDPConsistent12Split g
      d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 = true := by
  apply List.all_eq_true.mpr
  intro v hvRange
  have hvlt : v < 12 := List.mem_range.mp hvRange
  let vFin : Fin 12 := ⟨v, hvlt⟩
  apply beq_iff_eq.mpr
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro mask hmask
  let maskFin : Fin 4096 := ⟨mask, hmask⟩
  change
    (dpAt12 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 vFin).getLsbD
        maskFin =
      (dpNextBlock12 g d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11
        vFin).getLsbD maskFin
  rw [dpNextBlock12_getLsbD]
  apply Bool.eq_iff_iff.mpr
  change
    ((dpAt12 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 v).getLsbD
        mask = true) ↔
      ((decide (mask = 2 ^ v) ||
        (List.range 12).any fun u =>
          adjUpper (n := 12) g u v && maskHas mask v &&
            (dpAt12 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 u).getLsbD
              (mask - 2 ^ v)) = true)
  let support := verticesOfMask12 maskFin
  have supportMask : maskOfVertices12 support = mask := by
    exact maskOfVertices12_verticesOfMask12 maskFin
  constructor
  · intro marked
    have tableMarked :
        dpTable12 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 support vFin := by
      change (dpAt12 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 v).getLsbD
        (maskOfVertices12 support) = true
      rw [supportMask]
      exact marked
    rcases (recurrence support vFin).mp tableMarked with singleton | extended
    · apply Bool.or_eq_true_iff.mpr
      left
      apply decide_eq_true
      calc
        mask = maskOfVertices12 support := supportMask.symm
        _ = maskOfVertices12 {vFin} := congrArg maskOfVertices12 singleton
        _ = 2 ^ v := maskOfVertices12_singleton vFin
    · obtain ⟨present, u, previous, adjacent⟩ := extended
      apply Bool.or_eq_true_iff.mpr
      right
      apply List.any_eq_true.mpr
      refine ⟨(u : Nat), List.mem_range.mpr u.isLt, ?_⟩
      simp only [Bool.and_eq_true]
      refine ⟨⟨adjacent, ?_⟩, ?_⟩
      · exact (maskHas_eq_true_iff_mem12 maskFin vFin).mpr present
      · change (dpAt12 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11
          u).getLsbD (maskOfVertices12 (support.erase vFin)) = true at previous
        rw [maskOfVertices12_erase support vFin present, supportMask] at previous
        exact previous
  · intro encoded
    rcases Bool.or_eq_true_iff.mp encoded with singleton | extended
    · have maskEq : mask = 2 ^ v := of_decide_eq_true singleton
      have supportEq : support = {vFin} := by
        dsimp only [support]
        change verticesOfMask12 mask = {vFin}
        rw [maskEq]
        exact verticesOfMask12_singleton vFin
      have tableMarked := (recurrence support vFin).mpr (Or.inl supportEq)
      change (dpAt12 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 v).getLsbD
        (maskOfVertices12 support) = true at tableMarked
      rw [supportMask] at tableMarked
      exact tableMarked
    · obtain ⟨u, huRange, hu⟩ := List.any_eq_true.mp extended
      simp only [Bool.and_eq_true] at hu
      rcases hu with ⟨⟨adjacent, present⟩, previous⟩
      let uFin : Fin 12 := ⟨u, List.mem_range.mp huRange⟩
      have hvPresent : vFin ∈ support :=
        (maskHas_eq_true_iff_mem12 maskFin vFin).mp present
      have tablePrevious :
          dpTable12 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11
            (support.erase vFin) uFin := by
        change (dpAt12 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11
          u).getLsbD (maskOfVertices12 (support.erase vFin)) = true
        rw [maskOfVertices12_erase support vFin hvPresent, supportMask]
        exact previous
      have tableMarked := (recurrence support vFin).mpr
        (Or.inr ⟨hvPresent, uFin, tablePrevious, adjacent⟩)
      change (dpAt12 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 v).getLsbD
        (maskOfVertices12 support) = true at tableMarked
      rw [supportMask] at tableMarked
      exact tableMarked

theorem dpAt12_endpointBlocks (g : BitVec 66) (u : Nat) (hu : u < 12) :
    dpAt12 (endpointBlock12 g 0) (endpointBlock12 g 1)
      (endpointBlock12 g 2) (endpointBlock12 g 3)
      (endpointBlock12 g 4) (endpointBlock12 g 5)
      (endpointBlock12 g 6) (endpointBlock12 g 7)
      (endpointBlock12 g 8) (endpointBlock12 g 9)
      (endpointBlock12 g 10) (endpointBlock12 g 11) u =
        endpointBlock12 g ⟨u, hu⟩ := by
  interval_cases u <;> rfl

theorem endpointBlocks_dpTable_iff (g : BitVec 66)
    (support : Finset (Fin 12)) (v : Fin 12) :
    dpTable12 (endpointBlock12 g 0) (endpointBlock12 g 1)
      (endpointBlock12 g 2) (endpointBlock12 g 3)
      (endpointBlock12 g 4) (endpointBlock12 g 5)
      (endpointBlock12 g 6) (endpointBlock12 g 7)
      (endpointBlock12 g 8) (endpointBlock12 g 9)
      (endpointBlock12 g 10) (endpointBlock12 g 11) support v ↔
        WOWII217Semantics.EndpointReachable
          (graphOfUpper (n := 12) g) support v := by
  change
    (dpAt12 (endpointBlock12 g 0) (endpointBlock12 g 1)
      (endpointBlock12 g 2) (endpointBlock12 g 3)
      (endpointBlock12 g 4) (endpointBlock12 g 5)
      (endpointBlock12 g 6) (endpointBlock12 g 7)
      (endpointBlock12 g 8) (endpointBlock12 g 9)
      (endpointBlock12 g 10) (endpointBlock12 g 11) v).getLsbD
        (maskOfVertices12 support) = true ↔ _
  rw [dpAt12_endpointBlocks g v v.isLt]
  have lookup := endpointBlock12_getLsbD_eq_true_iff g v
    (maskOfVertices12Fin support)
  simp only [maskOfVertices12Fin, verticesOfMask12_maskOfVertices12] at lookup
  exact lookup

theorem endpointBlocks_recurrence (g : BitVec 66) :
    WOWII217Semantics.EndpointRecurrence (graphOfUpper (n := 12) g)
      (dpTable12 (endpointBlock12 g 0) (endpointBlock12 g 1)
        (endpointBlock12 g 2) (endpointBlock12 g 3)
        (endpointBlock12 g 4) (endpointBlock12 g 5)
        (endpointBlock12 g 6) (endpointBlock12 g 7)
        (endpointBlock12 g 8) (endpointBlock12 g 9)
        (endpointBlock12 g 10) (endpointBlock12 g 11)) := by
  intro support v
  simpa only [endpointBlocks_dpTable_iff] using
    (WOWII217Semantics.EndpointReachable.recurrence
      (G := graphOfUpper (n := 12) g) support v)

theorem endpointBlocks_consistent (g : BitVec 66) :
    hamiltonianDPConsistent12Split g
      (endpointBlock12 g 0) (endpointBlock12 g 1)
      (endpointBlock12 g 2) (endpointBlock12 g 3)
      (endpointBlock12 g 4) (endpointBlock12 g 5)
      (endpointBlock12 g 6) (endpointBlock12 g 7)
      (endpointBlock12 g 8) (endpointBlock12 g 9)
      (endpointBlock12 g 10) (endpointBlock12 g 11) = true := by
  exact dpConsistent12Split_of_recurrence g
    (endpointBlock12 g 0) (endpointBlock12 g 1)
    (endpointBlock12 g 2) (endpointBlock12 g 3)
    (endpointBlock12 g 4) (endpointBlock12 g 5)
    (endpointBlock12 g 6) (endpointBlock12 g 7)
    (endpointBlock12 g 8) (endpointBlock12 g 9)
    (endpointBlock12 g 10) (endpointBlock12 g 11)
    (endpointBlocks_recurrence g)

theorem traceable_of_endpointBlock12_full (g : BitVec 66) (v : Fin 12)
    (full : (endpointBlock12 g v).getLsbD 4095 = true) :
    Traceable (graphOfUpper (n := 12) g) := by
  have lookup := endpointBlock12_getLsbD_eq_true_iff g v
    (4095 : Fin 4096)
  have reachable : WOWII217Semantics.EndpointReachable
      (graphOfUpper (n := 12) g) Finset.univ v := by
    apply lookup.mp
    exact full
  exact reachable.exists_hamiltonian_walk

theorem traceable_of_endpointBlocks12_full (g : BitVec 66)
    (full : hamiltonianDPHasFullPath12Split
      (endpointBlock12 g 0) (endpointBlock12 g 1)
      (endpointBlock12 g 2) (endpointBlock12 g 3)
      (endpointBlock12 g 4) (endpointBlock12 g 5)
      (endpointBlock12 g 6) (endpointBlock12 g 7)
      (endpointBlock12 g 8) (endpointBlock12 g 9)
      (endpointBlock12 g 10) (endpointBlock12 g 11) = true) :
    Traceable (graphOfUpper (n := 12) g) := by
  simp only [hamiltonianDPHasFullPath12Split, Bool.or_eq_true] at full
  rcases full with ((((((((((h0 | h1) | h2) | h3) | h4) | h5) | h6) |
    h7) | h8) | h9) | h10) | h11
  · exact traceable_of_endpointBlock12_full g 0 h0
  · exact traceable_of_endpointBlock12_full g 1 h1
  · exact traceable_of_endpointBlock12_full g 2 h2
  · exact traceable_of_endpointBlock12_full g 3 h3
  · exact traceable_of_endpointBlock12_full g 4 h4
  · exact traceable_of_endpointBlock12_full g 5 h5
  · exact traceable_of_endpointBlock12_full g 6 h6
  · exact traceable_of_endpointBlock12_full g 7 h7
  · exact traceable_of_endpointBlock12_full g 8 h8
  · exact traceable_of_endpointBlock12_full g 9 h9
  · exact traceable_of_endpointBlock12_full g 10 h10
  · exact traceable_of_endpointBlock12_full g 11 h11

theorem traceable_of_canonicalFiveRegular12 (g : BitVec 66)
    (connected : connectedUpper (n := 12) g = true)
    (degrees : fixedDegreeSequenceUpper (n := 12) g
      [5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5] = true)
    (zeroNeighborhood : canonicalZeroNeighborhood12 g = true)
    (partitionSorted : canonicalPartitionDegreesSorted12 g = true) :
    Traceable (graphOfUpper (n := 12) g) := by
  have consistent := endpointBlocks_consistent g
  have certificate := canonicalFiveRegular12_hasHamiltonianDPState g
    (endpointBlock12 g 0) (endpointBlock12 g 1)
    (endpointBlock12 g 2) (endpointBlock12 g 3)
    (endpointBlock12 g 4) (endpointBlock12 g 5)
    (endpointBlock12 g 6) (endpointBlock12 g 7)
    (endpointBlock12 g 8) (endpointBlock12 g 9)
    (endpointBlock12 g 10) (endpointBlock12 g 11)
  rw [connected, degrees, zeroNeighborhood, partitionSorted, consistent] at certificate
  simp only [Bool.true_and] at certificate
  have full : hamiltonianDPHasFullPath12Split
      (endpointBlock12 g 0) (endpointBlock12 g 1)
      (endpointBlock12 g 2) (endpointBlock12 g 3)
      (endpointBlock12 g 4) (endpointBlock12 g 5)
      (endpointBlock12 g 6) (endpointBlock12 g 7)
      (endpointBlock12 g 8) (endpointBlock12 g 9)
      (endpointBlock12 g 10) (endpointBlock12 g 11) = true := by
    by_contra notFull
    have fullFalse : hamiltonianDPHasFullPath12Split
        (endpointBlock12 g 0) (endpointBlock12 g 1)
        (endpointBlock12 g 2) (endpointBlock12 g 3)
        (endpointBlock12 g 4) (endpointBlock12 g 5)
        (endpointBlock12 g 6) (endpointBlock12 g 7)
        (endpointBlock12 g 8) (endpointBlock12 g 9)
        (endpointBlock12 g 10) (endpointBlock12 g 11) = false :=
      Bool.eq_false_of_not_eq_true notFull
    simp [fullFalse] at certificate
  exact traceable_of_endpointBlocks12_full g full

end WOWII217Finite12Semantics
