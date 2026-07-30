import WOWII217Semantics
import WOWII217Finite10Regular
import WOWII217ClosureSemantics

/-!
Semantic interpretation of the split Held--Karp table in the certified
connected 4-regular order-10 case.
-/

namespace WOWII217Finite10Semantics

open SimpleGraph
open WOWII217FiniteBase WOWII217Finite10Regular
open WOWII217ClosureSemantics
open WOWII217BondyChvatal

def verticesOfMask10 (mask : Nat) : Finset (Fin 10) :=
  Finset.univ.filter fun v => maskHas mask v = true

def maskOfVertices10 (support : Finset (Fin 10)) : Nat :=
  support.sum fun v => 2 ^ (v : Nat)

theorem maskOfVertices10_lt :
    ∀ support : Finset (Fin 10), maskOfVertices10 support < 1024 := by
  native_decide

def maskOfVertices10Fin (support : Finset (Fin 10)) : Fin 1024 :=
  ⟨maskOfVertices10 support, maskOfVertices10_lt support⟩

theorem verticesOfMask10_maskOfVertices10 :
    ∀ support : Finset (Fin 10),
      verticesOfMask10 (maskOfVertices10 support) = support := by
  native_decide

theorem maskOfVertices10_verticesOfMask10 :
    ∀ mask : Fin 1024,
      maskOfVertices10 (verticesOfMask10 mask) = mask := by
  native_decide

theorem maskHas_maskOfVertices10 :
    ∀ (support : Finset (Fin 10)) (v : Fin 10),
      maskHas (maskOfVertices10 support) v = decide (v ∈ support) := by
  native_decide

theorem maskOfVertices10_singleton :
    ∀ v : Fin 10, maskOfVertices10 {v} = 2 ^ (v : Nat) := by
  native_decide

theorem maskOfVertices10_univ :
    maskOfVertices10 (Finset.univ : Finset (Fin 10)) = 1023 := by
  native_decide

theorem maskOfVertices10_eq_twoPow_iff :
    ∀ (support : Finset (Fin 10)) (v : Fin 10),
      maskOfVertices10 support = 2 ^ (v : Nat) ↔ support = {v} := by
  native_decide

theorem maskOfVertices10_erase :
    ∀ (support : Finset (Fin 10)) (v : Fin 10),
      v ∈ support →
      maskOfVertices10 (support.erase v) =
        maskOfVertices10 support - 2 ^ (v : Nat) := by
  native_decide

theorem verticesOfMask10_full :
    verticesOfMask10 1023 = Finset.univ := by
  native_decide

theorem verticesOfMask10_singleton :
    ∀ v : Fin 10, verticesOfMask10 (2 ^ (v : Nat)) = {v} := by
  native_decide

theorem maskHas_eq_true_iff_mem10 (mask : Fin 1024) (v : Fin 10) :
    maskHas mask v = true ↔ v ∈ verticesOfMask10 mask := by
  simp [verticesOfMask10]

noncomputable def endpointBlock10 (g : BitVec 45) (v : Fin 10) : BitVec 1024 := by
  classical
  let f := fun mask : Fin 1024 =>
    decide (WOWII217Semantics.EndpointReachable
      (graphOfUpper (n := 10) g) (verticesOfMask10 mask) v)
  exact BitVec.cast List.length_ofFn (BitVec.ofBoolListLE (List.ofFn f))

theorem endpointBlock10_getLsbD_eq_true_iff (g : BitVec 45) (v : Fin 10)
    (mask : Fin 1024) :
    (endpointBlock10 g v).getLsbD mask = true ↔
      WOWII217Semantics.EndpointReachable
        (graphOfUpper (n := 10) g) (verticesOfMask10 mask) v := by
  classical
  unfold endpointBlock10
  simp only [BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE]
  let f := fun index : Fin 1024 =>
    decide (WOWII217Semantics.EndpointReachable
      (graphOfUpper (n := 10) g) (verticesOfMask10 index) v)
  change (List.ofFn f).getD (mask : Nat) false = true ↔
    WOWII217Semantics.EndpointReachable
      (graphOfUpper (n := 10) g) (verticesOfMask10 mask) v
  have hmask : (mask : Nat) < (List.ofFn f).length := by
    rw [List.length_ofFn]
    exact mask.isLt
  rw [List.getD_eq_getElem (l := List.ofFn f) (d := false) hmask]
  rw [List.getElem_ofFn]
  exact decide_eq_true_iff

theorem getLsbD_foldl_or10 {w : Nat} {β : Type*} (xs : List β)
    (f : β → BitVec w) (initial : BitVec w) (i : Nat) :
    (xs.foldl (fun states x => states ||| f x) initial).getLsbD i =
      (initial.getLsbD i || xs.any fun x => (f x).getLsbD i) := by
  induction xs generalizing initial with
  | nil => simp
  | cons x xs ih =>
      simp only [List.foldl_cons, ih, BitVec.getLsbD_or, List.any_cons]
      simp only [Bool.or_assoc]

theorem absentMask10_getLsbD :
    ∀ (mask : Fin 1024) (v : Fin 10),
      (absentMask 10 v).getLsbD mask = !maskHas mask v := by
  native_decide

theorem shiftedFreshControl10 :
    ∀ (mask : Fin 1024) (v : Fin 10) (b : Bool),
      (!decide ((mask : Nat) < 2 ^ (v : Nat)) &&
          (b && (absentMask 10 v).getLsbD
            ((mask : Nat) - 2 ^ (v : Nat)))) =
        (maskHas mask v && b) := by
  native_decide

theorem shiftedFreshBlock_getLsbD10 (block : BitVec 1024)
    (mask : Fin 1024) (v : Fin 10) :
    (((block &&& absentMask 10 v) <<< (2 ^ (v : Nat))).getLsbD mask) =
      (maskHas mask v && block.getLsbD (mask - 2 ^ (v : Nat))) := by
  simp only [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_and]
  have width : (mask : Nat) < 1024 := mask.isLt
  simp only [width, decide_true, Bool.true_and]
  exact shiftedFreshControl10 mask v
    (block.getLsbD ((mask : Nat) - 2 ^ (v : Nat)))

theorem bitMask1024_getLsbD :
    ∀ (b : Bool) (i : Fin 1024),
      (bitMask (w := 1024) b).getLsbD i = b := by
  intro b i
  simp only [bitMask, BitVec.getLsbD_cast, BitVec.getLsbD_replicate,
    Nat.one_mul, i.isLt, decide_true, Bool.true_and, Nat.mod_one,
    BitVec.getLsbD_ofBool, Bool.and_self]

theorem twoPowIndex10_lt :
    ∀ v : Fin 10, 2 ^ (v : Nat) < 1024 := by
  native_decide

theorem twoPow1024_getLsbD :
    ∀ (mask : Fin 1024) (v : Fin 10),
      (BitVec.twoPow 1024 (2 ^ (v : Nat))).getLsbD mask =
        decide ((mask : Nat) = 2 ^ (v : Nat)) := by
  intro mask v
  simp [BitVec.getLsbD_twoPow, twoPowIndex10_lt v, eq_comm]

def dpNextBlock10 (g : BitVec 45)
    (d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 : BitVec 1024) :
    Nat → BitVec 1024 := fun v =>
  let extended := (List.range 10).foldl (fun states u =>
    states ||| (bitMask (w := 1024) (adjUpper (n := 10) g u v) &&&
      ((dpAt10 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 u &&&
        absentMask 10 v) <<< (2 ^ v)))) 0#1024
  BitVec.twoPow 1024 (2 ^ v) ||| extended

theorem extensionBlock10_getLsbD (g : BitVec 45) (block : BitVec 1024)
    (mask : Fin 1024) (u : Nat) (v : Fin 10) :
    (bitMask (w := 1024) (adjUpper (n := 10) g u v) &&&
        ((block &&& absentMask 10 v) <<< (2 ^ (v : Nat)))).getLsbD mask =
      (adjUpper (n := 10) g u v && maskHas mask v &&
        block.getLsbD (mask - 2 ^ (v : Nat))) := by
  rw [BitVec.getLsbD_and, bitMask1024_getLsbD,
    shiftedFreshBlock_getLsbD10]
  simp only [Bool.and_assoc]

theorem dpNextBlock10_getLsbD (g : BitVec 45)
    (d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 : BitVec 1024)
    (mask : Fin 1024) (v : Fin 10) :
    (dpNextBlock10 g d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 v).getLsbD
        mask =
      (decide ((mask : Nat) = 2 ^ (v : Nat)) ||
        (List.range 10).any fun u =>
          adjUpper (n := 10) g u v && maskHas mask v &&
            (dpAt10 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 u).getLsbD
              ((mask : Nat) - 2 ^ (v : Nat))) := by
  simp only [dpNextBlock10, BitVec.getLsbD_or, twoPow1024_getLsbD,
    getLsbD_foldl_or10, BitVec.getLsbD_zero, Bool.false_or,
    extensionBlock10_getLsbD]

theorem dpLookupOfConsistent10Split (g : BitVec 45)
    (d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 : BitVec 1024)
    (consistent : hamiltonianDPConsistent10Split g
      d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 = true)
    (mask : Fin 1024) (v : Fin 10) :
    (dpAt10 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 v).getLsbD mask =
      (decide ((mask : Nat) = 2 ^ (v : Nat)) ||
        (List.range 10).any fun u =>
          adjUpper (n := 10) g u v && maskHas mask v &&
            (dpAt10 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 u).getLsbD
              ((mask : Nat) - 2 ^ (v : Nat))) := by
  have blockEqualityBool :=
    (List.all_eq_true.mp consistent) (v : Nat) (List.mem_range.mpr v.isLt)
  have blockEquality := beq_iff_eq.mp blockEqualityBool
  have lookupEquality := congrArg
    (fun block : BitVec 1024 => block.getLsbD mask) blockEquality
  change (dpAt10 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 v).getLsbD
    mask =
    (dpNextBlock10 g d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 v).getLsbD
      mask at lookupEquality
  rw [dpNextBlock10_getLsbD] at lookupEquality
  exact lookupEquality

def dpTable10
    (d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 : BitVec 1024)
    (support : Finset (Fin 10)) (v : Fin 10) : Prop :=
  (dpAt10 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 v).getLsbD
      (maskOfVertices10 support) = true

theorem dpTable10_recurrence (g : BitVec 45)
    (d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 : BitVec 1024)
    (consistent : hamiltonianDPConsistent10Split g
      d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 = true) :
    WOWII217Semantics.EndpointRecurrence (graphOfUpper (n := 10) g)
      (dpTable10 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9) := by
  intro support v
  have lookup := dpLookupOfConsistent10Split g
    d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 consistent
    (maskOfVertices10Fin support) v
  simp only [maskOfVertices10Fin] at lookup
  constructor
  · intro marked
    change (dpAt10 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 v).getLsbD
      (maskOfVertices10 support) = true at marked
    rw [lookup] at marked
    rcases Bool.or_eq_true_iff.mp marked with singleton | extended
    · left
      apply (maskOfVertices10_eq_twoPow_iff support v).mp
      exact of_decide_eq_true singleton
    · obtain ⟨u, huRange, hu⟩ := List.any_eq_true.mp extended
      simp only [Bool.and_eq_true] at hu
      rcases hu with ⟨⟨adjacent, present⟩, previous⟩
      have hv : v ∈ support := by
        rw [maskHas_maskOfVertices10] at present
        exact of_decide_eq_true present
      let uFin : Fin 10 := ⟨u, List.mem_range.mp huRange⟩
      refine Or.inr ⟨hv, uFin, ?_, ?_⟩
      · change (dpAt10 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9
          u).getLsbD (maskOfVertices10 (support.erase v)) = true
        rw [maskOfVertices10_erase support v hv]
        exact previous
      · exact adjacent
  · intro recurrence
    change (dpAt10 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 v).getLsbD
      (maskOfVertices10 support) = true
    rw [lookup]
    apply Bool.or_eq_true_iff.mpr
    rcases recurrence with singleton | ⟨present, u, previous, adjacent⟩
    · left
      apply decide_eq_true
      exact (maskOfVertices10_eq_twoPow_iff support v).mpr singleton
    · right
      apply List.any_eq_true.mpr
      refine ⟨(u : Nat), List.mem_range.mpr u.isLt, ?_⟩
      simp only [Bool.and_eq_true]
      refine ⟨⟨adjacent, ?_⟩, ?_⟩
      · rw [maskHas_maskOfVertices10]
        exact decide_eq_true present
      · change (dpAt10 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9
          u).getLsbD (maskOfVertices10 (support.erase v)) = true at previous
        rw [maskOfVertices10_erase support v present] at previous
        exact previous

theorem dpConsistent10Split_of_recurrence (g : BitVec 45)
    (d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 : BitVec 1024)
    (recurrence : WOWII217Semantics.EndpointRecurrence
      (graphOfUpper (n := 10) g)
      (dpTable10 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9)) :
    hamiltonianDPConsistent10Split g
      d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 = true := by
  apply List.all_eq_true.mpr
  intro v hvRange
  have hvlt : v < 10 := List.mem_range.mp hvRange
  let vFin : Fin 10 := ⟨v, hvlt⟩
  apply beq_iff_eq.mpr
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro mask hmask
  let maskFin : Fin 1024 := ⟨mask, hmask⟩
  change
    (dpAt10 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 vFin).getLsbD
        maskFin =
      (dpNextBlock10 g d0 d1 d2 d3 d4 d5 d6 d7 d8 d9
        vFin).getLsbD maskFin
  rw [dpNextBlock10_getLsbD]
  apply Bool.eq_iff_iff.mpr
  change
    ((dpAt10 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 v).getLsbD
        mask = true) ↔
      ((decide (mask = 2 ^ v) ||
        (List.range 10).any fun u =>
          adjUpper (n := 10) g u v && maskHas mask v &&
            (dpAt10 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 u).getLsbD
              (mask - 2 ^ v)) = true)
  let support := verticesOfMask10 maskFin
  have supportMask : maskOfVertices10 support = mask := by
    exact maskOfVertices10_verticesOfMask10 maskFin
  constructor
  · intro marked
    have tableMarked :
        dpTable10 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 support vFin := by
      change (dpAt10 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 v).getLsbD
        (maskOfVertices10 support) = true
      rw [supportMask]
      exact marked
    rcases (recurrence support vFin).mp tableMarked with singleton | extended
    · apply Bool.or_eq_true_iff.mpr
      left
      apply decide_eq_true
      calc
        mask = maskOfVertices10 support := supportMask.symm
        _ = maskOfVertices10 {vFin} := congrArg maskOfVertices10 singleton
        _ = 2 ^ v := maskOfVertices10_singleton vFin
    · obtain ⟨present, u, previous, adjacent⟩ := extended
      apply Bool.or_eq_true_iff.mpr
      right
      apply List.any_eq_true.mpr
      refine ⟨(u : Nat), List.mem_range.mpr u.isLt, ?_⟩
      simp only [Bool.and_eq_true]
      refine ⟨⟨adjacent, ?_⟩, ?_⟩
      · exact (maskHas_eq_true_iff_mem10 maskFin vFin).mpr present
      · change (dpAt10 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9
          u).getLsbD (maskOfVertices10 (support.erase vFin)) = true at previous
        rw [maskOfVertices10_erase support vFin present, supportMask] at previous
        exact previous
  · intro encoded
    rcases Bool.or_eq_true_iff.mp encoded with singleton | extended
    · have maskEq : mask = 2 ^ v := of_decide_eq_true singleton
      have supportEq : support = {vFin} := by
        dsimp only [support]
        change verticesOfMask10 mask = {vFin}
        rw [maskEq]
        exact verticesOfMask10_singleton vFin
      have tableMarked := (recurrence support vFin).mpr (Or.inl supportEq)
      change (dpAt10 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 v).getLsbD
        (maskOfVertices10 support) = true at tableMarked
      rw [supportMask] at tableMarked
      exact tableMarked
    · obtain ⟨u, huRange, hu⟩ := List.any_eq_true.mp extended
      simp only [Bool.and_eq_true] at hu
      rcases hu with ⟨⟨adjacent, present⟩, previous⟩
      let uFin : Fin 10 := ⟨u, List.mem_range.mp huRange⟩
      have hvPresent : vFin ∈ support :=
        (maskHas_eq_true_iff_mem10 maskFin vFin).mp present
      have tablePrevious :
          dpTable10 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9
            (support.erase vFin) uFin := by
        change (dpAt10 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9
          u).getLsbD (maskOfVertices10 (support.erase vFin)) = true
        rw [maskOfVertices10_erase support vFin hvPresent, supportMask]
        exact previous
      have tableMarked := (recurrence support vFin).mpr
        (Or.inr ⟨hvPresent, uFin, tablePrevious, adjacent⟩)
      change (dpAt10 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 v).getLsbD
        (maskOfVertices10 support) = true at tableMarked
      rw [supportMask] at tableMarked
      exact tableMarked

theorem dpAt10_endpointBlocks (g : BitVec 45) (u : Nat) (hu : u < 10) :
    dpAt10 (endpointBlock10 g 0) (endpointBlock10 g 1)
      (endpointBlock10 g 2) (endpointBlock10 g 3)
      (endpointBlock10 g 4) (endpointBlock10 g 5)
      (endpointBlock10 g 6) (endpointBlock10 g 7)
      (endpointBlock10 g 8) (endpointBlock10 g 9) u =
        endpointBlock10 g ⟨u, hu⟩ := by
  interval_cases u <;> rfl

theorem endpointBlocks10_dpTable_iff (g : BitVec 45)
    (support : Finset (Fin 10)) (v : Fin 10) :
    dpTable10 (endpointBlock10 g 0) (endpointBlock10 g 1)
      (endpointBlock10 g 2) (endpointBlock10 g 3)
      (endpointBlock10 g 4) (endpointBlock10 g 5)
      (endpointBlock10 g 6) (endpointBlock10 g 7)
      (endpointBlock10 g 8) (endpointBlock10 g 9) support v ↔
        WOWII217Semantics.EndpointReachable
          (graphOfUpper (n := 10) g) support v := by
  change
    (dpAt10 (endpointBlock10 g 0) (endpointBlock10 g 1)
      (endpointBlock10 g 2) (endpointBlock10 g 3)
      (endpointBlock10 g 4) (endpointBlock10 g 5)
      (endpointBlock10 g 6) (endpointBlock10 g 7)
      (endpointBlock10 g 8) (endpointBlock10 g 9) v).getLsbD
        (maskOfVertices10 support) = true ↔ _
  rw [dpAt10_endpointBlocks g v v.isLt]
  have lookup := endpointBlock10_getLsbD_eq_true_iff g v
    (maskOfVertices10Fin support)
  simp only [maskOfVertices10Fin, verticesOfMask10_maskOfVertices10] at lookup
  exact lookup

theorem endpointBlocks10_recurrence (g : BitVec 45) :
    WOWII217Semantics.EndpointRecurrence (graphOfUpper (n := 10) g)
      (dpTable10 (endpointBlock10 g 0) (endpointBlock10 g 1)
        (endpointBlock10 g 2) (endpointBlock10 g 3)
        (endpointBlock10 g 4) (endpointBlock10 g 5)
        (endpointBlock10 g 6) (endpointBlock10 g 7)
        (endpointBlock10 g 8) (endpointBlock10 g 9)) := by
  intro support v
  simpa only [endpointBlocks10_dpTable_iff] using
    (WOWII217Semantics.EndpointReachable.recurrence
      (G := graphOfUpper (n := 10) g) support v)

theorem endpointBlocks10_consistent (g : BitVec 45) :
    hamiltonianDPConsistent10Split g
      (endpointBlock10 g 0) (endpointBlock10 g 1)
      (endpointBlock10 g 2) (endpointBlock10 g 3)
      (endpointBlock10 g 4) (endpointBlock10 g 5)
      (endpointBlock10 g 6) (endpointBlock10 g 7)
      (endpointBlock10 g 8) (endpointBlock10 g 9) = true := by
  exact dpConsistent10Split_of_recurrence g
    (endpointBlock10 g 0) (endpointBlock10 g 1)
    (endpointBlock10 g 2) (endpointBlock10 g 3)
    (endpointBlock10 g 4) (endpointBlock10 g 5)
    (endpointBlock10 g 6) (endpointBlock10 g 7)
    (endpointBlock10 g 8) (endpointBlock10 g 9)
    (endpointBlocks10_recurrence g)

theorem traceable_of_endpointBlock10_full (g : BitVec 45) (v : Fin 10)
    (full : (endpointBlock10 g v).getLsbD 1023 = true) :
    Traceable (graphOfUpper (n := 10) g) := by
  have lookup := endpointBlock10_getLsbD_eq_true_iff g v
    (1023 : Fin 1024)
  have reachable : WOWII217Semantics.EndpointReachable
      (graphOfUpper (n := 10) g) Finset.univ v := by
    apply lookup.mp
    exact full
  exact reachable.exists_hamiltonian_walk

theorem traceable_of_endpointBlocks10_full (g : BitVec 45)
    (full : hamiltonianDPHasFullPath10Split
      (endpointBlock10 g 0) (endpointBlock10 g 1)
      (endpointBlock10 g 2) (endpointBlock10 g 3)
      (endpointBlock10 g 4) (endpointBlock10 g 5)
      (endpointBlock10 g 6) (endpointBlock10 g 7)
      (endpointBlock10 g 8) (endpointBlock10 g 9) = true) :
    Traceable (graphOfUpper (n := 10) g) := by
  simp only [hamiltonianDPHasFullPath10Split, Bool.or_eq_true] at full
  rcases full with (((((((((h0 | h1) | h2) | h3) | h4) | h5) | h6) | h7) | h8) | h9)
  · exact traceable_of_endpointBlock10_full g 0 h0
  · exact traceable_of_endpointBlock10_full g 1 h1
  · exact traceable_of_endpointBlock10_full g 2 h2
  · exact traceable_of_endpointBlock10_full g 3 h3
  · exact traceable_of_endpointBlock10_full g 4 h4
  · exact traceable_of_endpointBlock10_full g 5 h5
  · exact traceable_of_endpointBlock10_full g 6 h6
  · exact traceable_of_endpointBlock10_full g 7 h7
  · exact traceable_of_endpointBlock10_full g 8 h8
  · exact traceable_of_endpointBlock10_full g 9 h9

theorem traceable_of_fourRegular10 (g : BitVec 45)
    (connected : connectedUpper (n := 10) g = true)
    (degrees : fixedDegreeSequenceUpper (n := 10) g
      [4, 4, 4, 4, 4, 4, 4, 4, 4, 4] = true) :
    Traceable (graphOfUpper (n := 10) g) := by
  have consistent := endpointBlocks10_consistent g
  have certificate := fourRegular10_hasHamiltonianDPState g
    (endpointBlock10 g 0) (endpointBlock10 g 1)
    (endpointBlock10 g 2) (endpointBlock10 g 3)
    (endpointBlock10 g 4) (endpointBlock10 g 5)
    (endpointBlock10 g 6) (endpointBlock10 g 7)
    (endpointBlock10 g 8) (endpointBlock10 g 9)
  rw [connected, degrees, consistent] at certificate
  simp only [Bool.true_and] at certificate
  have full : hamiltonianDPHasFullPath10Split
      (endpointBlock10 g 0) (endpointBlock10 g 1)
      (endpointBlock10 g 2) (endpointBlock10 g 3)
      (endpointBlock10 g 4) (endpointBlock10 g 5)
      (endpointBlock10 g 6) (endpointBlock10 g 7)
      (endpointBlock10 g 8) (endpointBlock10 g 9) = true := by
    by_contra notFull
    have fullFalse : hamiltonianDPHasFullPath10Split
        (endpointBlock10 g 0) (endpointBlock10 g 1)
        (endpointBlock10 g 2) (endpointBlock10 g 3)
        (endpointBlock10 g 4) (endpointBlock10 g 5)
        (endpointBlock10 g 6) (endpointBlock10 g 7)
        (endpointBlock10 g 8) (endpointBlock10 g 9) = false :=
      Bool.eq_false_of_not_eq_true notFull
    simp [fullFalse] at certificate
  exact traceable_of_endpointBlocks10_full g full

end WOWII217Finite10Semantics
