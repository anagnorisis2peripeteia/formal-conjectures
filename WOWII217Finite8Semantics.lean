import WOWII217Semantics
import WOWII217Finite8Cubic
import WOWII217ClosureSemantics

/-!
Semantic interpretation of the split Held--Karp table in the certified
connected 3-regular order-8 case.
-/

namespace WOWII217Finite8Semantics

open SimpleGraph
open WOWII217FiniteBase WOWII217Finite8Cubic
open WOWII217ClosureSemantics
open WOWII217BondyChvatal

def verticesOfMask8 (mask : Nat) : Finset (Fin 8) :=
  Finset.univ.filter fun v => maskHas mask v = true

def maskOfVertices8 (support : Finset (Fin 8)) : Nat :=
  support.sum fun v => 2 ^ (v : Nat)

theorem maskOfVertices8_lt :
    ∀ support : Finset (Fin 8), maskOfVertices8 support < 256 := by
  native_decide

def maskOfVertices8Fin (support : Finset (Fin 8)) : Fin 256 :=
  ⟨maskOfVertices8 support, maskOfVertices8_lt support⟩

theorem verticesOfMask8_maskOfVertices8 :
    ∀ support : Finset (Fin 8),
      verticesOfMask8 (maskOfVertices8 support) = support := by
  native_decide

theorem maskOfVertices8_verticesOfMask8 :
    ∀ mask : Fin 256,
      maskOfVertices8 (verticesOfMask8 mask) = mask := by
  native_decide

theorem maskHas_maskOfVertices8 :
    ∀ (support : Finset (Fin 8)) (v : Fin 8),
      maskHas (maskOfVertices8 support) v = decide (v ∈ support) := by
  native_decide

theorem maskOfVertices8_singleton :
    ∀ v : Fin 8, maskOfVertices8 {v} = 2 ^ (v : Nat) := by
  native_decide

theorem maskOfVertices8_univ :
    maskOfVertices8 (Finset.univ : Finset (Fin 8)) = 255 := by
  native_decide

theorem maskOfVertices8_eq_twoPow_iff :
    ∀ (support : Finset (Fin 8)) (v : Fin 8),
      maskOfVertices8 support = 2 ^ (v : Nat) ↔ support = {v} := by
  native_decide

theorem maskOfVertices8_erase :
    ∀ (support : Finset (Fin 8)) (v : Fin 8),
      v ∈ support →
      maskOfVertices8 (support.erase v) =
        maskOfVertices8 support - 2 ^ (v : Nat) := by
  native_decide

theorem verticesOfMask8_full :
    verticesOfMask8 255 = Finset.univ := by
  native_decide

theorem verticesOfMask8_singleton :
    ∀ v : Fin 8, verticesOfMask8 (2 ^ (v : Nat)) = {v} := by
  native_decide

theorem maskHas_eq_true_iff_mem8 (mask : Fin 256) (v : Fin 8) :
    maskHas mask v = true ↔ v ∈ verticesOfMask8 mask := by
  simp [verticesOfMask8]

noncomputable def endpointBlock8 (g : BitVec 28) (v : Fin 8) : BitVec 256 := by
  classical
  let f := fun mask : Fin 256 =>
    decide (WOWII217Semantics.EndpointReachable
      (graphOfUpper (n := 8) g) (verticesOfMask8 mask) v)
  exact BitVec.cast List.length_ofFn (BitVec.ofBoolListLE (List.ofFn f))

theorem endpointBlock8_getLsbD_eq_true_iff (g : BitVec 28) (v : Fin 8)
    (mask : Fin 256) :
    (endpointBlock8 g v).getLsbD mask = true ↔
      WOWII217Semantics.EndpointReachable
        (graphOfUpper (n := 8) g) (verticesOfMask8 mask) v := by
  classical
  unfold endpointBlock8
  simp only [BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE]
  let f := fun index : Fin 256 =>
    decide (WOWII217Semantics.EndpointReachable
      (graphOfUpper (n := 8) g) (verticesOfMask8 index) v)
  change (List.ofFn f).getD (mask : Nat) false = true ↔
    WOWII217Semantics.EndpointReachable
      (graphOfUpper (n := 8) g) (verticesOfMask8 mask) v
  have hmask : (mask : Nat) < (List.ofFn f).length := by
    rw [List.length_ofFn]
    exact mask.isLt
  rw [List.getD_eq_getElem (l := List.ofFn f) (d := false) hmask]
  rw [List.getElem_ofFn]
  exact decide_eq_true_iff

theorem getLsbD_foldl_or8 {w : Nat} {β : Type*} (xs : List β)
    (f : β → BitVec w) (initial : BitVec w) (i : Nat) :
    (xs.foldl (fun states x => states ||| f x) initial).getLsbD i =
      (initial.getLsbD i || xs.any fun x => (f x).getLsbD i) := by
  induction xs generalizing initial with
  | nil => simp
  | cons x xs ih =>
      simp only [List.foldl_cons, ih, BitVec.getLsbD_or, List.any_cons]
      simp only [Bool.or_assoc]

theorem absentMask8_getLsbD :
    ∀ (mask : Fin 256) (v : Fin 8),
      (absentMask 8 v).getLsbD mask = !maskHas mask v := by
  native_decide

theorem shiftedFreshControl8 :
    ∀ (mask : Fin 256) (v : Fin 8) (b : Bool),
      (!decide ((mask : Nat) < 2 ^ (v : Nat)) &&
          (b && (absentMask 8 v).getLsbD
            ((mask : Nat) - 2 ^ (v : Nat)))) =
        (maskHas mask v && b) := by
  native_decide

theorem shiftedFreshBlock_getLsbD8 (block : BitVec 256)
    (mask : Fin 256) (v : Fin 8) :
    (((block &&& absentMask 8 v) <<< (2 ^ (v : Nat))).getLsbD mask) =
      (maskHas mask v && block.getLsbD (mask - 2 ^ (v : Nat))) := by
  simp only [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_and]
  have width : (mask : Nat) < 256 := mask.isLt
  simp only [width, decide_true, Bool.true_and]
  exact shiftedFreshControl8 mask v
    (block.getLsbD ((mask : Nat) - 2 ^ (v : Nat)))

theorem bitMask256_getLsbD :
    ∀ (b : Bool) (i : Fin 256),
      (bitMask (w := 256) b).getLsbD i = b := by
  intro b i
  simp only [bitMask, BitVec.getLsbD_cast, BitVec.getLsbD_replicate,
    Nat.one_mul, i.isLt, decide_true, Bool.true_and, Nat.mod_one,
    BitVec.getLsbD_ofBool, Bool.and_self]

theorem twoPowIndex8_lt :
    ∀ v : Fin 8, 2 ^ (v : Nat) < 256 := by
  native_decide

theorem twoPow256_getLsbD :
    ∀ (mask : Fin 256) (v : Fin 8),
      (BitVec.twoPow 256 (2 ^ (v : Nat))).getLsbD mask =
        decide ((mask : Nat) = 2 ^ (v : Nat)) := by
  intro mask v
  simp [BitVec.getLsbD_twoPow, twoPowIndex8_lt v, eq_comm]

def dpNextBlock8 (g : BitVec 28)
    (d0 d1 d2 d3 d4 d5 d6 d7 : BitVec 256) :
    Nat → BitVec 256 := fun v =>
  let extended := (List.range 8).foldl (fun states u =>
    states ||| (bitMask (w := 256) (adjUpper (n := 8) g u v) &&&
      ((dpAt8 d0 d1 d2 d3 d4 d5 d6 d7 u &&&
        absentMask 8 v) <<< (2 ^ v)))) 0#256
  BitVec.twoPow 256 (2 ^ v) ||| extended

theorem extensionBlock8_getLsbD (g : BitVec 28) (block : BitVec 256)
    (mask : Fin 256) (u : Nat) (v : Fin 8) :
    (bitMask (w := 256) (adjUpper (n := 8) g u v) &&&
        ((block &&& absentMask 8 v) <<< (2 ^ (v : Nat)))).getLsbD mask =
      (adjUpper (n := 8) g u v && maskHas mask v &&
        block.getLsbD (mask - 2 ^ (v : Nat))) := by
  rw [BitVec.getLsbD_and, bitMask256_getLsbD,
    shiftedFreshBlock_getLsbD8]
  simp only [Bool.and_assoc]

theorem dpNextBlock8_getLsbD (g : BitVec 28)
    (d0 d1 d2 d3 d4 d5 d6 d7 : BitVec 256)
    (mask : Fin 256) (v : Fin 8) :
    (dpNextBlock8 g d0 d1 d2 d3 d4 d5 d6 d7 v).getLsbD
        mask =
      (decide ((mask : Nat) = 2 ^ (v : Nat)) ||
        (List.range 8).any fun u =>
          adjUpper (n := 8) g u v && maskHas mask v &&
            (dpAt8 d0 d1 d2 d3 d4 d5 d6 d7 u).getLsbD
              ((mask : Nat) - 2 ^ (v : Nat))) := by
  simp only [dpNextBlock8, BitVec.getLsbD_or, twoPow256_getLsbD,
    getLsbD_foldl_or8, BitVec.getLsbD_zero, Bool.false_or,
    extensionBlock8_getLsbD]

theorem dpLookupOfConsistent8Split (g : BitVec 28)
    (d0 d1 d2 d3 d4 d5 d6 d7 : BitVec 256)
    (consistent : hamiltonianDPConsistent8Split g
      d0 d1 d2 d3 d4 d5 d6 d7 = true)
    (mask : Fin 256) (v : Fin 8) :
    (dpAt8 d0 d1 d2 d3 d4 d5 d6 d7 v).getLsbD mask =
      (decide ((mask : Nat) = 2 ^ (v : Nat)) ||
        (List.range 8).any fun u =>
          adjUpper (n := 8) g u v && maskHas mask v &&
            (dpAt8 d0 d1 d2 d3 d4 d5 d6 d7 u).getLsbD
              ((mask : Nat) - 2 ^ (v : Nat))) := by
  have blockEqualityBool :=
    (List.all_eq_true.mp consistent) (v : Nat) (List.mem_range.mpr v.isLt)
  have blockEquality := beq_iff_eq.mp blockEqualityBool
  have lookupEquality := congrArg
    (fun block : BitVec 256 => block.getLsbD mask) blockEquality
  change (dpAt8 d0 d1 d2 d3 d4 d5 d6 d7 v).getLsbD
    mask =
    (dpNextBlock8 g d0 d1 d2 d3 d4 d5 d6 d7 v).getLsbD
      mask at lookupEquality
  rw [dpNextBlock8_getLsbD] at lookupEquality
  exact lookupEquality

def dpTable8
    (d0 d1 d2 d3 d4 d5 d6 d7 : BitVec 256)
    (support : Finset (Fin 8)) (v : Fin 8) : Prop :=
  (dpAt8 d0 d1 d2 d3 d4 d5 d6 d7 v).getLsbD
      (maskOfVertices8 support) = true

theorem dpTable8_recurrence (g : BitVec 28)
    (d0 d1 d2 d3 d4 d5 d6 d7 : BitVec 256)
    (consistent : hamiltonianDPConsistent8Split g
      d0 d1 d2 d3 d4 d5 d6 d7 = true) :
    WOWII217Semantics.EndpointRecurrence (graphOfUpper (n := 8) g)
      (dpTable8 d0 d1 d2 d3 d4 d5 d6 d7) := by
  intro support v
  have lookup := dpLookupOfConsistent8Split g
    d0 d1 d2 d3 d4 d5 d6 d7 consistent
    (maskOfVertices8Fin support) v
  simp only [maskOfVertices8Fin] at lookup
  constructor
  · intro marked
    change (dpAt8 d0 d1 d2 d3 d4 d5 d6 d7 v).getLsbD
      (maskOfVertices8 support) = true at marked
    rw [lookup] at marked
    rcases Bool.or_eq_true_iff.mp marked with singleton | extended
    · left
      apply (maskOfVertices8_eq_twoPow_iff support v).mp
      exact of_decide_eq_true singleton
    · obtain ⟨u, huRange, hu⟩ := List.any_eq_true.mp extended
      simp only [Bool.and_eq_true] at hu
      rcases hu with ⟨⟨adjacent, present⟩, previous⟩
      have hv : v ∈ support := by
        rw [maskHas_maskOfVertices8] at present
        exact of_decide_eq_true present
      let uFin : Fin 8 := ⟨u, List.mem_range.mp huRange⟩
      refine Or.inr ⟨hv, uFin, ?_, ?_⟩
      · change (dpAt8 d0 d1 d2 d3 d4 d5 d6 d7
          u).getLsbD (maskOfVertices8 (support.erase v)) = true
        rw [maskOfVertices8_erase support v hv]
        exact previous
      · exact adjacent
  · intro recurrence
    change (dpAt8 d0 d1 d2 d3 d4 d5 d6 d7 v).getLsbD
      (maskOfVertices8 support) = true
    rw [lookup]
    apply Bool.or_eq_true_iff.mpr
    rcases recurrence with singleton | ⟨present, u, previous, adjacent⟩
    · left
      apply decide_eq_true
      exact (maskOfVertices8_eq_twoPow_iff support v).mpr singleton
    · right
      apply List.any_eq_true.mpr
      refine ⟨(u : Nat), List.mem_range.mpr u.isLt, ?_⟩
      simp only [Bool.and_eq_true]
      refine ⟨⟨adjacent, ?_⟩, ?_⟩
      · rw [maskHas_maskOfVertices8]
        exact decide_eq_true present
      · change (dpAt8 d0 d1 d2 d3 d4 d5 d6 d7
          u).getLsbD (maskOfVertices8 (support.erase v)) = true at previous
        rw [maskOfVertices8_erase support v present] at previous
        exact previous

theorem dpConsistent8Split_of_recurrence (g : BitVec 28)
    (d0 d1 d2 d3 d4 d5 d6 d7 : BitVec 256)
    (recurrence : WOWII217Semantics.EndpointRecurrence
      (graphOfUpper (n := 8) g)
      (dpTable8 d0 d1 d2 d3 d4 d5 d6 d7)) :
    hamiltonianDPConsistent8Split g
      d0 d1 d2 d3 d4 d5 d6 d7 = true := by
  apply List.all_eq_true.mpr
  intro v hvRange
  have hvlt : v < 8 := List.mem_range.mp hvRange
  let vFin : Fin 8 := ⟨v, hvlt⟩
  apply beq_iff_eq.mpr
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro mask hmask
  let maskFin : Fin 256 := ⟨mask, hmask⟩
  change
    (dpAt8 d0 d1 d2 d3 d4 d5 d6 d7 vFin).getLsbD
        maskFin =
      (dpNextBlock8 g d0 d1 d2 d3 d4 d5 d6 d7
        vFin).getLsbD maskFin
  rw [dpNextBlock8_getLsbD]
  apply Bool.eq_iff_iff.mpr
  change
    ((dpAt8 d0 d1 d2 d3 d4 d5 d6 d7 v).getLsbD
        mask = true) ↔
      ((decide (mask = 2 ^ v) ||
        (List.range 8).any fun u =>
          adjUpper (n := 8) g u v && maskHas mask v &&
            (dpAt8 d0 d1 d2 d3 d4 d5 d6 d7 u).getLsbD
              (mask - 2 ^ v)) = true)
  let support := verticesOfMask8 maskFin
  have supportMask : maskOfVertices8 support = mask := by
    exact maskOfVertices8_verticesOfMask8 maskFin
  constructor
  · intro marked
    have tableMarked :
        dpTable8 d0 d1 d2 d3 d4 d5 d6 d7 support vFin := by
      change (dpAt8 d0 d1 d2 d3 d4 d5 d6 d7 v).getLsbD
        (maskOfVertices8 support) = true
      rw [supportMask]
      exact marked
    rcases (recurrence support vFin).mp tableMarked with singleton | extended
    · apply Bool.or_eq_true_iff.mpr
      left
      apply decide_eq_true
      calc
        mask = maskOfVertices8 support := supportMask.symm
        _ = maskOfVertices8 {vFin} := congrArg maskOfVertices8 singleton
        _ = 2 ^ v := maskOfVertices8_singleton vFin
    · obtain ⟨present, u, previous, adjacent⟩ := extended
      apply Bool.or_eq_true_iff.mpr
      right
      apply List.any_eq_true.mpr
      refine ⟨(u : Nat), List.mem_range.mpr u.isLt, ?_⟩
      simp only [Bool.and_eq_true]
      refine ⟨⟨adjacent, ?_⟩, ?_⟩
      · exact (maskHas_eq_true_iff_mem8 maskFin vFin).mpr present
      · change (dpAt8 d0 d1 d2 d3 d4 d5 d6 d7
          u).getLsbD (maskOfVertices8 (support.erase vFin)) = true at previous
        rw [maskOfVertices8_erase support vFin present, supportMask] at previous
        exact previous
  · intro encoded
    rcases Bool.or_eq_true_iff.mp encoded with singleton | extended
    · have maskEq : mask = 2 ^ v := of_decide_eq_true singleton
      have supportEq : support = {vFin} := by
        dsimp only [support]
        change verticesOfMask8 mask = {vFin}
        rw [maskEq]
        exact verticesOfMask8_singleton vFin
      have tableMarked := (recurrence support vFin).mpr (Or.inl supportEq)
      change (dpAt8 d0 d1 d2 d3 d4 d5 d6 d7 v).getLsbD
        (maskOfVertices8 support) = true at tableMarked
      rw [supportMask] at tableMarked
      exact tableMarked
    · obtain ⟨u, huRange, hu⟩ := List.any_eq_true.mp extended
      simp only [Bool.and_eq_true] at hu
      rcases hu with ⟨⟨adjacent, present⟩, previous⟩
      let uFin : Fin 8 := ⟨u, List.mem_range.mp huRange⟩
      have hvPresent : vFin ∈ support :=
        (maskHas_eq_true_iff_mem8 maskFin vFin).mp present
      have tablePrevious :
          dpTable8 d0 d1 d2 d3 d4 d5 d6 d7
            (support.erase vFin) uFin := by
        change (dpAt8 d0 d1 d2 d3 d4 d5 d6 d7
          u).getLsbD (maskOfVertices8 (support.erase vFin)) = true
        rw [maskOfVertices8_erase support vFin hvPresent, supportMask]
        exact previous
      have tableMarked := (recurrence support vFin).mpr
        (Or.inr ⟨hvPresent, uFin, tablePrevious, adjacent⟩)
      change (dpAt8 d0 d1 d2 d3 d4 d5 d6 d7 v).getLsbD
        (maskOfVertices8 support) = true at tableMarked
      rw [supportMask] at tableMarked
      exact tableMarked

theorem dpAt8_endpointBlocks (g : BitVec 28) (u : Nat) (hu : u < 8) :
    dpAt8 (endpointBlock8 g 0) (endpointBlock8 g 1)
      (endpointBlock8 g 2) (endpointBlock8 g 3)
      (endpointBlock8 g 4) (endpointBlock8 g 5)
      (endpointBlock8 g 6) (endpointBlock8 g 7) u =
        endpointBlock8 g ⟨u, hu⟩ := by
  interval_cases u <;> rfl

theorem endpointBlocks8_dpTable_iff (g : BitVec 28)
    (support : Finset (Fin 8)) (v : Fin 8) :
    dpTable8 (endpointBlock8 g 0) (endpointBlock8 g 1)
      (endpointBlock8 g 2) (endpointBlock8 g 3)
      (endpointBlock8 g 4) (endpointBlock8 g 5)
      (endpointBlock8 g 6) (endpointBlock8 g 7) support v ↔
        WOWII217Semantics.EndpointReachable
          (graphOfUpper (n := 8) g) support v := by
  change
    (dpAt8 (endpointBlock8 g 0) (endpointBlock8 g 1)
      (endpointBlock8 g 2) (endpointBlock8 g 3)
      (endpointBlock8 g 4) (endpointBlock8 g 5)
      (endpointBlock8 g 6) (endpointBlock8 g 7) v).getLsbD
        (maskOfVertices8 support) = true ↔ _
  rw [dpAt8_endpointBlocks g v v.isLt]
  have lookup := endpointBlock8_getLsbD_eq_true_iff g v
    (maskOfVertices8Fin support)
  simp only [maskOfVertices8Fin, verticesOfMask8_maskOfVertices8] at lookup
  exact lookup

theorem endpointBlocks8_recurrence (g : BitVec 28) :
    WOWII217Semantics.EndpointRecurrence (graphOfUpper (n := 8) g)
      (dpTable8 (endpointBlock8 g 0) (endpointBlock8 g 1)
        (endpointBlock8 g 2) (endpointBlock8 g 3)
        (endpointBlock8 g 4) (endpointBlock8 g 5)
        (endpointBlock8 g 6) (endpointBlock8 g 7)) := by
  intro support v
  simpa only [endpointBlocks8_dpTable_iff] using
    (WOWII217Semantics.EndpointReachable.recurrence
      (G := graphOfUpper (n := 8) g) support v)

theorem endpointBlocks8_consistent (g : BitVec 28) :
    hamiltonianDPConsistent8Split g
      (endpointBlock8 g 0) (endpointBlock8 g 1)
      (endpointBlock8 g 2) (endpointBlock8 g 3)
      (endpointBlock8 g 4) (endpointBlock8 g 5)
      (endpointBlock8 g 6) (endpointBlock8 g 7) = true := by
  exact dpConsistent8Split_of_recurrence g
    (endpointBlock8 g 0) (endpointBlock8 g 1)
    (endpointBlock8 g 2) (endpointBlock8 g 3)
    (endpointBlock8 g 4) (endpointBlock8 g 5)
    (endpointBlock8 g 6) (endpointBlock8 g 7)
    (endpointBlocks8_recurrence g)

theorem traceable_of_endpointBlock8_full (g : BitVec 28) (v : Fin 8)
    (full : (endpointBlock8 g v).getLsbD 255 = true) :
    Traceable (graphOfUpper (n := 8) g) := by
  have lookup := endpointBlock8_getLsbD_eq_true_iff g v
    (255 : Fin 256)
  have reachable : WOWII217Semantics.EndpointReachable
      (graphOfUpper (n := 8) g) Finset.univ v := by
    apply lookup.mp
    exact full
  exact reachable.exists_hamiltonian_walk

theorem traceable_of_endpointBlocks8_full (g : BitVec 28)
    (full : hamiltonianDPHasFullPath8Split
      (endpointBlock8 g 0) (endpointBlock8 g 1)
      (endpointBlock8 g 2) (endpointBlock8 g 3)
      (endpointBlock8 g 4) (endpointBlock8 g 5)
      (endpointBlock8 g 6) (endpointBlock8 g 7) = true) :
    Traceable (graphOfUpper (n := 8) g) := by
  simp only [hamiltonianDPHasFullPath8Split, Bool.or_eq_true] at full
  rcases full with (((((((h0 | h1) | h2) | h3) | h4) | h5) | h6) | h7)
  · exact traceable_of_endpointBlock8_full g 0 h0
  · exact traceable_of_endpointBlock8_full g 1 h1
  · exact traceable_of_endpointBlock8_full g 2 h2
  · exact traceable_of_endpointBlock8_full g 3 h3
  · exact traceable_of_endpointBlock8_full g 4 h4
  · exact traceable_of_endpointBlock8_full g 5 h5
  · exact traceable_of_endpointBlock8_full g 6 h6
  · exact traceable_of_endpointBlock8_full g 7 h7

theorem traceable_of_cubic8 (g : BitVec 28)
    (connected : connectedUpper (n := 8) g = true)
    (degrees : fixedDegreeSequenceUpper (n := 8) g
      [3, 3, 3, 3, 3, 3, 3, 3] = true) :
    Traceable (graphOfUpper (n := 8) g) := by
  have consistent := endpointBlocks8_consistent g
  have certificate := cubic8_hasHamiltonianDPState g
    (endpointBlock8 g 0) (endpointBlock8 g 1)
    (endpointBlock8 g 2) (endpointBlock8 g 3)
    (endpointBlock8 g 4) (endpointBlock8 g 5)
    (endpointBlock8 g 6) (endpointBlock8 g 7)
  rw [connected, degrees, consistent] at certificate
  simp only [Bool.true_and] at certificate
  have full : hamiltonianDPHasFullPath8Split
      (endpointBlock8 g 0) (endpointBlock8 g 1)
      (endpointBlock8 g 2) (endpointBlock8 g 3)
      (endpointBlock8 g 4) (endpointBlock8 g 5)
      (endpointBlock8 g 6) (endpointBlock8 g 7) = true := by
    by_contra notFull
    have fullFalse : hamiltonianDPHasFullPath8Split
        (endpointBlock8 g 0) (endpointBlock8 g 1)
        (endpointBlock8 g 2) (endpointBlock8 g 3)
        (endpointBlock8 g 4) (endpointBlock8 g 5)
        (endpointBlock8 g 6) (endpointBlock8 g 7) = false :=
      Bool.eq_false_of_not_eq_true notFull
    simp [fullFalse] at certificate
  exact traceable_of_endpointBlocks8_full g full

end WOWII217Finite8Semantics
