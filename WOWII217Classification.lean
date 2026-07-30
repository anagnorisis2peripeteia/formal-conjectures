import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Residue
import WOWII217SpanningTree
import WOWII217Hamiltonian
import WOWII217Relabel13
import WOWII217Relabel12
import WOWII217Degree12
import WOWII217BondyChvatal
import WOWII217Ore
import WOWII217Chvatal
import WOWII217ResidueBound
import WOWII217Relabel
import WOWII217Connected14
import WOWII217Degree14
import WOWII217Mid13
import WOWII217SmallN

/-!
# Classification entry for residue = 2 and Ls ≤ 6

Proved branches under residue = 2 and Ls ≤ 6:

- `Ls ≤ 2` → Hamiltonian path (spanning-tree argument).
- Dirac-type path condition `n - 1 ≤ 2 · δ(G)` → Ore path theorem.
- Order-13 degree class `6⁷5⁶` → residual path-closure certificate
  (`WOWII217Relabel13`), on both `Fin 13` and any vertex type of card 13.
- Order-12 five-regular → Held–Karp residual certificate (`WOWII217Relabel12`).
- Order-14 six-regular → Held–Karp residual certificate (`WOWII217Relabel`).
- Chvátal path condition → Hamiltonian path (`WOWII217Chvatal`).

Under `maxDegree ≤ 6` (from `Ls ≤ 6`), the Chvátal path condition is
impossible for `n ≥ 13`, so the non-Chvátal residual work concentrates on
finite exceptional classes (order 12/13/14/…).
-/

namespace WOWII217Classification

open Classical SimpleGraph Finset
open WOWII217SpanningTree
open WOWII217BondyChvatal
open WOWII217Relabel13
open WOWII217Relabel12
open WOWII217Relabel
open WOWII217Degree12
open WOWII217Ore
open WOWII217Chvatal
open WOWII217FiniteBase
open WOWII217ResidueBound
open WOWII217Mid13
open WOWII217SmallN

variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]

/-- Residual certificate specialised to labeled `Fin 13` graphs. -/
theorem hamiltonian_of_fin13_degree_class
    (G : SimpleGraph (Fin 13)) [DecidableRel G.Adj]
    (connected : G.Connected)
    (hSix : Fintype.card {v : Fin 13 // G.degree v = 6} = 7)
    (hDeg : ∀ v : Fin 13, G.degree v = 6 ∨ G.degree v = 5) :
    ∃ a b : Fin 13, ∃ p : G.Walk a b, p.IsHamiltonian := by
  have hTrace : Traceable G :=
    traceable_of_degreeCounts_6666666555555 G connected hSix hDeg
  exact hTrace

/-- Transport the residual certificate along any labeling of 13 vertices. -/
theorem hamiltonian_of_order13_degree_class
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : Fintype.card V = 13)
    (connected : G.Connected)
    (hSix : Fintype.card {v : V // G.degree v = 6} = 7)
    (hDeg : ∀ v : V, G.degree v = 6 ∨ G.degree v = 5) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  let e : Fin 13 ≃ V := (Fintype.equivFinOfCardEq hcard).symm
  let G' : SimpleGraph (Fin 13) := G.comap e.toEmbedding
  let iso : G' ≃g G := SimpleGraph.Iso.comap e G
  letI : DecidableRel G'.Adj := fun u v => by
    change Decidable (G.Adj (e u) (e v))
    infer_instance
  have connected' : G'.Connected := iso.connected_iff.mpr connected
  have hDeg' : ∀ v : Fin 13, G'.degree v = 6 ∨ G'.degree v = 5 := by
    intro v
    have hv := hDeg (e v)
    have hdeq : G'.degree v = G.degree (e v) := (iso.degree_eq v).symm
    rwa [hdeq]
  have hSix' : Fintype.card {v : Fin 13 // G'.degree v = 6} = 7 := by
    let φ : {v : Fin 13 // G'.degree v = 6} ≃ {v : V // G.degree v = 6} :=
      { toFun := fun ⟨v, hv⟩ =>
          ⟨e v, by
            have hdeq : G'.degree v = G.degree (e v) := (iso.degree_eq v).symm
            exact hdeq ▸ hv⟩
        invFun := fun ⟨w, hw⟩ =>
          ⟨e.symm w, by
            have hdeq :
                G'.degree (e.symm w) = G.degree w := by
              calc
                G'.degree (e.symm w) = G.degree (e (e.symm w)) :=
                  (iso.degree_eq (e.symm w)).symm
                _ = G.degree w := by rw [Equiv.apply_symm_apply]
            exact hdeq.trans hw⟩
        left_inv := by
          intro ⟨v, _⟩
          ext
          simp
        right_inv := by
          intro ⟨w, _⟩
          ext
          simp }
    simpa using (Fintype.card_congr φ).trans hSix
  have hTrace' : Traceable G' :=
    traceable_of_degreeCounts_6666666555555 G' connected' hSix' hDeg'
  rcases hTrace' with ⟨a, b, p, hp⟩
  exact ⟨e a, e b, p.map iso.toHom, hp.map iso.toHom e.bijective⟩

/-- Five-regular order-12 certificate on `Fin 12`. -/
theorem hamiltonian_of_fin12_five_regular
    (G : SimpleGraph (Fin 12)) [DecidableRel G.Adj]
    (connected : G.Connected)
    (hFive : ∀ v : Fin 12, G.degree v = 5) :
    ∃ a b : Fin 12, ∃ p : G.Walk a b, p.IsHamiltonian := by
  have hFixed := fixedDegreeSequenceUpper_encodeUpper12_of_fiveRegular G hFive
  have hTrace : Traceable G :=
    fiveRegular12Graph_traceable G connected hFixed
  exact hTrace

/-- Transport the five-regular order-12 certificate to any labeling. -/
theorem hamiltonian_of_order12_five_regular
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : Fintype.card V = 12)
    (connected : G.Connected)
    (hFive : ∀ v : V, G.degree v = 5) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  let e : Fin 12 ≃ V := (Fintype.equivFinOfCardEq hcard).symm
  let G' : SimpleGraph (Fin 12) := G.comap e.toEmbedding
  let iso : G' ≃g G := SimpleGraph.Iso.comap e G
  letI : DecidableRel G'.Adj := fun u v => by
    change Decidable (G.Adj (e u) (e v))
    infer_instance
  have connected' : G'.Connected := iso.connected_iff.mpr connected
  have hFive' : ∀ v : Fin 12, G'.degree v = 5 := by
    intro v
    have hdeq : G'.degree v = G.degree (e v) := (iso.degree_eq v).symm
    rw [hdeq]
    exact hFive (e v)
  have hTrace' := hamiltonian_of_fin12_five_regular G' connected' hFive'
  rcases hTrace' with ⟨a, b, p, hp⟩
  exact ⟨e a, e b, p.map iso.toHom, hp.map iso.toHom e.bijective⟩

/-- Six-regular order-14 certificate on `Fin 14`. -/
theorem hamiltonian_of_fin14_six_regular
    (G : SimpleGraph (Fin 14)) [DecidableRel G.Adj]
    (connected : G.Connected)
    (hSix : ∀ v : Fin 14, G.degree v = 6) :
    ∃ a b : Fin 14, ∃ p : G.Walk a b, p.IsHamiltonian :=
  sixRegular14Graph_hasHamiltonianWalk G connected hSix

/-- Transport the six-regular order-14 certificate to any labeling. -/
theorem hamiltonian_of_order14_six_regular
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : Fintype.card V = 14)
    (connected : G.Connected)
    (hSix : ∀ v : V, G.degree v = 6) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  let e : Fin 14 ≃ V := (Fintype.equivFinOfCardEq hcard).symm
  let G' : SimpleGraph (Fin 14) := G.comap e.toEmbedding
  let iso : G' ≃g G := SimpleGraph.Iso.comap e G
  letI : DecidableRel G'.Adj := fun u v => by
    change Decidable (G.Adj (e u) (e v))
    infer_instance
  have connected' : G'.Connected := iso.connected_iff.mpr connected
  have hSix' : ∀ v : Fin 14, G'.degree v = 6 := by
    intro v
    have hdeq : G'.degree v = G.degree (e v) := (iso.degree_eq v).symm
    rw [hdeq]
    exact hSix (e v)
  have hTrace' := hamiltonian_of_fin14_six_regular G' connected' hSix'
  rcases hTrace' with ⟨a, b, p, hp⟩
  exact ⟨e a, e b, p.map iso.toHom, hp.map iso.toHom e.bijective⟩

/-- Dirac-type half of the hard case: high minimum degree ⇒ Hamiltonian path. -/
theorem hamiltonian_of_minDegree_half
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hδ : Fintype.card V - 1 ≤ 2 * G.minDegree) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  have hTrace : Traceable G := traceable_of_minDegree_half G hδ
  exact hTrace

/-- Chvátal path condition ⇒ Hamiltonian path. -/
theorem hamiltonian_of_meetsChvatalPath
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hChv : MeetsChvatalPath G) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  have hTrace : Traceable G := traceable_of_chvatal G hChv
  exact hTrace

/-- Degrees are only 5 or 6, with exactly seven degree-6 vertices. -/
def IsDegreeClass6666666555555 (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  (∀ v : V, G.degree v = 6 ∨ G.degree v = 5) ∧
    Fintype.card {v : V // G.degree v = 6} = 7

/-- Five-regular on exactly 12 vertices. -/
def IsFiveRegular12 (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  Fintype.card V = 12 ∧ ∀ v : V, G.degree v = 5

/-- Six-regular on exactly 14 vertices. -/
def IsSixRegular14 (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  Fintype.card V = 14 ∧ ∀ v : V, G.degree v = 6

/-- If every degree is 5 or 6 then the degree-6 count determines the class. -/
theorem degree_eq_five_or_six_of_bounds (G : SimpleGraph V) [DecidableRel G.Adj]
    (hmin : 5 ≤ G.minDegree) (hmax : G.maxDegree ≤ 6) :
    ∀ v : V, G.degree v = 6 ∨ G.degree v = 5 := by
  intro v
  have hlo := (show 5 ≤ G.degree v from hmin.trans (G.minDegree_le_degree v))
  have hhi := G.degree_le_maxDegree v |>.trans hmax
  interval_cases h : G.degree v <;> omega

/--
With maximum degree ≤ 6, the Chvátal path condition is impossible for
`n ≥ 13`: the index `i = 6` has premise (every degree is ≤ 6) but conclusion
`d_{n-6} ≥ n-6 ≥ 7`, which exceeds the degree bound.
-/
theorem not_meetsChvatalPath_of_maxDegree_le_six_of_thirteen_le_card
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hmax : G.maxDegree ≤ 6) (hn : 13 ≤ Fintype.card V) :
    ¬ MeetsChvatalPath G := by
  classical
  intro hM
  let n := Fintype.card V
  have hi1 : 1 ≤ 6 := by omega
  have hi2 : 6 ≤ n / 2 := by omega
  have hall_le6 : ∀ v : V, G.degree v ≤ 6 := fun v =>
    (G.degree_le_maxDegree v).trans hmax
  have hprem : 6 ≤ card (univ.filter fun v : V => G.degree v ≤ 6) := by
    have heq : univ.filter (fun v : V => G.degree v ≤ 6) = univ := by
      ext v
      simp [hall_le6 v]
    have : 6 ≤ n := by omega
    simpa [heq, card_univ, n] using this
  have hcon := hM 6 hi1 (by simpa [n] using hi2) (by simpa [n] using hprem)
  -- hcon: 7 ≤ card {n - 6 ≤ deg}; but n - 6 ≥ 7 > 6 ≥ every degree
  have hempty : card (univ.filter fun v : V => n - 6 ≤ G.degree v) = 0 := by
    have hnone : ∀ v, v ∉ univ.filter fun v : V => n - 6 ≤ G.degree v := by
      intro v hv
      have hge : n - 6 ≤ G.degree v := (mem_filter.mp hv).2
      have hle : G.degree v ≤ 6 := hall_le6 v
      omega
    simpa using card_eq_zero.mpr (eq_empty_iff_forall_notMem.mpr hnone)
  have hcon' : 7 ≤ card (univ.filter fun v : V => n - 6 ≤ G.degree v) := by
    simpa [n] using hcon
  exact absurd hcon' (by omega)

/--
Remaining open case after Ore-half, Chvátal, residual-13, and five-regular-12.

Under `maxDegree ≤ 6`, Chvátal is impossible for `n ≥ 13`, so this branch is
exactly the finite exceptional degree classes (order 12 non-five-regular
non-Chvátal sequences, order-13 non-`6⁷5⁶`, six-regular-14, order-10, …).
-/
theorem hamiltonian_of_residue_eq_two_remaining
    (G : SimpleGraph V) [DecidableRel G.Adj] (connected : G.Connected)
    (_hResidue : residue G = 2)
    (hL : Ls G ≤ 6) (_hL2 : ¬ Ls G ≤ 2)
    (hNotHalf : ¬ Fintype.card V - 1 ≤ 2 * G.minDegree)
    (hNotChv : ¬ MeetsChvatalPath G)
    (hNotResidual13 : ¬ (Fintype.card V = 13 ∧ IsDegreeClass6666666555555 G))
    (hNotFive12 : ¬ IsFiveRegular12 G) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  have hMaxDeg : G.maxDegree ≤ 6 :=
    maxDegree_le_six_of_Ls_le_six G connected hL
  by_cases hn13 : 13 ≤ Fintype.card V
  · -- n ≥ 13: Chvátal is impossible under maxDegree ≤ 6 (see lemma above).
    have _hAuto :=
      not_meetsChvatalPath_of_maxDegree_le_six_of_thirteen_le_card G hMaxDeg hn13
    by_cases hcard13 : Fintype.card V = 13
    · -- Degree list is one of seven residue-2 sequences.
      set s :=
        (Finset.univ.val.map fun v : V => G.degree v).sort (· ≥ ·) with hs
      have hseq :
          s = [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] ∨
          s = [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 4] ∨
          s = [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 5, 5] ∨
          s = [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 4, 4] ∨
          s = [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 5, 5, 4] ∨
          s = [6, 6, 6, 6, 6, 6, 6, 6, 6, 5, 5, 5, 5] ∨
          s = [6, 6, 6, 6, 6, 6, 6, 5, 5, 5, 5, 5, 5] := by
        simpa [s, hs] using
          (degreeList_eq_allowed_of_card_eq_thirteen_of_residue_eq_two_of_maxDegree_le_six
            G hcard13 _hResidue hMaxDeg)
      have hmem (v : V) : G.degree v ∈ s := by
        have : G.degree v ∈
            Multiset.map (fun w : V => G.degree w) Finset.univ.val :=
          Multiset.mem_map.mpr ⟨v, by simp, rfl⟩
        simpa [s, hs] using (Multiset.mem_sort (· ≥ ·)).mpr this
      rcases hseq with hAll6 | hOther
      · -- 6-regular ⇒ Ore-half, contradicting `hNotHalf`.
        have hdeg : ∀ v : V, G.degree v = 6 := by
          intro v
          have hv : G.degree v ∈ s := hmem v
          rw [hAll6] at hv
          have hall : ∀ x ∈ ([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List ℕ),
              x = 6 := by decide
          exact hall _ hv
        have hmin6 : G.minDegree = 6 := by
          haveI : Nonempty V := Nontrivial.to_nonempty (α := V)
          obtain ⟨v, hv⟩ := G.exists_minimal_degree_vertex
          rw [hv, hdeg]
        have hOre : Fintype.card V - 1 ≤ 2 * G.minDegree := by
          rw [hcard13, hmin6]
        exact absurd hOre hNotHalf
      · -- Remaining six sequences: five mid sequences via path-closure;
        -- residual 6⁷5⁶ contradicts the residual-class exclusion.
        have hsort :
            (Finset.univ.val.map fun v : V => G.degree v).sort (· ≥ ·) = s := by
          simpa [s, hs]
        have hmin_of_list (L : List ℕ)
            (hL : s = L) (hall : ∀ x ∈ L, 4 ≤ x) : 4 ≤ G.minDegree := by
          haveI : Nonempty V := Nontrivial.to_nonempty (α := V)
          obtain ⟨v, hv⟩ := G.exists_minimal_degree_vertex
          have hvmem : G.degree v ∈ s := hmem v
          rw [hL] at hvmem
          have : G.minDegree = G.degree v := hv
          rw [this]
          exact hall _ hvmem
        have hmid (hlist : 9 ≤ List.count 6 s) (hmin4 : 4 ≤ G.minDegree) :
            ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
          have hS : 9 ≤ card (univ.filter fun v : V => G.degree v = 6) := by
            rw [card_filter_deg_eq_list_count G s hsort]
            exact hlist
          exact traceable_of_nine_deg_six_card_thirteen G hcard13 hMaxDeg hmin4 hS
        rcases hOther with h1264 | hRest
        · -- 12×6+4
          exact hmid (by rw [h1264]; decide)
            (hmin_of_list _ h1264 (by decide))
        · rcases hRest with h1125 | hRest
          · -- 11×6+2×5
            exact hmid (by rw [h1125]; decide)
              (hmin_of_list _ h1125 (by decide))
          · rcases hRest with h1124 | hRest
            · -- 11×6+2×4
              exact hmid (by rw [h1124]; decide)
                (hmin_of_list _ h1124 (by decide))
            · rcases hRest with h10254 | hRest
              · -- 10×6+2×5+4
                exact hmid (by rw [h10254]; decide)
                  (hmin_of_list _ h10254 (by decide))
              · rcases hRest with h964 | hRes13
                · -- 9×6+4×5
                  exact hmid (by rw [h964]; decide)
                    (hmin_of_list _ h964 (by decide))
                · -- 7×6+6×5 residual class
                  have hDeg : ∀ v : V, G.degree v = 6 ∨ G.degree v = 5 := by
                    intro v
                    have hv : G.degree v ∈ s := hmem v
                    rw [hRes13] at hv
                    have hall :
                        ∀ x ∈ ([6, 6, 6, 6, 6, 6, 6, 5, 5, 5, 5, 5, 5] : List ℕ),
                          x = 6 ∨ x = 5 := by decide
                    exact hall _ hv
                  have hSixCard : Fintype.card {v : V // G.degree v = 6} = 7 := by
                    classical
                    have hlist : List.count 6 s = 7 := by
                      rw [hRes13]; decide
                    have hcoe :
                        Multiset.map (fun v : V => G.degree v) Finset.univ.val =
                          (↑s : Multiset ℕ) := by
                      have h :=
                        Multiset.sort_eq
                          (Finset.univ.val.map fun v : V => G.degree v) (· ≥ ·)
                      simpa [s, hs] using h.symm
                    have hcnt :
                        (Multiset.map (fun v : V => G.degree v)
                            Finset.univ.val).count 6 = 7 := by
                      rw [hcoe, Multiset.coe_count, hlist]
                    have hmap := Multiset.count_map
                      (fun v : V => G.degree v) Finset.univ.val (b := 6)
                    rw [Fintype.card_subtype, ← hcnt, hmap]
                    simp [Finset.filter, Finset.card, eq_comm]
                  exact absurd ⟨hcard13, ⟨hDeg, hSixCard⟩⟩ hNotResidual13
    · by_cases hcard14 : Fintype.card V = 14
      · -- Force six-regularity; Hamiltonian path via Relabel14 certificate.
        have hSix :
            ∀ v : V, G.degree v = 6 :=
          six_regular_of_card_eq_fourteen_of_residue_eq_two_of_maxDegree_le_six
            G hcard14 _hResidue hMaxDeg
        exact hamiltonian_of_order14_six_regular G hcard14 connected hSix
      · -- n ≥ 15: impossible under residue=2 and maxDegree ≤ 6.
        have hle :
            Fintype.card V ≤ 14 :=
          card_le_fourteen_of_residue_eq_two_of_maxDegree_le_six
            G _hResidue hMaxDeg
        omega
  · -- n ≤ 12: stuck regulars + non-stuck high-set path-closure bulk.
    have hnle : Fintype.card V ≤ 12 := by omega
    have hNotFive :
        ¬ (Fintype.card V = 12 ∧ ∀ v : V, G.degree v = 5) := by
      intro h
      exact hNotFive12 ⟨h.1, h.2⟩
    exact hamiltonian_of_residue_eq_two_card_le_twelve G connected
      _hResidue hMaxDeg hnle hNotHalf hNotChv hNotFive

/-- Main entry under residue = 2 and Ls ≤ 6. -/
theorem hamiltonian_of_residue_eq_two_and_Ls_le_six
    (G : SimpleGraph V) [DecidableRel G.Adj] (connected : G.Connected)
    (hResidue : residue G = 2) (hL : Ls G ≤ 6) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  have _hMaxDeg : G.maxDegree ≤ 6 :=
    maxDegree_le_six_of_Ls_le_six G connected hL
  by_cases hL2 : Ls G ≤ 2
  · exact WOWII217SpanningTree.exists_hamiltonianPath_of_Ls_le_two G connected hL2
  · by_cases hHalf : Fintype.card V - 1 ≤ 2 * G.minDegree
    · exact hamiltonian_of_minDegree_half G hHalf
    · by_cases hChv : MeetsChvatalPath G
      · exact hamiltonian_of_meetsChvatalPath G hChv
      · by_cases hRes13 : Fintype.card V = 13 ∧ IsDegreeClass6666666555555 G
        · rcases hRes13 with ⟨hcard, hClass⟩
          exact hamiltonian_of_order13_degree_class G hcard connected hClass.2 hClass.1
        · by_cases hFive12 : IsFiveRegular12 G
          · rcases hFive12 with ⟨hcard, hFive⟩
            exact hamiltonian_of_order12_five_regular G hcard connected hFive
          · exact hamiltonian_of_residue_eq_two_remaining G connected hResidue hL hL2
              hHalf hChv hRes13 hFive12

end WOWII217Classification
