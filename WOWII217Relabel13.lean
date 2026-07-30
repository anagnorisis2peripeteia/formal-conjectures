import WOWII217ClosureCertificateSemantics

/-! Relabelling the certified order-13 degree class back to arbitrary labels. -/

namespace WOWII217Relabel13

open SimpleGraph
open WOWII217BondyChvatal
open WOWII217ClosureCertificateSemantics

theorem exists_degreeSixFirstEquiv13
    (G : SimpleGraph (Fin 13)) [DecidableRel G.Adj]
    (degreeSixCount : Fintype.card {v : Fin 13 // G.degree v = 6} = 7)
    (degrees : ∀ v : Fin 13, G.degree v = 6 ∨ G.degree v = 5) :
    ∃ e : Fin 13 ≃ Fin 13, ∀ v : Fin 13,
      G.degree (e v) = if v.val < 7 then 6 else 5 := by
  classical
  let high : Set (Fin 13) := {v | G.degree v = 6}
  have highCard : Fintype.card high = 7 := by
    simpa [high] using degreeSixCount
  have lowCard : Fintype.card (highᶜ : Set (Fin 13)) = 6 := by
    rw [Fintype.card_compl_set, highCard]
    norm_num
  let highEquiv : high ≃ Fin 7 := Fintype.equivFinOfCardEq highCard
  let lowEquiv : (highᶜ : Set (Fin 13)) ≃ Fin 6 :=
    Fintype.equivFinOfCardEq lowCard
  let e : Fin 13 ≃ Fin 13 :=
    (@finSumFinEquiv 7 6).symm |>.trans
      (Equiv.sumCongr highEquiv.symm lowEquiv.symm) |>.trans
      (Equiv.Set.sumCompl high)
  refine ⟨e, ?_⟩
  intro v
  by_cases hv : v.val < 7
  · let i : Fin 7 := ⟨v, hv⟩
    have vi : v = Fin.castAdd 6 i := by
      apply Fin.ext
      rfl
    rw [vi]
    rw [if_pos (by change (i : Nat) < 7; exact i.isLt)]
    have eApply : e (Fin.castAdd 6 i) = (highEquiv.symm i : Fin 13) := by
      change (Equiv.Set.sumCompl high)
        ((Equiv.sumCongr highEquiv.symm lowEquiv.symm)
          ((@finSumFinEquiv 7 6).symm (Fin.castAdd 6 i))) =
        (highEquiv.symm i : Fin 13)
      rw [finSumFinEquiv_symm_apply_castAdd]
      rfl
    rw [eApply]
    exact (highEquiv.symm i).property
  · have hvLower : 7 ≤ v.val := Nat.le_of_not_gt hv
    let i : Fin 6 := ⟨v.val - 7, by omega⟩
    have vi : v = Fin.natAdd 7 i := by
      apply Fin.ext
      simp [i]
      omega
    rw [vi]
    simp only [Fin.val_natAdd]
    rw [if_neg (by omega)]
    have eApply : e (Fin.natAdd 7 i) = (lowEquiv.symm i : Fin 13) := by
      change (Equiv.Set.sumCompl high)
        ((Equiv.sumCongr highEquiv.symm lowEquiv.symm)
          ((@finSumFinEquiv 7 6).symm (Fin.natAdd 7 i))) =
        (lowEquiv.symm i : Fin 13)
      rw [finSumFinEquiv_symm_apply_natAdd]
      rfl
    rw [eApply]
    have notHigh : G.degree (lowEquiv.symm i : Fin 13) ≠ 6 := by
      intro degreeSix
      exact (lowEquiv.symm i).property (by simpa [high] using degreeSix)
    exact (degrees (lowEquiv.symm i)).resolve_left notHigh

theorem traceable_of_degreeSequence_6666666555555_up_to_equiv
    (G : SimpleGraph (Fin 13)) [DecidableRel G.Adj]
    (connected : G.Connected)
    (degreeOrder : ∃ e : Fin 13 ≃ Fin 13, ∀ v : Fin 13,
      G.degree (e v) = if v.val < 7 then 6 else 5) :
    Traceable G := by
  obtain ⟨e, degrees⟩ := degreeOrder
  let canonical : SimpleGraph (Fin 13) := G.comap e.toEmbedding
  let iso : canonical ≃g G := SimpleGraph.Iso.comap e G
  letI : DecidableRel canonical.Adj := fun u v => by
    change Decidable (G.Adj (e u) (e v))
    infer_instance
  have canonicalConnected : canonical.Connected :=
    iso.connected_iff.mpr connected
  have canonicalDegrees : ∀ v : Fin 13,
      canonical.degree v = if v.val < 7 then 6 else 5 := by
    intro v
    calc
      canonical.degree v = G.degree (e v) := (iso.degree_eq v).symm
      _ = if v.val < 7 then 6 else 5 := degrees v
  have certified : Traceable canonical :=
    traceable_of_connected_labeled_degreeSequence_6666666555555
      canonical canonicalConnected canonicalDegrees
  rcases certified with ⟨a, b, p, hp⟩
  refine ⟨e a, e b, p.map iso.toHom, ?_⟩
  exact hp.map iso.toHom e.bijective

theorem traceable_of_degreeCounts_6666666555555
    (G : SimpleGraph (Fin 13)) [DecidableRel G.Adj]
    (connected : G.Connected)
    (degreeSixCount : Fintype.card {v : Fin 13 // G.degree v = 6} = 7)
    (degrees : ∀ v : Fin 13, G.degree v = 6 ∨ G.degree v = 5) :
    Traceable G := by
  exact traceable_of_degreeSequence_6666666555555_up_to_equiv G connected
    (exists_degreeSixFirstEquiv13 G degreeSixCount degrees)

end WOWII217Relabel13
