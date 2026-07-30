import WOWII217ClosureCertificateSemantics
import WOWII217Relabel13
import Mathlib

open SimpleGraph
open WOWII217Relabel13

namespace Scratch

example (G : SimpleGraph (Fin 13)) [DecidableRel G.Adj]
    (labeled : ∀ v : Fin 13, G.degree v = if v.1 < 7 then 6 else 5) :
    ∀ v : Fin 13, G.degree v = 6 ∨ G.degree v = 5 := by
  intro v
  by_cases hv : v.1 < 7
  · left; simpa [labeled, hv]
  · right; simpa [labeled, hv]

example (G : SimpleGraph (Fin 13)) [DecidableRel G.Adj]
    (labeled : ∀ v : Fin 13, G.degree v = if v.1 < 7 then 6 else 5) :
    Fintype.card {v : Fin 13 // G.degree v = 6} = 7 := by
  let e : {v : Fin 13 // v.1 < 7} ≃ {v : Fin 13 // G.degree v = 6} :=
    { toFun := fun v => ⟨v, by simpa [labeled, v.2] using labeled v.1⟩,
      invFun := fun v =>
        let hlt : v.1.1 < 7 := by
          by_cases hv : v.1.1 < 7
          · exact hv
          · exfalso
            have hd5 : G.degree v.1 = 5 := by simpa [labeled, hv] using labeled v.1
            omega
        ⟨v.1, hlt⟩,
      left_inv := by
        intro v
        rfl,
      right_inv := by
        intro v
        simp [labeled] }
  calc
    Fintype.card {v : Fin 13 // G.degree v = 6}
        = Fintype.card {v : Fin 13 // v.1 < 7} := Fintype.card_congr e
    _ = 7 := by native_decide

end Scratch
