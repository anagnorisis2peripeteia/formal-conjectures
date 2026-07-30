import WOWII217ClosureCertificateSemantics
import WOWII217Relabel13

open SimpleGraph
open WOWII217Relabel13

example
    (G : SimpleGraph (Fin 13)) [DecidableRel G.Adj]
    (labeledDegrees : ∀ v : Fin 13, G.degree v = if v.val < 7 then 6 else 5) :
    WOWII217Finite13.canonicalPermutationBlocksPattern13 (WOWII217Encoding.encodeUpper13 G) 0 = true := by
  simp [WOWII217Finite13.canonicalPermutationBlocksPattern13, WOWII217Encoding.encodeUpper13]
