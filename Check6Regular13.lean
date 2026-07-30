import WOWII217BondyChvatal
import WOWII217SpanningTree

namespace Check6Regular13
open Classical SimpleGraph

theorem traceable_of_6regular_13 (G : SimpleGraph (Fin 13)) [DecidableRel G.Adj] (connected : G.Connected)
    (h6 : ∀ v, G.degree v = 6) : Traceable G := by
  sorry

end Check6Regular13
