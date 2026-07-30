import WOWII217ClosureSemantics
import WOWII217Closure
import WOWII217ClosureSemanticsSmall
import WOWII217BondyChvatal

namespace WOWII217ClosureBridge

open SimpleGraph WOWII217FiniteBase WOWII217Closure WOWII217ClosureSemantics WOWII217ClosureSemanticsSmall
open WOWII217BondyChvatal

theorem traceable_graphOfUpper_pathClosureParallelRounds_iff {n : Nat} (hn : n < 16 := by norm_num)
    {rounds : Nat} {g : BitVec (edgeCount n)} :
    Traceable (graphOfUpper (pathClosureParallelRounds (n := n) rounds g)) ↔
    Traceable (graphOfUpper (n := n) g) := by
  sorry

end WOWII217ClosureBridge
