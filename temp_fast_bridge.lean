import WOWII217ClosureCertificateSemantics
import WOWII217Closure13Fast
import WOWII217Finite13ClosureRel

open SimpleGraph
open WOWII217FiniteBase WOWII217Closure WOWII217BondyChvatal WOWII217ClosureSemantics
open WOWII217Closure13Fast
open WOWII217Encoding13

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in

theorem test_rel_round (g : BitVec 78) :
    WOWII217Finite13ClosureRel.pathClosureParallelRel13 g (pathClosureParallelRound13 g) = true := by
  simp [WOWII217Finite13ClosureRel.pathClosureParallelRel13,
    pathClosureParallelRound13, pathClosureParallelMask13, upperPairs, upperIndex, setBit,
    adjUpper, BitVec.getLsbD, Bool.not]

