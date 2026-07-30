import WOWII217Finite13ClosureRel
import WOWII217Closure13Fast

#check WOWII217Finite13ClosureRel.pathClosureParallelRel13
#check pathClosureParallelRound13

example (g : BitVec 78) :
    WOWII217Finite13ClosureRel.pathClosureParallelRel13 g (pathClosureParallelRound13 g) = true := by
  simp [WOWII217Finite13ClosureRel.pathClosureParallelRel13,
    pathClosureParallelRound13, pathClosureParallelMask13, upperPairs, upperIndex, setBit,
    adjUpper, BitVec.getLsbD, Bool.not]
