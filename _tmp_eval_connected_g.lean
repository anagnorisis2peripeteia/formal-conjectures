import WOWII217Finite13ClosureSharedDeg
import Counter13

open WOWII217Finite13ClosureSharedDeg
open WOWII217FiniteBase

#eval (fixedDegreeSequenceUpper (n := 13) Counter13.g [6,6,6,6,6,6,6,5,5,5,5,5,5])
#eval (hasHighLowEdge13 Counter13.g)
#eval (canonicalPermutationBlocksPattern13 Counter13.g 0)
#eval (connectedUpper (n := 13) Counter13.g)
#eval (completeUpper (n := 13) (pathClosureParallelRounds13 (n := 13) 4 Counter13.g))
