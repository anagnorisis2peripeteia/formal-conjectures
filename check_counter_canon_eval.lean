import Counter13
import WOWII217Finite13ClosureSharedDeg

open WOWII217Finite13ClosureSharedDeg WOWII217Finite13

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000000 in
#eval hasHighLowEdge13 Counter13.g
#eval fixedDegreeSequenceUpper (n := 13) Counter13.g
  [6,6,6,6,6,6,6,5,5,5,5,5,5]
#eval canonicalPermutationBlocksPattern13 Counter13.g 0
#eval connectedUpper (n := 13) Counter13.g
