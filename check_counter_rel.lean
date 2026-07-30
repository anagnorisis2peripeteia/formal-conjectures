import WOWII217Finite13ClosureSharedDeg

open WOWII217Finite13ClosureSharedDeg WOWII217ClosureSemantics WOWII217FiniteBase WOWII217Finite13

#eval (connectedUpper (n := 13) Counter13.g)
#eval (hasHighLowEdge13 Counter13.g)
#eval (fixedDegreeSequenceUpper (n := 13) Counter13.g [6,6,6,6,6,6,6,5,5,5,5,5,5])
#eval (pathClosureParallelRel13 Counter13.g (nextUpper13 Counter13.g) (degreeTableOfUpper13 Counter13.g))
#eval (pathClosureParallelRel13 (nextUpper13 Counter13.g) (nextUpper13 (nextUpper13 Counter13.g)) (degreeTableOfUpper13 (nextUpper13 Counter13.g)))
#eval (pathClosureParallelRel13 (nextUpper13 (nextUpper13 Counter13.g)) (nextUpper13 (nextUpper13 (nextUpper13 Counter13.g))) (degreeTableOfUpper13 (nextUpper13 (nextUpper13 Counter13.g))))
#eval (pathClosureParallelRel13 (nextUpper13 (nextUpper13 (nextUpper13 Counter13.g))) (nextUpper13 (nextUpper13 (nextUpper13 (nextUpper13 Counter13.g)))) (degreeTableOfUpper13 (nextUpper13 (nextUpper13 (nextUpper13 Counter13.g))))
#eval (completeUpper (n := 13) (nextUpper13 (nextUpper13 (nextUpper13 (nextUpper13 Counter13.g)))) )
#eval (WOWII217Finite13ClosureRelSymHighLowSharedDeg.pathClosureParallelRel13 Counter13.g (nextUpper13 Counter13.g) (degreeTableOfUpper13 Counter13.g))
