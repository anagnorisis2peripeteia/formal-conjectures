import WOWII217Finite13ClosureSharedDeg
import WOWII217Finite13R0Perm
import WOWII217ClosureCertificateSemantics
import WOWII217ClosureSemantics

open WOWII217Finite13ClosureSharedDeg WOWII217FiniteBase WOWII217Closure WOWII217Finite13 WOWII217ClosureCertificateSemantics WOWII217ClosureSemantics

#eval (fixedDegreeSequenceUpper (n := 13) Counter13.g [6,6,6,6,6,6,6,5,5,5,5,5,5])
#eval (hasHighLowEdge13 Counter13.g)
#eval (connectedUpper (n := 13) Counter13.g)

#eval (degreeTableConsistent13 Counter13.g (degreeTableOfUpper13 Counter13.g))
#eval (pathClosureParallelRel13 Counter13.g (nextUpper13 Counter13.g) (degreeTableOfUpper13 Counter13.g))
#eval (pathClosureParallelRel13 (nextUpper13 Counter13.g) (nextUpper13 (nextUpper13 Counter13.g)) (degreeTableOfUpper13 (nextUpper13 Counter13.g)))
#eval (pathClosureParallelRel13 (nextUpper13 (nextUpper13 Counter13.g)) (nextUpper13 (nextUpper13 (nextUpper13 Counter13.g))) (degreeTableOfUpper13 (nextUpper13 (nextUpper13 Counter13.g))))
#eval (pathClosureParallelRel13 (nextUpper13 (nextUpper13 (nextUpper13 Counter13.g))) (nextUpper13 (nextUpper13 (nextUpper13 (nextUpper13 Counter13.g))) ) (degreeTableOfUpper13 (nextUpper13 (nextUpper13 (nextUpper13 Counter13.g))))
#eval (completeUpper (n := 13) (nextUpper13 (nextUpper13 (nextUpper13 (nextUpper13 Counter13.g)))))
