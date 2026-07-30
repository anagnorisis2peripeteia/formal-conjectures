import WOWII217Finite13ClosureRelSymHighLowSharedDeg
import WOWII217Encoding13
import WOWII217Finite13

open WOWII217FiniteBase WOWII217Closure WOWII217Finite13ClosureRelSymHighLowSharedDeg WOWII217Finite13 WOWII217Encoding13

-- copy graph from Counter13

def isHighComp : Fin 13 → Bool := fun v =>
  if v.1 = 0 || v.1 = 1 || v.1 = 2 || v.1 = 3 || v.1 = 4 || v.1 = 5 || v.1 = 7 then true else false

def G : SimpleGraph (Fin 13) where
  Adj u v :=
    if h : u = v then False else
      ((u.1 = 0 || u.1 = 1 || u.1 = 2 || u.1 = 3 || u.1 = 4 || u.1 = 5 || u.1 = 7) &&
       (v.1 = 0 || v.1 = 1 || v.1 = 2 || v.1 = 3 || v.1 = 4 || v.1 = 5 || v.1 = 7)) ||
      ((u.1 = 6 || u.1 = 8 || u.1 = 9 || u.1 = 10 || u.1 = 11 || u.1 = 12) &&
       (v.1 = 6 || v.1 = 8 || v.1 = 9 || v.1 = 10 || v.1 = 11 || v.1 = 12)

 def g : BitVec 78 := encodeUpper13 G

#eval hasHighLowEdge13 g
#eval fixedDegreeSequenceUpper (n := 13) g [6, 6, 6, 6, 6, 6, 6, 5, 5, 5, 5, 5, 5]
#eval canonicalPermutationBlocksPattern13 g 0
#eval connectedUpper (n := 13) g
#eval degreeTableConsistent13 g (extractDegreesUpper13 g)
#eval pathClosureParallelRel13 g g (extractDegreesUpper13 g)
