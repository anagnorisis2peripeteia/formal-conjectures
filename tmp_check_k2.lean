import FormalConjectures.WrittenOnTheWallII.GraphConjecture72

open SimpleGraph
open WrittenOnTheWallII.GraphConjecture72
open WrittenOnTheWallII.GraphConjecture101

def G : SimpleGraph (Fin 2) := completeGraph (Fin 2)

#eval matchingNumber G
#eval maxEvenDistance G
#eval (alphaCore G).card
