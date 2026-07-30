import Mathlib

structure BoolFive where
  b0 : Bool
  b1 : Bool
  b2 : Bool
  b3 : Bool
  b4 : Bool

def BoolFive.increment (x : BoolFive) (b : Bool) : BoolFive :=
  let c1 := x.b0 && b
  let c2 := x.b1 && c1
  let c3 := x.b2 && c2
  let c4 := x.b3 && c3
  { b0 := x.b0 ^^ b, b1 := x.b1 ^^ c1, b2 := x.b2 ^^ c2,
    b3 := x.b3 ^^ c3, b4 := x.b4 ^^ c4 }

def boolFiveValue (x : BoolFive) : Nat :=
  (if x.b0 then 1 else 0) +
    2 * (if x.b1 then 1 else 0) +
    4 * (if x.b2 then 1 else 0) +
    8 * (if x.b3 then 1 else 0) +
    16 * (if x.b4 then 1 else 0)

def bool5zero : BoolFive := { b0 := false,b1:=false,b2:=false,b3:=false,b4:=false }

def allones : BoolFive := { b0 := true,b1:=true,b2:=true,b3:=true,b4:=true }

#eval boolFiveValue bool5zero
#eval boolFiveValue allones
#eval boolFiveValue (BoolFive.increment allones true)
#eval boolFiveValue (BoolFive.increment allones true) = boolFiveValue allones + 1
