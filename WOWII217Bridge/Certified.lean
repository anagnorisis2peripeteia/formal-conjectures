import WOWII217Encoding4
import WOWII217Connected4
import WOWII217Degree4
import WOWII217Encoding5
import WOWII217Connected5
import WOWII217Degree5
import WOWII217Encoding6
import WOWII217Connected6
import WOWII217Degree6
import WOWII217Encoding7
import WOWII217Connected7
import WOWII217Degree7
import WOWII217Encoding8
import WOWII217Connected8
import WOWII217Degree8
import WOWII217Encoding9
import WOWII217Connected9
import WOWII217Degree9
import WOWII217Encoding10
import WOWII217Connected10
import WOWII217Degree10
import WOWII217Encoding11
import WOWII217Connected11
import WOWII217Degree11
import WOWII217Encoding12
import WOWII217Connected12
import WOWII217Degree12
import WOWII217ClosureSemanticsSmall
import WOWII217ClosureBridge
import WOWII217BondyChvatal

namespace WOWII217Bridge

open SimpleGraph WOWII217FiniteBase WOWII217Closure WOWII217ClosureSemantics
open WOWII217BondyChvatal WOWII217ClosureSemanticsSmall WOWII217ClosureBridge
open WOWII217Encoding4 WOWII217Connected4 WOWII217Degree4
open WOWII217Encoding5 WOWII217Connected5 WOWII217Degree5
open WOWII217Encoding6 WOWII217Connected6 WOWII217Degree6
open WOWII217Encoding7 WOWII217Connected7 WOWII217Degree7
open WOWII217Encoding8 WOWII217Connected8 WOWII217Degree8
open WOWII217Encoding9 WOWII217Connected9 WOWII217Degree9
open WOWII217Encoding10 WOWII217Connected10 WOWII217Degree10
open WOWII217Encoding11 WOWII217Connected11 WOWII217Degree11
open WOWII217Encoding12 WOWII217Connected12 WOWII217Degree12

/-- Certified chain for n=4: chunk theorem + encoding + bridge -> `Traceable`. -/
theorem certified_4 (ds : List Nat) (H : SimpleGraph (Fin 4)) [DecidableRel H.Adj]
    (chunk : ∀ g : BitVec 6, connectedUpper (n := 4) g = true →
        fixedDegreeSequenceUpper (n := 4) g ds = true →
        completeUpper (n := 4) (pathClosureParallelRounds (n := 4) 4 g) = true)
    (conn : H.Connected)
    (degs : List.ofFn (fun v : Fin 4 => H.degree v) = ds) :
    Traceable H := by
  have hconn : connectedUpper (n := 4) (encodeUpper4 H) = true :=
    connectedUpper_of_connected_graphOfUpper4 _ (by rw [graphOfUpper_encodeUpper4]; exact conn)
  have hdeg : fixedDegreeSequenceUpper (n := 4) (encodeUpper4 H) ds = true :=
    fixedDegreeSequenceUpper_encodeUpper4_of_degreeSequence H _ degs
  have hbridge := Iff.mp
    (traceable_graphOfUpper_pathClosureParallelRounds_iff (by norm_num))
    (traceable_graphOfUpper_of_completeUpper4 _ (chunk (encodeUpper4 H) hconn hdeg))
  rwa [graphOfUpper_encodeUpper4] at hbridge

/-- Certified chain for n=5: chunk theorem + encoding + bridge -> `Traceable`. -/
theorem certified_5 (ds : List Nat) (H : SimpleGraph (Fin 5)) [DecidableRel H.Adj]
    (chunk : ∀ g : BitVec 10, connectedUpper (n := 5) g = true →
        fixedDegreeSequenceUpper (n := 5) g ds = true →
        completeUpper (n := 5) (pathClosureParallelRounds (n := 5) 4 g) = true)
    (conn : H.Connected)
    (degs : List.ofFn (fun v : Fin 5 => H.degree v) = ds) :
    Traceable H := by
  have hconn : connectedUpper (n := 5) (encodeUpper5 H) = true :=
    connectedUpper_of_connected_graphOfUpper5 _ (by rw [graphOfUpper_encodeUpper5]; exact conn)
  have hdeg : fixedDegreeSequenceUpper (n := 5) (encodeUpper5 H) ds = true :=
    fixedDegreeSequenceUpper_encodeUpper5_of_degreeSequence H _ degs
  have hbridge := Iff.mp
    (traceable_graphOfUpper_pathClosureParallelRounds_iff (by norm_num))
    (traceable_graphOfUpper_of_completeUpper5 _ (chunk (encodeUpper5 H) hconn hdeg))
  rwa [graphOfUpper_encodeUpper5] at hbridge

/-- Certified chain for n=6: chunk theorem + encoding + bridge -> `Traceable`. -/
theorem certified_6 (ds : List Nat) (H : SimpleGraph (Fin 6)) [DecidableRel H.Adj]
    (chunk : ∀ g : BitVec 15, connectedUpper (n := 6) g = true →
        fixedDegreeSequenceUpper (n := 6) g ds = true →
        completeUpper (n := 6) (pathClosureParallelRounds (n := 6) 4 g) = true)
    (conn : H.Connected)
    (degs : List.ofFn (fun v : Fin 6 => H.degree v) = ds) :
    Traceable H := by
  have hconn : connectedUpper (n := 6) (encodeUpper6 H) = true :=
    connectedUpper_of_connected_graphOfUpper6 _ (by rw [graphOfUpper_encodeUpper6]; exact conn)
  have hdeg : fixedDegreeSequenceUpper (n := 6) (encodeUpper6 H) ds = true :=
    fixedDegreeSequenceUpper_encodeUpper6_of_degreeSequence H _ degs
  have hbridge := Iff.mp
    (traceable_graphOfUpper_pathClosureParallelRounds_iff (by norm_num))
    (traceable_graphOfUpper_of_completeUpper6 _ (chunk (encodeUpper6 H) hconn hdeg))
  rwa [graphOfUpper_encodeUpper6] at hbridge

/-- Certified chain for n=7: chunk theorem + encoding + bridge -> `Traceable`. -/
theorem certified_7 (ds : List Nat) (H : SimpleGraph (Fin 7)) [DecidableRel H.Adj]
    (chunk : ∀ g : BitVec 21, connectedUpper (n := 7) g = true →
        fixedDegreeSequenceUpper (n := 7) g ds = true →
        completeUpper (n := 7) (pathClosureParallelRounds (n := 7) 4 g) = true)
    (conn : H.Connected)
    (degs : List.ofFn (fun v : Fin 7 => H.degree v) = ds) :
    Traceable H := by
  have hconn : connectedUpper (n := 7) (encodeUpper7 H) = true :=
    connectedUpper_of_connected_graphOfUpper7 _ (by rw [graphOfUpper_encodeUpper7]; exact conn)
  have hdeg : fixedDegreeSequenceUpper (n := 7) (encodeUpper7 H) ds = true :=
    fixedDegreeSequenceUpper_encodeUpper7_of_degreeSequence H _ degs
  have hbridge := Iff.mp
    (traceable_graphOfUpper_pathClosureParallelRounds_iff (by norm_num))
    (traceable_graphOfUpper_of_completeUpper7 _ (chunk (encodeUpper7 H) hconn hdeg))
  rwa [graphOfUpper_encodeUpper7] at hbridge

/-- Certified chain for n=8: chunk theorem + encoding + bridge -> `Traceable`. -/
theorem certified_8 (ds : List Nat) (H : SimpleGraph (Fin 8)) [DecidableRel H.Adj]
    (chunk : ∀ g : BitVec 28, connectedUpper (n := 8) g = true →
        fixedDegreeSequenceUpper (n := 8) g ds = true →
        completeUpper (n := 8) (pathClosureParallelRounds (n := 8) 4 g) = true)
    (conn : H.Connected)
    (degs : List.ofFn (fun v : Fin 8 => H.degree v) = ds) :
    Traceable H := by
  have hconn : connectedUpper (n := 8) (encodeUpper8 H) = true :=
    connectedUpper_of_connected_graphOfUpper8 _ (by rw [graphOfUpper_encodeUpper8]; exact conn)
  have hdeg : fixedDegreeSequenceUpper (n := 8) (encodeUpper8 H) ds = true :=
    fixedDegreeSequenceUpper_encodeUpper8_of_degreeSequence H _ degs
  have hbridge := Iff.mp
    (traceable_graphOfUpper_pathClosureParallelRounds_iff (by norm_num))
    (traceable_graphOfUpper_of_completeUpper8 _ (chunk (encodeUpper8 H) hconn hdeg))
  rwa [graphOfUpper_encodeUpper8] at hbridge

/-- Certified chain for n=9: chunk theorem + encoding + bridge -> `Traceable`. -/
theorem certified_9 (ds : List Nat) (H : SimpleGraph (Fin 9)) [DecidableRel H.Adj]
    (chunk : ∀ g : BitVec 36, connectedUpper (n := 9) g = true →
        fixedDegreeSequenceUpper (n := 9) g ds = true →
        completeUpper (n := 9) (pathClosureParallelRounds (n := 9) 4 g) = true)
    (conn : H.Connected)
    (degs : List.ofFn (fun v : Fin 9 => H.degree v) = ds) :
    Traceable H := by
  have hconn : connectedUpper (n := 9) (encodeUpper9 H) = true :=
    connectedUpper_of_connected_graphOfUpper9 _ (by rw [graphOfUpper_encodeUpper9]; exact conn)
  have hdeg : fixedDegreeSequenceUpper (n := 9) (encodeUpper9 H) ds = true :=
    fixedDegreeSequenceUpper_encodeUpper9_of_degreeSequence H _ degs
  have hbridge := Iff.mp
    (traceable_graphOfUpper_pathClosureParallelRounds_iff (by norm_num))
    (traceable_graphOfUpper_of_completeUpper9 _ (chunk (encodeUpper9 H) hconn hdeg))
  rwa [graphOfUpper_encodeUpper9] at hbridge

/-- Certified chain for n=10: chunk theorem + encoding + bridge -> `Traceable`. -/
theorem certified_10 (ds : List Nat) (H : SimpleGraph (Fin 10)) [DecidableRel H.Adj]
    (chunk : ∀ g : BitVec 45, connectedUpper (n := 10) g = true →
        fixedDegreeSequenceUpper (n := 10) g ds = true →
        completeUpper (n := 10) (pathClosureParallelRounds (n := 10) 4 g) = true)
    (conn : H.Connected)
    (degs : List.ofFn (fun v : Fin 10 => H.degree v) = ds) :
    Traceable H := by
  have hconn : connectedUpper (n := 10) (encodeUpper10 H) = true :=
    connectedUpper_of_connected_graphOfUpper10 _ (by rw [graphOfUpper_encodeUpper10]; exact conn)
  have hdeg : fixedDegreeSequenceUpper (n := 10) (encodeUpper10 H) ds = true :=
    fixedDegreeSequenceUpper_encodeUpper10_of_degreeSequence H _ degs
  have hbridge := Iff.mp
    (traceable_graphOfUpper_pathClosureParallelRounds_iff (by norm_num))
    (traceable_graphOfUpper_of_completeUpper10 _ (chunk (encodeUpper10 H) hconn hdeg))
  rwa [graphOfUpper_encodeUpper10] at hbridge

/-- Certified chain for n=11: chunk theorem + encoding + bridge -> `Traceable`. -/
theorem certified_11 (ds : List Nat) (H : SimpleGraph (Fin 11)) [DecidableRel H.Adj]
    (chunk : ∀ g : BitVec 55, connectedUpper (n := 11) g = true →
        fixedDegreeSequenceUpper (n := 11) g ds = true →
        completeUpper (n := 11) (pathClosureParallelRounds (n := 11) 4 g) = true)
    (conn : H.Connected)
    (degs : List.ofFn (fun v : Fin 11 => H.degree v) = ds) :
    Traceable H := by
  have hconn : connectedUpper (n := 11) (encodeUpper11 H) = true :=
    connectedUpper_of_connected_graphOfUpper11 _ (by rw [graphOfUpper_encodeUpper11]; exact conn)
  have hdeg : fixedDegreeSequenceUpper (n := 11) (encodeUpper11 H) ds = true :=
    fixedDegreeSequenceUpper_encodeUpper11_of_degreeSequence H _ degs
  have hbridge := Iff.mp
    (traceable_graphOfUpper_pathClosureParallelRounds_iff (by norm_num))
    (traceable_graphOfUpper_of_completeUpper11 _ (chunk (encodeUpper11 H) hconn hdeg))
  rwa [graphOfUpper_encodeUpper11] at hbridge

/-- Certified chain for n=12: chunk theorem + encoding + bridge -> `Traceable`. -/
theorem certified_12 (ds : List Nat) (H : SimpleGraph (Fin 12)) [DecidableRel H.Adj]
    (chunk : ∀ g : BitVec 66, connectedUpper (n := 12) g = true →
        fixedDegreeSequenceUpper (n := 12) g ds = true →
        completeUpper (n := 12) (pathClosureParallelRounds (n := 12) 4 g) = true)
    (conn : H.Connected)
    (degs : List.ofFn (fun v : Fin 12 => H.degree v) = ds) :
    Traceable H := by
  have hconn : connectedUpper (n := 12) (encodeUpper12 H) = true :=
    connectedUpper_of_connected_graphOfUpper12 _ (by rw [graphOfUpper_encodeUpper12]; exact conn)
  have hdeg : fixedDegreeSequenceUpper (n := 12) (encodeUpper12 H) ds = true :=
    fixedDegreeSequenceUpper_encodeUpper12_of_degreeSequence H _ degs
  have hbridge := Iff.mp
    (traceable_graphOfUpper_pathClosureParallelRounds_iff (by norm_num))
    (traceable_graphOfUpper_of_completeUpper12 _ (chunk (encodeUpper12 H) hconn hdeg))
  rwa [graphOfUpper_encodeUpper12] at hbridge

end WOWII217Bridge
