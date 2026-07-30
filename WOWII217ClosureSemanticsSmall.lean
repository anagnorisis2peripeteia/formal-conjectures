/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import WOWII217ClosureSemantics
import WOWII217FiniteBase
import WOWII217Closure
import WOWII217BondyChvatal

open SimpleGraph WOWII217FiniteBase WOWII217Closure WOWII217ClosureSemantics WOWII217BondyChvatal

namespace WOWII217ClosureSemanticsSmall

def completeWalk4 :
    (⊤ : SimpleGraph (Fin 4)).Walk (0 : Fin 4) (3 : Fin 4) :=
  .cons (show (⊤ : SimpleGraph (Fin 4)).Adj 0 1 by simp) <|
  .cons (show (⊤ : SimpleGraph (Fin 4)).Adj 1 2 by simp) <|
  .cons (show (⊤ : SimpleGraph (Fin 4)).Adj 2 3 by simp) <|
  .nil

theorem completeWalk4_isHamiltonian : completeWalk4.IsHamiltonian := by
  intro v
  fin_cases v <;> simp [completeWalk4]

theorem traceable_top4 : Traceable (⊤ : SimpleGraph (Fin 4)) :=
  ⟨0, 3, completeWalk4, completeWalk4_isHamiltonian⟩

theorem adjUpper_true_of_completeUpper4 (g : BitVec 6)
    (complete : completeUpper (n := 4) g = true)
    {u v : Nat} (huv : u < v) (hv : v < 4) :
    adjUpper (n := 4) g u v = true := by
  rw [completeUpper] at complete
  exact (List.all_eq_true.mp complete) (u, v)
    (mem_upperPairs_iff.mpr ⟨hv, huv⟩)

theorem graphOfUpper_eq_top_of_completeUpper4 (g : BitVec 6)
    (complete : completeUpper (n := 4) g = true) :
    graphOfUpper (n := 4) g = ⊤ := by
  ext x y
  change adjUpper (n := 4) g x y = true ↔
    (⊤ : SimpleGraph (Fin 4)).Adj x y
  rw [SimpleGraph.top_adj]
  constructor
  · intro adjacent hxy
    subst y
    simp [adjUpper] at adjacent
  · intro hxy
    have hvalne : x.val ≠ y.val := fun h => hxy (Fin.ext h)
    by_cases hlt : x.val < y.val
    · exact adjUpper_true_of_completeUpper4 g complete hlt y.isLt
    · have hyx : y.val < x.val := by omega
      rw [adjUpper_comm (n := 4) g x y]
      exact adjUpper_true_of_completeUpper4 g complete hyx x.isLt

theorem traceable_graphOfUpper_of_completeUpper4 (g : BitVec 6)
    (complete : completeUpper (n := 4) g = true) :
    Traceable (graphOfUpper (n := 4) g) := by
  rw [graphOfUpper_eq_top_of_completeUpper4 g complete]
  exact traceable_top4

def completeWalk5 :
    (⊤ : SimpleGraph (Fin 5)).Walk (0 : Fin 5) (4 : Fin 5) :=
  .cons (show (⊤ : SimpleGraph (Fin 5)).Adj 0 1 by simp) <|
  .cons (show (⊤ : SimpleGraph (Fin 5)).Adj 1 2 by simp) <|
  .cons (show (⊤ : SimpleGraph (Fin 5)).Adj 2 3 by simp) <|
  .cons (show (⊤ : SimpleGraph (Fin 5)).Adj 3 4 by simp) <|
  .nil

theorem completeWalk5_isHamiltonian : completeWalk5.IsHamiltonian := by
  intro v
  fin_cases v <;> simp [completeWalk5]

theorem traceable_top5 : Traceable (⊤ : SimpleGraph (Fin 5)) :=
  ⟨0, 4, completeWalk5, completeWalk5_isHamiltonian⟩

theorem adjUpper_true_of_completeUpper5 (g : BitVec 10)
    (complete : completeUpper (n := 5) g = true)
    {u v : Nat} (huv : u < v) (hv : v < 5) :
    adjUpper (n := 5) g u v = true := by
  rw [completeUpper] at complete
  exact (List.all_eq_true.mp complete) (u, v)
    (mem_upperPairs_iff.mpr ⟨hv, huv⟩)

theorem graphOfUpper_eq_top_of_completeUpper5 (g : BitVec 10)
    (complete : completeUpper (n := 5) g = true) :
    graphOfUpper (n := 5) g = ⊤ := by
  ext x y
  change adjUpper (n := 5) g x y = true ↔
    (⊤ : SimpleGraph (Fin 5)).Adj x y
  rw [SimpleGraph.top_adj]
  constructor
  · intro adjacent hxy
    subst y
    simp [adjUpper] at adjacent
  · intro hxy
    have hvalne : x.val ≠ y.val := fun h => hxy (Fin.ext h)
    by_cases hlt : x.val < y.val
    · exact adjUpper_true_of_completeUpper5 g complete hlt y.isLt
    · have hyx : y.val < x.val := by omega
      rw [adjUpper_comm (n := 5) g x y]
      exact adjUpper_true_of_completeUpper5 g complete hyx x.isLt

theorem traceable_graphOfUpper_of_completeUpper5 (g : BitVec 10)
    (complete : completeUpper (n := 5) g = true) :
    Traceable (graphOfUpper (n := 5) g) := by
  rw [graphOfUpper_eq_top_of_completeUpper5 g complete]
  exact traceable_top5

def completeWalk6 :
    (⊤ : SimpleGraph (Fin 6)).Walk (0 : Fin 6) (5 : Fin 6) :=
  .cons (show (⊤ : SimpleGraph (Fin 6)).Adj 0 1 by simp) <|
  .cons (show (⊤ : SimpleGraph (Fin 6)).Adj 1 2 by simp) <|
  .cons (show (⊤ : SimpleGraph (Fin 6)).Adj 2 3 by simp) <|
  .cons (show (⊤ : SimpleGraph (Fin 6)).Adj 3 4 by simp) <|
  .cons (show (⊤ : SimpleGraph (Fin 6)).Adj 4 5 by simp) <|
  .nil

theorem completeWalk6_isHamiltonian : completeWalk6.IsHamiltonian := by
  intro v
  fin_cases v <;> simp [completeWalk6]

theorem traceable_top6 : Traceable (⊤ : SimpleGraph (Fin 6)) :=
  ⟨0, 5, completeWalk6, completeWalk6_isHamiltonian⟩

theorem adjUpper_true_of_completeUpper6 (g : BitVec 15)
    (complete : completeUpper (n := 6) g = true)
    {u v : Nat} (huv : u < v) (hv : v < 6) :
    adjUpper (n := 6) g u v = true := by
  rw [completeUpper] at complete
  exact (List.all_eq_true.mp complete) (u, v)
    (mem_upperPairs_iff.mpr ⟨hv, huv⟩)

theorem graphOfUpper_eq_top_of_completeUpper6 (g : BitVec 15)
    (complete : completeUpper (n := 6) g = true) :
    graphOfUpper (n := 6) g = ⊤ := by
  ext x y
  change adjUpper (n := 6) g x y = true ↔
    (⊤ : SimpleGraph (Fin 6)).Adj x y
  rw [SimpleGraph.top_adj]
  constructor
  · intro adjacent hxy
    subst y
    simp [adjUpper] at adjacent
  · intro hxy
    have hvalne : x.val ≠ y.val := fun h => hxy (Fin.ext h)
    by_cases hlt : x.val < y.val
    · exact adjUpper_true_of_completeUpper6 g complete hlt y.isLt
    · have hyx : y.val < x.val := by omega
      rw [adjUpper_comm (n := 6) g x y]
      exact adjUpper_true_of_completeUpper6 g complete hyx x.isLt

theorem traceable_graphOfUpper_of_completeUpper6 (g : BitVec 15)
    (complete : completeUpper (n := 6) g = true) :
    Traceable (graphOfUpper (n := 6) g) := by
  rw [graphOfUpper_eq_top_of_completeUpper6 g complete]
  exact traceable_top6

def completeWalk7 :
    (⊤ : SimpleGraph (Fin 7)).Walk (0 : Fin 7) (6 : Fin 7) :=
  .cons (show (⊤ : SimpleGraph (Fin 7)).Adj 0 1 by simp) <|
  .cons (show (⊤ : SimpleGraph (Fin 7)).Adj 1 2 by simp) <|
  .cons (show (⊤ : SimpleGraph (Fin 7)).Adj 2 3 by simp) <|
  .cons (show (⊤ : SimpleGraph (Fin 7)).Adj 3 4 by simp) <|
  .cons (show (⊤ : SimpleGraph (Fin 7)).Adj 4 5 by simp) <|
  .cons (show (⊤ : SimpleGraph (Fin 7)).Adj 5 6 by simp) <|
  .nil

theorem completeWalk7_isHamiltonian : completeWalk7.IsHamiltonian := by
  intro v
  fin_cases v <;> simp [completeWalk7]

theorem traceable_top7 : Traceable (⊤ : SimpleGraph (Fin 7)) :=
  ⟨0, 6, completeWalk7, completeWalk7_isHamiltonian⟩

theorem adjUpper_true_of_completeUpper7 (g : BitVec 21)
    (complete : completeUpper (n := 7) g = true)
    {u v : Nat} (huv : u < v) (hv : v < 7) :
    adjUpper (n := 7) g u v = true := by
  rw [completeUpper] at complete
  exact (List.all_eq_true.mp complete) (u, v)
    (mem_upperPairs_iff.mpr ⟨hv, huv⟩)

theorem graphOfUpper_eq_top_of_completeUpper7 (g : BitVec 21)
    (complete : completeUpper (n := 7) g = true) :
    graphOfUpper (n := 7) g = ⊤ := by
  ext x y
  change adjUpper (n := 7) g x y = true ↔
    (⊤ : SimpleGraph (Fin 7)).Adj x y
  rw [SimpleGraph.top_adj]
  constructor
  · intro adjacent hxy
    subst y
    simp [adjUpper] at adjacent
  · intro hxy
    have hvalne : x.val ≠ y.val := fun h => hxy (Fin.ext h)
    by_cases hlt : x.val < y.val
    · exact adjUpper_true_of_completeUpper7 g complete hlt y.isLt
    · have hyx : y.val < x.val := by omega
      rw [adjUpper_comm (n := 7) g x y]
      exact adjUpper_true_of_completeUpper7 g complete hyx x.isLt

theorem traceable_graphOfUpper_of_completeUpper7 (g : BitVec 21)
    (complete : completeUpper (n := 7) g = true) :
    Traceable (graphOfUpper (n := 7) g) := by
  rw [graphOfUpper_eq_top_of_completeUpper7 g complete]
  exact traceable_top7

def completeWalk8 :
    (⊤ : SimpleGraph (Fin 8)).Walk (0 : Fin 8) (7 : Fin 8) :=
  .cons (show (⊤ : SimpleGraph (Fin 8)).Adj 0 1 by simp) <|
  .cons (show (⊤ : SimpleGraph (Fin 8)).Adj 1 2 by simp) <|
  .cons (show (⊤ : SimpleGraph (Fin 8)).Adj 2 3 by simp) <|
  .cons (show (⊤ : SimpleGraph (Fin 8)).Adj 3 4 by simp) <|
  .cons (show (⊤ : SimpleGraph (Fin 8)).Adj 4 5 by simp) <|
  .cons (show (⊤ : SimpleGraph (Fin 8)).Adj 5 6 by simp) <|
  .cons (show (⊤ : SimpleGraph (Fin 8)).Adj 6 7 by simp) <|
  .nil

theorem completeWalk8_isHamiltonian : completeWalk8.IsHamiltonian := by
  intro v
  fin_cases v <;> simp [completeWalk8]

theorem traceable_top8 : Traceable (⊤ : SimpleGraph (Fin 8)) :=
  ⟨0, 7, completeWalk8, completeWalk8_isHamiltonian⟩

theorem adjUpper_true_of_completeUpper8 (g : BitVec 28)
    (complete : completeUpper (n := 8) g = true)
    {u v : Nat} (huv : u < v) (hv : v < 8) :
    adjUpper (n := 8) g u v = true := by
  rw [completeUpper] at complete
  exact (List.all_eq_true.mp complete) (u, v)
    (mem_upperPairs_iff.mpr ⟨hv, huv⟩)

theorem graphOfUpper_eq_top_of_completeUpper8 (g : BitVec 28)
    (complete : completeUpper (n := 8) g = true) :
    graphOfUpper (n := 8) g = ⊤ := by
  ext x y
  change adjUpper (n := 8) g x y = true ↔
    (⊤ : SimpleGraph (Fin 8)).Adj x y
  rw [SimpleGraph.top_adj]
  constructor
  · intro adjacent hxy
    subst y
    simp [adjUpper] at adjacent
  · intro hxy
    have hvalne : x.val ≠ y.val := fun h => hxy (Fin.ext h)
    by_cases hlt : x.val < y.val
    · exact adjUpper_true_of_completeUpper8 g complete hlt y.isLt
    · have hyx : y.val < x.val := by omega
      rw [adjUpper_comm (n := 8) g x y]
      exact adjUpper_true_of_completeUpper8 g complete hyx x.isLt

theorem traceable_graphOfUpper_of_completeUpper8 (g : BitVec 28)
    (complete : completeUpper (n := 8) g = true) :
    Traceable (graphOfUpper (n := 8) g) := by
  rw [graphOfUpper_eq_top_of_completeUpper8 g complete]
  exact traceable_top8

def completeWalk9 :
    (⊤ : SimpleGraph (Fin 9)).Walk (0 : Fin 9) (8 : Fin 9) :=
  .cons (show (⊤ : SimpleGraph (Fin 9)).Adj 0 1 by simp) <|
  .cons (show (⊤ : SimpleGraph (Fin 9)).Adj 1 2 by simp) <|
  .cons (show (⊤ : SimpleGraph (Fin 9)).Adj 2 3 by simp) <|
  .cons (show (⊤ : SimpleGraph (Fin 9)).Adj 3 4 by simp) <|
  .cons (show (⊤ : SimpleGraph (Fin 9)).Adj 4 5 by simp) <|
  .cons (show (⊤ : SimpleGraph (Fin 9)).Adj 5 6 by simp) <|
  .cons (show (⊤ : SimpleGraph (Fin 9)).Adj 6 7 by simp) <|
  .cons (show (⊤ : SimpleGraph (Fin 9)).Adj 7 8 by simp) <|
  .nil

theorem completeWalk9_isHamiltonian : completeWalk9.IsHamiltonian := by
  intro v
  fin_cases v <;> simp [completeWalk9]

theorem traceable_top9 : Traceable (⊤ : SimpleGraph (Fin 9)) :=
  ⟨0, 8, completeWalk9, completeWalk9_isHamiltonian⟩

theorem adjUpper_true_of_completeUpper9 (g : BitVec 36)
    (complete : completeUpper (n := 9) g = true)
    {u v : Nat} (huv : u < v) (hv : v < 9) :
    adjUpper (n := 9) g u v = true := by
  rw [completeUpper] at complete
  exact (List.all_eq_true.mp complete) (u, v)
    (mem_upperPairs_iff.mpr ⟨hv, huv⟩)

theorem graphOfUpper_eq_top_of_completeUpper9 (g : BitVec 36)
    (complete : completeUpper (n := 9) g = true) :
    graphOfUpper (n := 9) g = ⊤ := by
  ext x y
  change adjUpper (n := 9) g x y = true ↔
    (⊤ : SimpleGraph (Fin 9)).Adj x y
  rw [SimpleGraph.top_adj]
  constructor
  · intro adjacent hxy
    subst y
    simp [adjUpper] at adjacent
  · intro hxy
    have hvalne : x.val ≠ y.val := fun h => hxy (Fin.ext h)
    by_cases hlt : x.val < y.val
    · exact adjUpper_true_of_completeUpper9 g complete hlt y.isLt
    · have hyx : y.val < x.val := by omega
      rw [adjUpper_comm (n := 9) g x y]
      exact adjUpper_true_of_completeUpper9 g complete hyx x.isLt

theorem traceable_graphOfUpper_of_completeUpper9 (g : BitVec 36)
    (complete : completeUpper (n := 9) g = true) :
    Traceable (graphOfUpper (n := 9) g) := by
  rw [graphOfUpper_eq_top_of_completeUpper9 g complete]
  exact traceable_top9

def completeWalk10 :
    (⊤ : SimpleGraph (Fin 10)).Walk (0 : Fin 10) (9 : Fin 10) :=
  .cons (show (⊤ : SimpleGraph (Fin 10)).Adj 0 1 by simp) <|
  .cons (show (⊤ : SimpleGraph (Fin 10)).Adj 1 2 by simp) <|
  .cons (show (⊤ : SimpleGraph (Fin 10)).Adj 2 3 by simp) <|
  .cons (show (⊤ : SimpleGraph (Fin 10)).Adj 3 4 by simp) <|
  .cons (show (⊤ : SimpleGraph (Fin 10)).Adj 4 5 by simp) <|
  .cons (show (⊤ : SimpleGraph (Fin 10)).Adj 5 6 by simp) <|
  .cons (show (⊤ : SimpleGraph (Fin 10)).Adj 6 7 by simp) <|
  .cons (show (⊤ : SimpleGraph (Fin 10)).Adj 7 8 by simp) <|
  .cons (show (⊤ : SimpleGraph (Fin 10)).Adj 8 9 by simp) <|
  .nil

theorem completeWalk10_isHamiltonian : completeWalk10.IsHamiltonian := by
  intro v
  fin_cases v <;> simp [completeWalk10]

theorem traceable_top10 : Traceable (⊤ : SimpleGraph (Fin 10)) :=
  ⟨0, 9, completeWalk10, completeWalk10_isHamiltonian⟩

theorem adjUpper_true_of_completeUpper10 (g : BitVec 45)
    (complete : completeUpper (n := 10) g = true)
    {u v : Nat} (huv : u < v) (hv : v < 10) :
    adjUpper (n := 10) g u v = true := by
  rw [completeUpper] at complete
  exact (List.all_eq_true.mp complete) (u, v)
    (mem_upperPairs_iff.mpr ⟨hv, huv⟩)

theorem graphOfUpper_eq_top_of_completeUpper10 (g : BitVec 45)
    (complete : completeUpper (n := 10) g = true) :
    graphOfUpper (n := 10) g = ⊤ := by
  ext x y
  change adjUpper (n := 10) g x y = true ↔
    (⊤ : SimpleGraph (Fin 10)).Adj x y
  rw [SimpleGraph.top_adj]
  constructor
  · intro adjacent hxy
    subst y
    simp [adjUpper] at adjacent
  · intro hxy
    have hvalne : x.val ≠ y.val := fun h => hxy (Fin.ext h)
    by_cases hlt : x.val < y.val
    · exact adjUpper_true_of_completeUpper10 g complete hlt y.isLt
    · have hyx : y.val < x.val := by omega
      rw [adjUpper_comm (n := 10) g x y]
      exact adjUpper_true_of_completeUpper10 g complete hyx x.isLt

theorem traceable_graphOfUpper_of_completeUpper10 (g : BitVec 45)
    (complete : completeUpper (n := 10) g = true) :
    Traceable (graphOfUpper (n := 10) g) := by
  rw [graphOfUpper_eq_top_of_completeUpper10 g complete]
  exact traceable_top10

def completeWalk11 :
    (⊤ : SimpleGraph (Fin 11)).Walk (0 : Fin 11) (10 : Fin 11) :=
  .cons (show (⊤ : SimpleGraph (Fin 11)).Adj 0 1 by simp) <|
  .cons (show (⊤ : SimpleGraph (Fin 11)).Adj 1 2 by simp) <|
  .cons (show (⊤ : SimpleGraph (Fin 11)).Adj 2 3 by simp) <|
  .cons (show (⊤ : SimpleGraph (Fin 11)).Adj 3 4 by simp) <|
  .cons (show (⊤ : SimpleGraph (Fin 11)).Adj 4 5 by simp) <|
  .cons (show (⊤ : SimpleGraph (Fin 11)).Adj 5 6 by simp) <|
  .cons (show (⊤ : SimpleGraph (Fin 11)).Adj 6 7 by simp) <|
  .cons (show (⊤ : SimpleGraph (Fin 11)).Adj 7 8 by simp) <|
  .cons (show (⊤ : SimpleGraph (Fin 11)).Adj 8 9 by simp) <|
  .cons (show (⊤ : SimpleGraph (Fin 11)).Adj 9 10 by simp) <|
  .nil

theorem completeWalk11_isHamiltonian : completeWalk11.IsHamiltonian := by
  intro v
  fin_cases v <;> simp [completeWalk11]

theorem traceable_top11 : Traceable (⊤ : SimpleGraph (Fin 11)) :=
  ⟨0, 10, completeWalk11, completeWalk11_isHamiltonian⟩

theorem adjUpper_true_of_completeUpper11 (g : BitVec 55)
    (complete : completeUpper (n := 11) g = true)
    {u v : Nat} (huv : u < v) (hv : v < 11) :
    adjUpper (n := 11) g u v = true := by
  rw [completeUpper] at complete
  exact (List.all_eq_true.mp complete) (u, v)
    (mem_upperPairs_iff.mpr ⟨hv, huv⟩)

theorem graphOfUpper_eq_top_of_completeUpper11 (g : BitVec 55)
    (complete : completeUpper (n := 11) g = true) :
    graphOfUpper (n := 11) g = ⊤ := by
  ext x y
  change adjUpper (n := 11) g x y = true ↔
    (⊤ : SimpleGraph (Fin 11)).Adj x y
  rw [SimpleGraph.top_adj]
  constructor
  · intro adjacent hxy
    subst y
    simp [adjUpper] at adjacent
  · intro hxy
    have hvalne : x.val ≠ y.val := fun h => hxy (Fin.ext h)
    by_cases hlt : x.val < y.val
    · exact adjUpper_true_of_completeUpper11 g complete hlt y.isLt
    · have hyx : y.val < x.val := by omega
      rw [adjUpper_comm (n := 11) g x y]
      exact adjUpper_true_of_completeUpper11 g complete hyx x.isLt

theorem traceable_graphOfUpper_of_completeUpper11 (g : BitVec 55)
    (complete : completeUpper (n := 11) g = true) :
    Traceable (graphOfUpper (n := 11) g) := by
  rw [graphOfUpper_eq_top_of_completeUpper11 g complete]
  exact traceable_top11

def completeWalk12 :
    (⊤ : SimpleGraph (Fin 12)).Walk (0 : Fin 12) (11 : Fin 12) :=
  .cons (show (⊤ : SimpleGraph (Fin 12)).Adj 0 1 by simp) <|
  .cons (show (⊤ : SimpleGraph (Fin 12)).Adj 1 2 by simp) <|
  .cons (show (⊤ : SimpleGraph (Fin 12)).Adj 2 3 by simp) <|
  .cons (show (⊤ : SimpleGraph (Fin 12)).Adj 3 4 by simp) <|
  .cons (show (⊤ : SimpleGraph (Fin 12)).Adj 4 5 by simp) <|
  .cons (show (⊤ : SimpleGraph (Fin 12)).Adj 5 6 by simp) <|
  .cons (show (⊤ : SimpleGraph (Fin 12)).Adj 6 7 by simp) <|
  .cons (show (⊤ : SimpleGraph (Fin 12)).Adj 7 8 by simp) <|
  .cons (show (⊤ : SimpleGraph (Fin 12)).Adj 8 9 by simp) <|
  .cons (show (⊤ : SimpleGraph (Fin 12)).Adj 9 10 by simp) <|
  .cons (show (⊤ : SimpleGraph (Fin 12)).Adj 10 11 by simp) <|
  .nil

theorem completeWalk12_isHamiltonian : completeWalk12.IsHamiltonian := by
  intro v
  fin_cases v <;> simp [completeWalk12]

theorem traceable_top12 : Traceable (⊤ : SimpleGraph (Fin 12)) :=
  ⟨0, 11, completeWalk12, completeWalk12_isHamiltonian⟩

theorem adjUpper_true_of_completeUpper12 (g : BitVec 66)
    (complete : completeUpper (n := 12) g = true)
    {u v : Nat} (huv : u < v) (hv : v < 12) :
    adjUpper (n := 12) g u v = true := by
  rw [completeUpper] at complete
  exact (List.all_eq_true.mp complete) (u, v)
    (mem_upperPairs_iff.mpr ⟨hv, huv⟩)

theorem graphOfUpper_eq_top_of_completeUpper12 (g : BitVec 66)
    (complete : completeUpper (n := 12) g = true) :
    graphOfUpper (n := 12) g = ⊤ := by
  ext x y
  change adjUpper (n := 12) g x y = true ↔
    (⊤ : SimpleGraph (Fin 12)).Adj x y
  rw [SimpleGraph.top_adj]
  constructor
  · intro adjacent hxy
    subst y
    simp [adjUpper] at adjacent
  · intro hxy
    have hvalne : x.val ≠ y.val := fun h => hxy (Fin.ext h)
    by_cases hlt : x.val < y.val
    · exact adjUpper_true_of_completeUpper12 g complete hlt y.isLt
    · have hyx : y.val < x.val := by omega
      rw [adjUpper_comm (n := 12) g x y]
      exact adjUpper_true_of_completeUpper12 g complete hyx x.isLt

theorem traceable_graphOfUpper_of_completeUpper12 (g : BitVec 66)
    (complete : completeUpper (n := 12) g = true) :
    Traceable (graphOfUpper (n := 12) g) := by
  rw [graphOfUpper_eq_top_of_completeUpper12 g complete]
  exact traceable_top12

end WOWII217ClosureSemanticsSmall
