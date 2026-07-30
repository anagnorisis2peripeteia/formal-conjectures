import WOWII217ClosureSemantics
import WOWII217FiniteSmallExceptions
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Maxine
import WOWII217ClosureSemanticsSmall
import WOWII217ClosureBridge
import WOWII217Bridge.MaxDegree
import WOWII217Bridge.AbsLink
import WOWII217SmallNExceptionsChunks.Branches
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

open SimpleGraph Classical Finset WOWII217ClosureSemantics WOWII217FiniteSmallExceptions WOWII217ClosureBridge
open WOWII217Encoding4 WOWII217Connected4 WOWII217Degree4
open WOWII217Encoding5 WOWII217Connected5 WOWII217Degree5
open WOWII217Encoding6 WOWII217Connected6 WOWII217Degree6
open WOWII217Encoding7 WOWII217Connected7 WOWII217Degree7
open WOWII217Encoding8 WOWII217Connected8 WOWII217Degree8
open WOWII217Encoding9 WOWII217Connected9 WOWII217Degree9
open WOWII217Encoding10 WOWII217Connected10 WOWII217Degree10
open WOWII217Encoding11 WOWII217Connected11 WOWII217Degree11
open WOWII217Encoding12 WOWII217Connected12 WOWII217Degree12

namespace WOWII217SmallNExceptions

theorem exception_stuck_non_regular
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (connected : G.Connected)
    (hCard : Fintype.card V ≤ 12)
    (hResidue : residue G = 2)
    (hMaxDeg : G.maxDegree ≤ 6)
    (hStuck : 2 * G.maxDegree < Fintype.card V - 1)
    (hNot2 : ¬ G.IsRegularOfDegree 2)
    (hNot3 : ¬ (Fintype.card V = 8 ∧ G.IsRegularOfDegree 3))
    (hNot4 : ¬ (Fintype.card V = 10 ∧ G.IsRegularOfDegree 4))
    : ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  have hCard12 : Fintype.card V ≤ 12 := by assumption
  match hn : Fintype.card V with
  | 4 =>
    -- `hStuck : 2 * maxDegree < card V - 1` forces `maxDegree <= 1`, but a connected
    -- graph on >= 3 vertices has a vertex of degree >= 2. Vacuous.
    exact (MaxDeg.stuck_vacuous_of_card_le_five G connected (by omega) (by omega) hStuck).elim
  | 5 =>
    obtain ⟨e, he⟩ := AbsLink.exists_ofFn_eq_reverse (n := 5) G (by omega)
    if hS11222 : G.degreeSequence = [1, 1, 2, 2, 2] then
      exact exception_stuck_non_regular_card5_seq22211 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (hStuck := hStuck) (hNot2 := hNot2) (hNot3 := hNot3)
        (hNot4 := hNot4) (hCard := by simpa [hn]) ⟨e, by rw [he, hS11222]; rfl⟩
    else
      sorry
  | 6 =>
    obtain ⟨e, he⟩ := AbsLink.exists_ofFn_eq_reverse (n := 6) G (by omega)
    if hS222233 : G.degreeSequence = [2, 2, 2, 2, 3, 3] then
      exact exception_stuck_non_regular_card6_seq332222 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (hStuck := hStuck) (hNot2 := hNot2) (hNot3 := hNot3)
        (hNot4 := hNot4) (hCard := by simpa [hn]) ⟨e, by rw [he, hS222233]; rfl⟩
    else if hS122333 : G.degreeSequence = [1, 2, 2, 3, 3, 3] then
      exact exception_stuck_non_regular_card6_seq333221 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (hStuck := hStuck) (hNot2 := hNot2) (hNot3 := hNot3)
        (hNot4 := hNot4) (hCard := by simpa [hn]) ⟨e, by rw [he, hS122333]; rfl⟩
    else if hS113333 : G.degreeSequence = [1, 1, 3, 3, 3, 3] then
      exact exception_stuck_non_regular_card6_seq333311 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (hStuck := hStuck) (hNot2 := hNot2) (hNot3 := hNot3)
        (hNot4 := hNot4) (hCard := by simpa [hn]) ⟨e, by rw [he, hS113333]; rfl⟩
    else if hS222334 : G.degreeSequence = [2, 2, 2, 3, 3, 4] then
      exact exception_stuck_non_regular_card6_seq433222 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (hStuck := hStuck) (hNot2 := hNot2) (hNot3 := hNot3)
        (hNot4 := hNot4) (hCard := by simpa [hn]) ⟨e, by rw [he, hS222334]; rfl⟩
    else if hS123334 : G.degreeSequence = [1, 2, 3, 3, 3, 4] then
      exact exception_stuck_non_regular_card6_seq433321 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (hStuck := hStuck) (hNot2 := hNot2) (hNot3 := hNot3)
        (hNot4 := hNot4) (hCard := by simpa [hn]) ⟨e, by rw [he, hS123334]; rfl⟩
    else
      sorry
  | 7 =>
    obtain ⟨e, he⟩ := AbsLink.exists_ofFn_eq_reverse (n := 7) G (by omega)
    if hS2223333 : G.degreeSequence = [2, 2, 2, 3, 3, 3, 3] then
      exact exception_stuck_non_regular_card7_seq3333222 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (hStuck := hStuck) (hNot2 := hNot2) (hNot3 := hNot3)
        (hNot4 := hNot4) (hCard := by simpa [hn]) ⟨e, by rw [he, hS2223333]; rfl⟩
    else if hS2224444 : G.degreeSequence = [2, 2, 2, 4, 4, 4, 4] then
      exact exception_stuck_non_regular_card7_seq4444222 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (hStuck := hStuck) (hNot2 := hNot2) (hNot3 := hNot3)
        (hNot4 := hNot4) (hCard := by simpa [hn]) ⟨e, by rw [he, hS2224444]; rfl⟩
    else if hS1234444 : G.degreeSequence = [1, 2, 3, 4, 4, 4, 4] then
      exact exception_stuck_non_regular_card7_seq4444321 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (hStuck := hStuck) (hNot2 := hNot2) (hNot3 := hNot3)
        (hNot4 := hNot4) (hCard := by simpa [hn]) ⟨e, by rw [he, hS1234444]; rfl⟩
    else if hS1144444 : G.degreeSequence = [1, 1, 4, 4, 4, 4, 4] then
      exact exception_stuck_non_regular_card7_seq4444411 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (hStuck := hStuck) (hNot2 := hNot2) (hNot3 := hNot3)
        (hNot4 := hNot4) (hCard := by simpa [hn]) ⟨e, by rw [he, hS1144444]; rfl⟩
    else if hS1244445 : G.degreeSequence = [1, 2, 4, 4, 4, 4, 5] then
      exact exception_stuck_non_regular_card7_seq5444421 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (hStuck := hStuck) (hNot2 := hNot2) (hNot3 := hNot3)
        (hNot4 := hNot4) (hCard := by simpa [hn]) ⟨e, by rw [he, hS1244445]; rfl⟩
    else
      sorry
  | 8 =>
    obtain ⟨e, he⟩ := AbsLink.exists_ofFn_eq_reverse (n := 8) G (by omega)
    if hS33333344 : G.degreeSequence = [3, 3, 3, 3, 3, 3, 4, 4] then
      exact exception_stuck_non_regular_card8_seq44333333 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (hStuck := hStuck) (hNot2 := hNot2) (hNot3 := hNot3)
        (hNot4 := hNot4) (hCard := by simpa [hn]) ⟨e, by rw [he, hS33333344]; rfl⟩
    else if hS23333444 : G.degreeSequence = [2, 3, 3, 3, 3, 4, 4, 4] then
      exact exception_stuck_non_regular_card8_seq44433332 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (hStuck := hStuck) (hNot2 := hNot2) (hNot3 := hNot3)
        (hNot4 := hNot4) (hCard := by simpa [hn]) ⟨e, by rw [he, hS23333444]; rfl⟩
    else if hS22334444 : G.degreeSequence = [2, 2, 3, 3, 4, 4, 4, 4] then
      exact exception_stuck_non_regular_card8_seq44443322 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (hStuck := hStuck) (hNot2 := hNot2) (hNot3 := hNot3)
        (hNot4 := hNot4) (hCard := by simpa [hn]) ⟨e, by rw [he, hS22334444]; rfl⟩
    else if hS33334444 : G.degreeSequence = [3, 3, 3, 3, 4, 4, 4, 4] then
      exact exception_stuck_non_regular_card8_seq44443333 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (hStuck := hStuck) (hNot2 := hNot2) (hNot3 := hNot3)
        (hNot4 := hNot4) (hCard := by simpa [hn]) ⟨e, by rw [he, hS33334444]; rfl⟩
    else if hS22244444 : G.degreeSequence = [2, 2, 2, 4, 4, 4, 4, 4] then
      exact exception_stuck_non_regular_card8_seq44444222 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (hStuck := hStuck) (hNot2 := hNot2) (hNot3 := hNot3)
        (hNot4 := hNot4) (hCard := by simpa [hn]) ⟨e, by rw [he, hS22244444]; rfl⟩
    else if hS23344444 : G.degreeSequence = [2, 3, 3, 4, 4, 4, 4, 4] then
      exact exception_stuck_non_regular_card8_seq44444332 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (hStuck := hStuck) (hNot2 := hNot2) (hNot3 := hNot3)
        (hNot4 := hNot4) (hCard := by simpa [hn]) ⟨e, by rw [he, hS23344444]; rfl⟩
    else if hS33333445 : G.degreeSequence = [3, 3, 3, 3, 3, 4, 4, 5] then
      exact exception_stuck_non_regular_card8_seq54433333 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (hStuck := hStuck) (hNot2 := hNot2) (hNot3 := hNot3)
        (hNot4 := hNot4) (hCard := by simpa [hn]) ⟨e, by rw [he, hS33333445]; rfl⟩
    else if hS23334445 : G.degreeSequence = [2, 3, 3, 3, 4, 4, 4, 5] then
      exact exception_stuck_non_regular_card8_seq54443332 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (hStuck := hStuck) (hNot2 := hNot2) (hNot3 := hNot3)
        (hNot4 := hNot4) (hCard := by simpa [hn]) ⟨e, by rw [he, hS23334445]; rfl⟩
    else if hS22344445 : G.degreeSequence = [2, 2, 3, 4, 4, 4, 4, 5] then
      exact exception_stuck_non_regular_card8_seq54444322 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (hStuck := hStuck) (hNot2 := hNot2) (hNot3 := hNot3)
        (hNot4 := hNot4) (hCard := by simpa [hn]) ⟨e, by rw [he, hS22344445]; rfl⟩
    else if hS33334455 : G.degreeSequence = [3, 3, 3, 3, 4, 4, 5, 5] then
      exact exception_stuck_non_regular_card8_seq55443333 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (hStuck := hStuck) (hNot2 := hNot2) (hNot3 := hNot3)
        (hNot4 := hNot4) (hCard := by simpa [hn]) ⟨e, by rw [he, hS33334455]; rfl⟩
    else if hS23344455 : G.degreeSequence = [2, 3, 3, 4, 4, 4, 5, 5] then
      exact exception_stuck_non_regular_card8_seq55444332 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (hStuck := hStuck) (hNot2 := hNot2) (hNot3 := hNot3)
        (hNot4 := hNot4) (hCard := by simpa [hn]) ⟨e, by rw [he, hS23344455]; rfl⟩
    else if hS33335555 : G.degreeSequence = [3, 3, 3, 3, 5, 5, 5, 5] then
      exact exception_stuck_non_regular_card8_seq55553333 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (hStuck := hStuck) (hNot2 := hNot2) (hNot3 := hNot3)
        (hNot4 := hNot4) (hCard := by simpa [hn]) ⟨e, by rw [he, hS33335555]; rfl⟩
    else if hS13445555 : G.degreeSequence = [1, 3, 4, 4, 5, 5, 5, 5] then
      exact exception_stuck_non_regular_card8_seq55554431 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (hStuck := hStuck) (hNot2 := hNot2) (hNot3 := hNot3)
        (hNot4 := hNot4) (hCard := by simpa [hn]) ⟨e, by rw [he, hS13445555]; rfl⟩
    else if hS22355555 : G.degreeSequence = [2, 2, 3, 5, 5, 5, 5, 5] then
      exact exception_stuck_non_regular_card8_seq55555322 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (hStuck := hStuck) (hNot2 := hNot2) (hNot3 := hNot3)
        (hNot4 := hNot4) (hCard := by simpa [hn]) ⟨e, by rw [he, hS22355555]; rfl⟩
    else if hS13355555 : G.degreeSequence = [1, 3, 3, 5, 5, 5, 5, 5] then
      exact exception_stuck_non_regular_card8_seq55555331 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (hStuck := hStuck) (hNot2 := hNot2) (hNot3 := hNot3)
        (hNot4 := hNot4) (hCard := by simpa [hn]) ⟨e, by rw [he, hS13355555]; rfl⟩
    else if hS12455555 : G.degreeSequence = [1, 2, 4, 5, 5, 5, 5, 5] then
      exact exception_stuck_non_regular_card8_seq55555421 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (hStuck := hStuck) (hNot2 := hNot2) (hNot3 := hNot3)
        (hNot4 := hNot4) (hCard := by simpa [hn]) ⟨e, by rw [he, hS12455555]; rfl⟩
    else if hS11555555 : G.degreeSequence = [1, 1, 5, 5, 5, 5, 5, 5] then
      exact exception_stuck_non_regular_card8_seq55555511 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (hStuck := hStuck) (hNot2 := hNot2) (hNot3 := hNot3)
        (hNot4 := hNot4) (hCard := by simpa [hn]) ⟨e, by rw [he, hS11555555]; rfl⟩
    else if hS13555555 : G.degreeSequence = [1, 3, 5, 5, 5, 5, 5, 5] then
      exact exception_stuck_non_regular_card8_seq55555531 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (hStuck := hStuck) (hNot2 := hNot2) (hNot3 := hNot3)
        (hNot4 := hNot4) (hCard := by simpa [hn]) ⟨e, by rw [he, hS13555555]; rfl⟩
    else if hS33334446 : G.degreeSequence = [3, 3, 3, 3, 4, 4, 4, 6] then
      exact exception_stuck_non_regular_card8_seq64443333 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (hStuck := hStuck) (hNot2 := hNot2) (hNot3 := hNot3)
        (hNot4 := hNot4) (hCard := by simpa [hn]) ⟨e, by rw [he, hS33334446]; rfl⟩
    else if hS23344446 : G.degreeSequence = [2, 3, 3, 4, 4, 4, 4, 6] then
      exact exception_stuck_non_regular_card8_seq64444332 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (hStuck := hStuck) (hNot2 := hNot2) (hNot3 := hNot3)
        (hNot4 := hNot4) (hCard := by simpa [hn]) ⟨e, by rw [he, hS23344446]; rfl⟩
    else if hS13455556 : G.degreeSequence = [1, 3, 4, 5, 5, 5, 5, 6] then
      exact exception_stuck_non_regular_card8_seq65555431 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (hStuck := hStuck) (hNot2 := hNot2) (hNot3 := hNot3)
        (hNot4 := hNot4) (hCard := by simpa [hn]) ⟨e, by rw [he, hS13455556]; rfl⟩
    else if hS12555556 : G.degreeSequence = [1, 2, 5, 5, 5, 5, 5, 6] then
      exact exception_stuck_non_regular_card8_seq65555521 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (hStuck := hStuck) (hNot2 := hNot2) (hNot3 := hNot3)
        (hNot4 := hNot4) (hCard := by simpa [hn]) ⟨e, by rw [he, hS12555556]; rfl⟩
    else if hS13555566 : G.degreeSequence = [1, 3, 5, 5, 5, 5, 6, 6] then
      exact exception_stuck_non_regular_card8_seq66555531 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (hStuck := hStuck) (hNot2 := hNot2) (hNot3 := hNot3)
        (hNot4 := hNot4) (hCard := by simpa [hn]) ⟨e, by rw [he, hS13555566]; rfl⟩
    else
      sorry
  | 9 =>
    obtain ⟨e, he⟩ := AbsLink.exists_ofFn_eq_reverse (n := 9) G (by omega)
    if hS333344444 : G.degreeSequence = [3, 3, 3, 3, 4, 4, 4, 4, 4] then
      exact exception_stuck_non_regular_card9_seq444443333 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (hStuck := hStuck) (hNot2 := hNot2) (hNot3 := hNot3)
        (hNot4 := hNot4) (hCard := by simpa [hn]) ⟨e, by rw [he, hS333344444]; rfl⟩
    else if hS333345555 : G.degreeSequence = [3, 3, 3, 3, 4, 5, 5, 5, 5] then
      exact exception_stuck_non_regular_card9_seq555543333 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (hStuck := hStuck) (hNot2 := hNot2) (hNot3 := hNot3)
        (hNot4 := hNot4) (hCard := by simpa [hn]) ⟨e, by rw [he, hS333345555]; rfl⟩
    else if hS233445555 : G.degreeSequence = [2, 3, 3, 4, 4, 5, 5, 5, 5] then
      exact exception_stuck_non_regular_card9_seq555544332 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (hStuck := hStuck) (hNot2 := hNot2) (hNot3 := hNot3)
        (hNot4 := hNot4) (hCard := by simpa [hn]) ⟨e, by rw [he, hS233445555]; rfl⟩
    else if hS233355555 : G.degreeSequence = [2, 3, 3, 3, 5, 5, 5, 5, 5] then
      exact exception_stuck_non_regular_card9_seq555553332 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (hStuck := hStuck) (hNot2 := hNot2) (hNot3 := hNot3)
        (hNot4 := hNot4) (hCard := by simpa [hn]) ⟨e, by rw [he, hS233355555]; rfl⟩
    else if hS223455555 : G.degreeSequence = [2, 2, 3, 4, 5, 5, 5, 5, 5] then
      exact exception_stuck_non_regular_card9_seq555554322 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (hStuck := hStuck) (hNot2 := hNot2) (hNot3 := hNot3)
        (hNot4 := hNot4) (hCard := by simpa [hn]) ⟨e, by rw [he, hS223455555]; rfl⟩
    else if hS222555555 : G.degreeSequence = [2, 2, 2, 5, 5, 5, 5, 5, 5] then
      exact exception_stuck_non_regular_card9_seq555555222 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (hStuck := hStuck) (hNot2 := hNot2) (hNot3 := hNot3)
        (hNot4 := hNot4) (hCard := by simpa [hn]) ⟨e, by rw [he, hS222555555]; rfl⟩
    else if hS233555555 : G.degreeSequence = [2, 3, 3, 5, 5, 5, 5, 5, 5] then
      exact exception_stuck_non_regular_card9_seq555555332 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (hStuck := hStuck) (hNot2 := hNot2) (hNot3 := hNot3)
        (hNot4 := hNot4) (hCard := by simpa [hn]) ⟨e, by rw [he, hS233555555]; rfl⟩
    else if hS333355556 : G.degreeSequence = [3, 3, 3, 3, 5, 5, 5, 5, 6] then
      exact exception_stuck_non_regular_card9_seq655553333 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (hStuck := hStuck) (hNot2 := hNot2) (hNot3 := hNot3)
        (hNot4 := hNot4) (hCard := by simpa [hn]) ⟨e, by rw [he, hS333355556]; rfl⟩
    else if hS233455556 : G.degreeSequence = [2, 3, 3, 4, 5, 5, 5, 5, 6] then
      exact exception_stuck_non_regular_card9_seq655554332 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (hStuck := hStuck) (hNot2 := hNot2) (hNot3 := hNot3)
        (hNot4 := hNot4) (hCard := by simpa [hn]) ⟨e, by rw [he, hS233455556]; rfl⟩
    else if hS223555556 : G.degreeSequence = [2, 2, 3, 5, 5, 5, 5, 5, 6] then
      exact exception_stuck_non_regular_card9_seq655555322 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (hStuck := hStuck) (hNot2 := hNot2) (hNot3 := hNot3)
        (hNot4 := hNot4) (hCard := by simpa [hn]) ⟨e, by rw [he, hS223555556]; rfl⟩
    else if hS233555566 : G.degreeSequence = [2, 3, 3, 5, 5, 5, 5, 6, 6] then
      exact exception_stuck_non_regular_card9_seq665555332 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (hStuck := hStuck) (hNot2 := hNot2) (hNot3 := hNot3)
        (hNot4 := hNot4) (hCard := by simpa [hn]) ⟨e, by rw [he, hS233555566]; rfl⟩
    else if hS135566666 : G.degreeSequence = [1, 3, 5, 5, 6, 6, 6, 6, 6] then
      exact exception_stuck_non_regular_card9_seq666665531 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (hStuck := hStuck) (hNot2 := hNot2) (hNot3 := hNot3)
        (hNot4 := hNot4) (hCard := by simpa [hn]) ⟨e, by rw [he, hS135566666]; rfl⟩
    else if hS134666666 : G.degreeSequence = [1, 3, 4, 6, 6, 6, 6, 6, 6] then
      exact exception_stuck_non_regular_card9_seq666666431 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (hStuck := hStuck) (hNot2 := hNot2) (hNot3 := hNot3)
        (hNot4 := hNot4) (hCard := by simpa [hn]) ⟨e, by rw [he, hS134666666]; rfl⟩
    else if hS125666666 : G.degreeSequence = [1, 2, 5, 6, 6, 6, 6, 6, 6] then
      exact exception_stuck_non_regular_card9_seq666666521 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (hStuck := hStuck) (hNot2 := hNot2) (hNot3 := hNot3)
        (hNot4 := hNot4) (hCard := by simpa [hn]) ⟨e, by rw [he, hS125666666]; rfl⟩
    else if hS116666666 : G.degreeSequence = [1, 1, 6, 6, 6, 6, 6, 6, 6] then
      exact exception_stuck_non_regular_card9_seq666666611 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (hStuck := hStuck) (hNot2 := hNot2) (hNot3 := hNot3)
        (hNot4 := hNot4) (hCard := by simpa [hn]) ⟨e, by rw [he, hS116666666]; rfl⟩
    else if hS136666666 : G.degreeSequence = [1, 3, 6, 6, 6, 6, 6, 6, 6] then
      exact exception_stuck_non_regular_card9_seq666666631 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (hStuck := hStuck) (hNot2 := hNot2) (hNot3 := hNot3)
        (hNot4 := hNot4) (hCard := by simpa [hn]) ⟨e, by rw [he, hS136666666]; rfl⟩
    else
      sorry
  | 10 =>
    obtain ⟨e, he⟩ := AbsLink.exists_ofFn_eq_reverse (n := 10) G (by omega)
    if hS4444444455 : G.degreeSequence = [4, 4, 4, 4, 4, 4, 4, 4, 5, 5] then
      exact exception_stuck_non_regular_card10_seq5544444444 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (hStuck := hStuck) (hNot2 := hNot2) (hNot3 := hNot3)
        (hNot4 := hNot4) (hCard := by simpa [hn]) ⟨e, by rw [he, hS4444444455]; rfl⟩
    else if hS3444444555 : G.degreeSequence = [3, 4, 4, 4, 4, 4, 4, 5, 5, 5] then
      exact exception_stuck_non_regular_card10_seq5554444443 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (hStuck := hStuck) (hNot2 := hNot2) (hNot3 := hNot3)
        (hNot4 := hNot4) (hCard := by simpa [hn]) ⟨e, by rw [he, hS3444444555]; rfl⟩
    else if hS3344445555 : G.degreeSequence = [3, 3, 4, 4, 4, 4, 5, 5, 5, 5] then
      exact exception_stuck_non_regular_card10_seq5555444433 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (hStuck := hStuck) (hNot2 := hNot2) (hNot3 := hNot3)
        (hNot4 := hNot4) (hCard := by simpa [hn]) ⟨e, by rw [he, hS3344445555]; rfl⟩
    else if hS4444445555 : G.degreeSequence = [4, 4, 4, 4, 4, 4, 5, 5, 5, 5] then
      exact exception_stuck_non_regular_card10_seq5555444444 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (hStuck := hStuck) (hNot2 := hNot2) (hNot3 := hNot3)
        (hNot4 := hNot4) (hCard := by simpa [hn]) ⟨e, by rw [he, hS4444445555]; rfl⟩
    else if hS3334455555 : G.degreeSequence = [3, 3, 3, 4, 4, 5, 5, 5, 5, 5] then
      exact exception_stuck_non_regular_card10_seq5555544333 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (hStuck := hStuck) (hNot2 := hNot2) (hNot3 := hNot3)
        (hNot4 := hNot4) (hCard := by simpa [hn]) ⟨e, by rw [he, hS3334455555]; rfl⟩
    else if hS3444455555 : G.degreeSequence = [3, 4, 4, 4, 4, 5, 5, 5, 5, 5] then
      exact exception_stuck_non_regular_card10_seq5555544443 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (hStuck := hStuck) (hNot2 := hNot2) (hNot3 := hNot3)
        (hNot4 := hNot4) (hCard := by simpa [hn]) ⟨e, by rw [he, hS3444455555]; rfl⟩
    else if hS3333555555 : G.degreeSequence = [3, 3, 3, 3, 5, 5, 5, 5, 5, 5] then
      exact exception_stuck_non_regular_card10_seq5555553333 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (hStuck := hStuck) (hNot2 := hNot2) (hNot3 := hNot3)
        (hNot4 := hNot4) (hCard := by simpa [hn]) ⟨e, by rw [he, hS3333555555]; rfl⟩
    else if hS3344555555 : G.degreeSequence = [3, 3, 4, 4, 5, 5, 5, 5, 5, 5] then
      exact exception_stuck_non_regular_card10_seq5555554433 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (hStuck := hStuck) (hNot2 := hNot2) (hNot3 := hNot3)
        (hNot4 := hNot4) (hCard := by simpa [hn]) ⟨e, by rw [he, hS3344555555]; rfl⟩
    else if hS2444555555 : G.degreeSequence = [2, 4, 4, 4, 5, 5, 5, 5, 5, 5] then
      exact exception_stuck_non_regular_card10_seq5555554442 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (hStuck := hStuck) (hNot2 := hNot2) (hNot3 := hNot3)
        (hNot4 := hNot4) (hCard := by simpa [hn]) ⟨e, by rw [he, hS2444555555]; rfl⟩
    else if hS4444444556 : G.degreeSequence = [4, 4, 4, 4, 4, 4, 4, 5, 5, 6] then
      exact exception_stuck_non_regular_card10_seq6554444444 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (hStuck := hStuck) (hNot2 := hNot2) (hNot3 := hNot3)
        (hNot4 := hNot4) (hCard := by simpa [hn]) ⟨e, by rw [he, hS4444444556]; rfl⟩
    else if hS3444445556 : G.degreeSequence = [3, 4, 4, 4, 4, 4, 5, 5, 5, 6] then
      exact exception_stuck_non_regular_card10_seq6555444443 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (hStuck := hStuck) (hNot2 := hNot2) (hNot3 := hNot3)
        (hNot4 := hNot4) (hCard := by simpa [hn]) ⟨e, by rw [he, hS3444445556]; rfl⟩
    else if hS3344455556 : G.degreeSequence = [3, 3, 4, 4, 4, 5, 5, 5, 5, 6] then
      exact exception_stuck_non_regular_card10_seq6555544433 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (hStuck := hStuck) (hNot2 := hNot2) (hNot3 := hNot3)
        (hNot4 := hNot4) (hCard := by simpa [hn]) ⟨e, by rw [he, hS3344455556]; rfl⟩
    else if hS4444455556 : G.degreeSequence = [4, 4, 4, 4, 4, 5, 5, 5, 5, 6] then
      exact exception_stuck_non_regular_card10_seq6555544444 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (hStuck := hStuck) (hNot2 := hNot2) (hNot3 := hNot3)
        (hNot4 := hNot4) (hCard := by simpa [hn]) ⟨e, by rw [he, hS4444455556]; rfl⟩
    else if hS3334555556 : G.degreeSequence = [3, 3, 3, 4, 5, 5, 5, 5, 5, 6] then
      exact exception_stuck_non_regular_card10_seq6555554333 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (hStuck := hStuck) (hNot2 := hNot2) (hNot3 := hNot3)
        (hNot4 := hNot4) (hCard := by simpa [hn]) ⟨e, by rw [he, hS3334555556]; rfl⟩
    else if hS3444555556 : G.degreeSequence = [3, 4, 4, 4, 5, 5, 5, 5, 5, 6] then
      exact exception_stuck_non_regular_card10_seq6555554443 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (hStuck := hStuck) (hNot2 := hNot2) (hNot3 := hNot3)
        (hNot4 := hNot4) (hCard := by simpa [hn]) ⟨e, by rw [he, hS3444555556]; rfl⟩
    else if hS4444445566 : G.degreeSequence = [4, 4, 4, 4, 4, 4, 5, 5, 6, 6] then
      exact exception_stuck_non_regular_card10_seq6655444444 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (hStuck := hStuck) (hNot2 := hNot2) (hNot3 := hNot3)
        (hNot4 := hNot4) (hCard := by simpa [hn]) ⟨e, by rw [he, hS4444445566]; rfl⟩
    else if hS3444455566 : G.degreeSequence = [3, 4, 4, 4, 4, 5, 5, 5, 6, 6] then
      exact exception_stuck_non_regular_card10_seq6655544443 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (hStuck := hStuck) (hNot2 := hNot2) (hNot3 := hNot3)
        (hNot4 := hNot4) (hCard := by simpa [hn]) ⟨e, by rw [he, hS3444455566]; rfl⟩
    else if hS3344555566 : G.degreeSequence = [3, 3, 4, 4, 5, 5, 5, 5, 6, 6] then
      exact exception_stuck_non_regular_card10_seq6655554433 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (hStuck := hStuck) (hNot2 := hNot2) (hNot3 := hNot3)
        (hNot4 := hNot4) (hCard := by simpa [hn]) ⟨e, by rw [he, hS3344555566]; rfl⟩
    else if hS4444455666 : G.degreeSequence = [4, 4, 4, 4, 4, 5, 5, 6, 6, 6] then
      exact exception_stuck_non_regular_card10_seq6665544444 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (hStuck := hStuck) (hNot2 := hNot2) (hNot3 := hNot3)
        (hNot4 := hNot4) (hCard := by simpa [hn]) ⟨e, by rw [he, hS4444455666]; rfl⟩
    else if hS3444555666 : G.degreeSequence = [3, 4, 4, 4, 5, 5, 5, 6, 6, 6] then
      exact exception_stuck_non_regular_card10_seq6665554443 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (hStuck := hStuck) (hNot2 := hNot2) (hNot3 := hNot3)
        (hNot4 := hNot4) (hCard := by simpa [hn]) ⟨e, by rw [he, hS3444555666]; rfl⟩
    else if hS3444456666 : G.degreeSequence = [3, 4, 4, 4, 4, 5, 6, 6, 6, 6] then
      exact exception_stuck_non_regular_card10_seq6666544443 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (hStuck := hStuck) (hNot2 := hNot2) (hNot3 := hNot3)
        (hNot4 := hNot4) (hCard := by simpa [hn]) ⟨e, by rw [he, hS3444456666]; rfl⟩
    else if hS3344556666 : G.degreeSequence = [3, 3, 4, 4, 5, 5, 6, 6, 6, 6] then
      exact exception_stuck_non_regular_card10_seq6666554433 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (hStuck := hStuck) (hNot2 := hNot2) (hNot3 := hNot3)
        (hNot4 := hNot4) (hCard := by simpa [hn]) ⟨e, by rw [he, hS3344556666]; rfl⟩
    else if hS2444556666 : G.degreeSequence = [2, 4, 4, 4, 5, 5, 6, 6, 6, 6] then
      exact exception_stuck_non_regular_card10_seq6666554442 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (hStuck := hStuck) (hNot2 := hNot2) (hNot3 := hNot3)
        (hNot4 := hNot4) (hCard := by simpa [hn]) ⟨e, by rw [he, hS2444556666]; rfl⟩
    else if hS3344466666 : G.degreeSequence = [3, 3, 4, 4, 4, 6, 6, 6, 6, 6] then
      exact exception_stuck_non_regular_card10_seq6666644433 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (hStuck := hStuck) (hNot2 := hNot2) (hNot3 := hNot3)
        (hNot4 := hNot4) (hCard := by simpa [hn]) ⟨e, by rw [he, hS3344466666]; rfl⟩
    else if hS2444466666 : G.degreeSequence = [2, 4, 4, 4, 4, 6, 6, 6, 6, 6] then
      exact exception_stuck_non_regular_card10_seq6666644442 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (hStuck := hStuck) (hNot2 := hNot2) (hNot3 := hNot3)
        (hNot4 := hNot4) (hCard := by simpa [hn]) ⟨e, by rw [he, hS2444466666]; rfl⟩
    else if hS4444466666 : G.degreeSequence = [4, 4, 4, 4, 4, 6, 6, 6, 6, 6] then
      exact exception_stuck_non_regular_card10_seq6666644444 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (hStuck := hStuck) (hNot2 := hNot2) (hNot3 := hNot3)
        (hNot4 := hNot4) (hCard := by simpa [hn]) ⟨e, by rw [he, hS4444466666]; rfl⟩
    else if hS3334566666 : G.degreeSequence = [3, 3, 3, 4, 5, 6, 6, 6, 6, 6] then
      exact exception_stuck_non_regular_card10_seq6666654333 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (hStuck := hStuck) (hNot2 := hNot2) (hNot3 := hNot3)
        (hNot4 := hNot4) (hCard := by simpa [hn]) ⟨e, by rw [he, hS3334566666]; rfl⟩
    else if hS2335566666 : G.degreeSequence = [2, 3, 3, 5, 5, 6, 6, 6, 6, 6] then
      exact exception_stuck_non_regular_card10_seq6666655332 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (hStuck := hStuck) (hNot2 := hNot2) (hNot3 := hNot3)
        (hNot4 := hNot4) (hCard := by simpa [hn]) ⟨e, by rw [he, hS2335566666]; rfl⟩
    else if hS2245566666 : G.degreeSequence = [2, 2, 4, 5, 5, 6, 6, 6, 6, 6] then
      exact exception_stuck_non_regular_card10_seq6666655422 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (hStuck := hStuck) (hNot2 := hNot2) (hNot3 := hNot3)
        (hNot4 := hNot4) (hCard := by simpa [hn]) ⟨e, by rw [he, hS2245566666]; rfl⟩
    else if hS3333666666 : G.degreeSequence = [3, 3, 3, 3, 6, 6, 6, 6, 6, 6] then
      exact exception_stuck_non_regular_card10_seq6666663333 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (hStuck := hStuck) (hNot2 := hNot2) (hNot3 := hNot3)
        (hNot4 := hNot4) (hCard := by simpa [hn]) ⟨e, by rw [he, hS3333666666]; rfl⟩
    else if hS2334666666 : G.degreeSequence = [2, 3, 3, 4, 6, 6, 6, 6, 6, 6] then
      exact exception_stuck_non_regular_card10_seq6666664332 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (hStuck := hStuck) (hNot2 := hNot2) (hNot3 := hNot3)
        (hNot4 := hNot4) (hCard := by simpa [hn]) ⟨e, by rw [he, hS2334666666]; rfl⟩
    else if hS2244666666 : G.degreeSequence = [2, 2, 4, 4, 6, 6, 6, 6, 6, 6] then
      exact exception_stuck_non_regular_card10_seq6666664422 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (hStuck := hStuck) (hNot2 := hNot2) (hNot3 := hNot3)
        (hNot4 := hNot4) (hCard := by simpa [hn]) ⟨e, by rw [he, hS2244666666]; rfl⟩
    else if hS2235666666 : G.degreeSequence = [2, 2, 3, 5, 6, 6, 6, 6, 6, 6] then
      exact exception_stuck_non_regular_card10_seq6666665322 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (hStuck := hStuck) (hNot2 := hNot2) (hNot3 := hNot3)
        (hNot4 := hNot4) (hCard := by simpa [hn]) ⟨e, by rw [he, hS2235666666]; rfl⟩
    else if hS2226666666 : G.degreeSequence = [2, 2, 2, 6, 6, 6, 6, 6, 6, 6] then
      exact exception_stuck_non_regular_card10_seq6666666222 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (hStuck := hStuck) (hNot2 := hNot2) (hNot3 := hNot3)
        (hNot4 := hNot4) (hCard := by simpa [hn]) ⟨e, by rw [he, hS2226666666]; rfl⟩
    else if hS2336666666 : G.degreeSequence = [2, 3, 3, 6, 6, 6, 6, 6, 6, 6] then
      exact exception_stuck_non_regular_card10_seq6666666332 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (hStuck := hStuck) (hNot2 := hNot2) (hNot3 := hNot3)
        (hNot4 := hNot4) (hCard := by simpa [hn]) ⟨e, by rw [he, hS2336666666]; rfl⟩
    else if hS2246666666 : G.degreeSequence = [2, 2, 4, 6, 6, 6, 6, 6, 6, 6] then
      exact exception_stuck_non_regular_card10_seq6666666422 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (hStuck := hStuck) (hNot2 := hNot2) (hNot3 := hNot3)
        (hNot4 := hNot4) (hCard := by simpa [hn]) ⟨e, by rw [he, hS2246666666]; rfl⟩
    else
      sorry
  | 11 =>
    obtain ⟨e, he⟩ := AbsLink.exists_ofFn_eq_reverse (n := 11) G (by omega)
    if hS44444555555 : G.degreeSequence = [4, 4, 4, 4, 4, 5, 5, 5, 5, 5, 5] then
      exact exception_stuck_non_regular_card11_seq55555544444 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (hStuck := hStuck) (hNot2 := hNot2) (hNot3 := hNot3)
        (hNot4 := hNot4) (hCard := by simpa [hn]) ⟨e, by rw [he, hS44444555555]; rfl⟩
    else if hS44444556666 : G.degreeSequence = [4, 4, 4, 4, 4, 5, 5, 6, 6, 6, 6] then
      exact exception_stuck_non_regular_card11_seq66665544444 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (hStuck := hStuck) (hNot2 := hNot2) (hNot3 := hNot3)
        (hNot4 := hNot4) (hCard := by simpa [hn]) ⟨e, by rw [he, hS44444556666]; rfl⟩
    else if hS34445556666 : G.degreeSequence = [3, 4, 4, 4, 5, 5, 5, 6, 6, 6, 6] then
      exact exception_stuck_non_regular_card11_seq66665554443 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (hStuck := hStuck) (hNot2 := hNot2) (hNot3 := hNot3)
        (hNot4 := hNot4) (hCard := by simpa [hn]) ⟨e, by rw [he, hS34445556666]; rfl⟩
    else if hS44444466666 : G.degreeSequence = [4, 4, 4, 4, 4, 4, 6, 6, 6, 6, 6] then
      exact exception_stuck_non_regular_card11_seq66666444444 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (hStuck := hStuck) (hNot2 := hNot2) (hNot3 := hNot3)
        (hNot4 := hNot4) (hCard := by simpa [hn]) ⟨e, by rw [he, hS44444466666]; rfl⟩
    else if hS34444566666 : G.degreeSequence = [3, 4, 4, 4, 4, 5, 6, 6, 6, 6, 6] then
      exact exception_stuck_non_regular_card11_seq66666544443 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (hStuck := hStuck) (hNot2 := hNot2) (hNot3 := hNot3)
        (hNot4 := hNot4) (hCard := by simpa [hn]) ⟨e, by rw [he, hS34444566666]; rfl⟩
    else if hS33445566666 : G.degreeSequence = [3, 3, 4, 4, 5, 5, 6, 6, 6, 6, 6] then
      exact exception_stuck_non_regular_card11_seq66666554433 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (hStuck := hStuck) (hNot2 := hNot2) (hNot3 := hNot3)
        (hNot4 := hNot4) (hCard := by simpa [hn]) ⟨e, by rw [he, hS33445566666]; rfl⟩
    else if hS33444666666 : G.degreeSequence = [3, 3, 4, 4, 4, 6, 6, 6, 6, 6, 6] then
      exact exception_stuck_non_regular_card11_seq66666644433 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (hStuck := hStuck) (hNot2 := hNot2) (hNot3 := hNot3)
        (hNot4 := hNot4) (hCard := by simpa [hn]) ⟨e, by rw [he, hS33444666666]; rfl⟩
    else if hS44444666666 : G.degreeSequence = [4, 4, 4, 4, 4, 6, 6, 6, 6, 6, 6] then
      exact exception_stuck_non_regular_card11_seq66666644444 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (hStuck := hStuck) (hNot2 := hNot2) (hNot3 := hNot3)
        (hNot4 := hNot4) (hCard := by simpa [hn]) ⟨e, by rw [he, hS44444666666]; rfl⟩
    else if hS33345666666 : G.degreeSequence = [3, 3, 3, 4, 5, 6, 6, 6, 6, 6, 6] then
      exact exception_stuck_non_regular_card11_seq66666654333 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (hStuck := hStuck) (hNot2 := hNot2) (hNot3 := hNot3)
        (hNot4 := hNot4) (hCard := by simpa [hn]) ⟨e, by rw [he, hS33345666666]; rfl⟩
    else if hS34445666666 : G.degreeSequence = [3, 4, 4, 4, 5, 6, 6, 6, 6, 6, 6] then
      exact exception_stuck_non_regular_card11_seq66666654443 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (hStuck := hStuck) (hNot2 := hNot2) (hNot3 := hNot3)
        (hNot4 := hNot4) (hCard := by simpa [hn]) ⟨e, by rw [he, hS34445666666]; rfl⟩
    else if hS33336666666 : G.degreeSequence = [3, 3, 3, 3, 6, 6, 6, 6, 6, 6, 6] then
      exact exception_stuck_non_regular_card11_seq66666663333 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (hStuck := hStuck) (hNot2 := hNot2) (hNot3 := hNot3)
        (hNot4 := hNot4) (hCard := by simpa [hn]) ⟨e, by rw [he, hS33336666666]; rfl⟩
    else if hS33446666666 : G.degreeSequence = [3, 3, 4, 4, 6, 6, 6, 6, 6, 6, 6] then
      exact exception_stuck_non_regular_card11_seq66666664433 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (hStuck := hStuck) (hNot2 := hNot2) (hNot3 := hNot3)
        (hNot4 := hNot4) (hCard := by simpa [hn]) ⟨e, by rw [he, hS33446666666]; rfl⟩
    else if hS24446666666 : G.degreeSequence = [2, 4, 4, 4, 6, 6, 6, 6, 6, 6, 6] then
      exact exception_stuck_non_regular_card11_seq66666664442 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (hStuck := hStuck) (hNot2 := hNot2) (hNot3 := hNot3)
        (hNot4 := hNot4) (hCard := by simpa [hn]) ⟨e, by rw [he, hS24446666666]; rfl⟩
    else
      sorry
  | 12 =>
    obtain ⟨e, he⟩ := AbsLink.exists_ofFn_eq_reverse (n := 12) G (by omega)
    if hS555555555566 : G.degreeSequence = [5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 6, 6] then
      exact exception_stuck_non_regular_card12_seq665555555555 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (hStuck := hStuck) (hNot2 := hNot2) (hNot3 := hNot3)
        (hNot4 := hNot4) (hCard := by simpa [hn]) ⟨e, by rw [he, hS555555555566]; rfl⟩
    else if hS455555555666 : G.degreeSequence = [4, 5, 5, 5, 5, 5, 5, 5, 5, 6, 6, 6] then
      exact exception_stuck_non_regular_card12_seq666555555554 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (hStuck := hStuck) (hNot2 := hNot2) (hNot3 := hNot3)
        (hNot4 := hNot4) (hCard := by simpa [hn]) ⟨e, by rw [he, hS455555555666]; rfl⟩
    else if hS445555556666 : G.degreeSequence = [4, 4, 5, 5, 5, 5, 5, 5, 6, 6, 6, 6] then
      exact exception_stuck_non_regular_card12_seq666655555544 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (hStuck := hStuck) (hNot2 := hNot2) (hNot3 := hNot3)
        (hNot4 := hNot4) (hCard := by simpa [hn]) ⟨e, by rw [he, hS445555556666]; rfl⟩
    else if hS555555556666 : G.degreeSequence = [5, 5, 5, 5, 5, 5, 5, 5, 6, 6, 6, 6] then
      exact exception_stuck_non_regular_card12_seq666655555555 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (hStuck := hStuck) (hNot2 := hNot2) (hNot3 := hNot3)
        (hNot4 := hNot4) (hCard := by simpa [hn]) ⟨e, by rw [he, hS555555556666]; rfl⟩
    else if hS444555566666 : G.degreeSequence = [4, 4, 4, 5, 5, 5, 5, 6, 6, 6, 6, 6] then
      exact exception_stuck_non_regular_card12_seq666665555444 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (hStuck := hStuck) (hNot2 := hNot2) (hNot3 := hNot3)
        (hNot4 := hNot4) (hCard := by simpa [hn]) ⟨e, by rw [he, hS444555566666]; rfl⟩
    else if hS455555566666 : G.degreeSequence = [4, 5, 5, 5, 5, 5, 5, 6, 6, 6, 6, 6] then
      exact exception_stuck_non_regular_card12_seq666665555554 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (hStuck := hStuck) (hNot2 := hNot2) (hNot3 := hNot3)
        (hNot4 := hNot4) (hCard := by simpa [hn]) ⟨e, by rw [he, hS455555566666]; rfl⟩
    else if hS444455666666 : G.degreeSequence = [4, 4, 4, 4, 5, 5, 6, 6, 6, 6, 6, 6] then
      exact exception_stuck_non_regular_card12_seq666666554444 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (hStuck := hStuck) (hNot2 := hNot2) (hNot3 := hNot3)
        (hNot4 := hNot4) (hCard := by simpa [hn]) ⟨e, by rw [he, hS444455666666]; rfl⟩
    else if hS445555666666 : G.degreeSequence = [4, 4, 5, 5, 5, 5, 6, 6, 6, 6, 6, 6] then
      exact exception_stuck_non_regular_card12_seq666666555544 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (hStuck := hStuck) (hNot2 := hNot2) (hNot3 := hNot3)
        (hNot4 := hNot4) (hCard := by simpa [hn]) ⟨e, by rw [he, hS445555666666]; rfl⟩
    else if hS355555666666 : G.degreeSequence = [3, 5, 5, 5, 5, 5, 6, 6, 6, 6, 6, 6] then
      exact exception_stuck_non_regular_card12_seq666666555553 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (hStuck := hStuck) (hNot2 := hNot2) (hNot3 := hNot3)
        (hNot4 := hNot4) (hCard := by simpa [hn]) ⟨e, by rw [he, hS355555666666]; rfl⟩
    else if hS555555666666 : G.degreeSequence = [5, 5, 5, 5, 5, 5, 6, 6, 6, 6, 6, 6] then
      exact exception_stuck_non_regular_card12_seq666666555555 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (hStuck := hStuck) (hNot2 := hNot2) (hNot3 := hNot3)
        (hNot4 := hNot4) (hCard := by simpa [hn]) ⟨e, by rw [he, hS555555666666]; rfl⟩
    else if hS444446666666 : G.degreeSequence = [4, 4, 4, 4, 4, 6, 6, 6, 6, 6, 6, 6] then
      exact exception_stuck_non_regular_card12_seq666666644444 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (hStuck := hStuck) (hNot2 := hNot2) (hNot3 := hNot3)
        (hNot4 := hNot4) (hCard := by simpa [hn]) ⟨e, by rw [he, hS444446666666]; rfl⟩
    else if hS444556666666 : G.degreeSequence = [4, 4, 4, 5, 5, 6, 6, 6, 6, 6, 6, 6] then
      exact exception_stuck_non_regular_card12_seq666666655444 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (hStuck := hStuck) (hNot2 := hNot2) (hNot3 := hNot3)
        (hNot4 := hNot4) (hCard := by simpa [hn]) ⟨e, by rw [he, hS444556666666]; rfl⟩
    else if hS345556666666 : G.degreeSequence = [3, 4, 5, 5, 5, 6, 6, 6, 6, 6, 6, 6] then
      exact exception_stuck_non_regular_card12_seq666666655543 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (hStuck := hStuck) (hNot2 := hNot2) (hNot3 := hNot3)
        (hNot4 := hNot4) (hCard := by simpa [hn]) ⟨e, by rw [he, hS345556666666]; rfl⟩
    else if hS455556666666 : G.degreeSequence = [4, 5, 5, 5, 5, 6, 6, 6, 6, 6, 6, 6] then
      exact exception_stuck_non_regular_card12_seq666666655554 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (hStuck := hStuck) (hNot2 := hNot2) (hNot3 := hNot3)
        (hNot4 := hNot4) (hCard := by simpa [hn]) ⟨e, by rw [he, hS455556666666]; rfl⟩
    else
      sorry
  | _ => sorry

theorem exception_not_hOutOK
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (connected : G.Connected)
    (hCard : Fintype.card V ≤ 12)
    (hResidue : residue G = 2)
    (hMaxDeg : G.maxDegree ≤ 6)
    (t : ℕ)
    (S : Finset V) (hS : ∀ v, v ∈ S ↔ t ≤ G.degree v)
    (hBig : Fintype.card V - 1 ≤ 2 * (card S - 1) ∧ 1 ≤ card S)
    (hNotOutOK : ¬ (∀ v : V, ¬ t ≤ G.degree v →
            Fintype.card V - 1 - (card S - 1) ≤ G.degree v))
    : ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  have hCard12 : Fintype.card V ≤ 12 := by assumption
  match hn : Fintype.card V with
  | 4 =>
    obtain ⟨e, he⟩ := AbsLink.exists_ofFn_eq_reverse (n := 4) G (by omega)
    if hS1122 : G.degreeSequence = [1, 1, 2, 2] then
      exact exception_not_hOutOK_card4_seq2211 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS) (hBig := hBig) (hNotOutOK := hNotOutOK)
        (hCard := by simpa [hn]) ⟨e, by rw [he, hS1122]; rfl⟩
    else
      sorry
  | 5 =>
    obtain ⟨e, he⟩ := AbsLink.exists_ofFn_eq_reverse (n := 5) G (by omega)
    if hS11222 : G.degreeSequence = [1, 1, 2, 2, 2] then
      exact exception_not_hOutOK_card5_seq22211 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS) (hBig := hBig) (hNotOutOK := hNotOutOK)
        (hCard := by simpa [hn]) ⟨e, by rw [he, hS11222]; rfl⟩
    else
      sorry
  | 6 =>
    obtain ⟨e, he⟩ := AbsLink.exists_ofFn_eq_reverse (n := 6) G (by omega)
    if hS222233 : G.degreeSequence = [2, 2, 2, 2, 3, 3] then
      exact exception_not_hOutOK_card6_seq332222 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS) (hBig := hBig) (hNotOutOK := hNotOutOK)
        (hCard := by simpa [hn]) ⟨e, by rw [he, hS222233]; rfl⟩
    else if hS122333 : G.degreeSequence = [1, 2, 2, 3, 3, 3] then
      exact exception_not_hOutOK_card6_seq333221 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS) (hBig := hBig) (hNotOutOK := hNotOutOK)
        (hCard := by simpa [hn]) ⟨e, by rw [he, hS122333]; rfl⟩
    else if hS113333 : G.degreeSequence = [1, 1, 3, 3, 3, 3] then
      exact exception_not_hOutOK_card6_seq333311 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS) (hBig := hBig) (hNotOutOK := hNotOutOK)
        (hCard := by simpa [hn]) ⟨e, by rw [he, hS113333]; rfl⟩
    else if hS222334 : G.degreeSequence = [2, 2, 2, 3, 3, 4] then
      exact exception_not_hOutOK_card6_seq433222 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS) (hBig := hBig) (hNotOutOK := hNotOutOK)
        (hCard := by simpa [hn]) ⟨e, by rw [he, hS222334]; rfl⟩
    else if hS123334 : G.degreeSequence = [1, 2, 3, 3, 3, 4] then
      exact exception_not_hOutOK_card6_seq433321 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS) (hBig := hBig) (hNotOutOK := hNotOutOK)
        (hCard := by simpa [hn]) ⟨e, by rw [he, hS123334]; rfl⟩
    else
      sorry
  | 7 =>
    obtain ⟨e, he⟩ := AbsLink.exists_ofFn_eq_reverse (n := 7) G (by omega)
    if hS2223333 : G.degreeSequence = [2, 2, 2, 3, 3, 3, 3] then
      exact exception_not_hOutOK_card7_seq3333222 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS) (hBig := hBig) (hNotOutOK := hNotOutOK)
        (hCard := by simpa [hn]) ⟨e, by rw [he, hS2223333]; rfl⟩
    else if hS2224444 : G.degreeSequence = [2, 2, 2, 4, 4, 4, 4] then
      exact exception_not_hOutOK_card7_seq4444222 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS) (hBig := hBig) (hNotOutOK := hNotOutOK)
        (hCard := by simpa [hn]) ⟨e, by rw [he, hS2224444]; rfl⟩
    else if hS1234444 : G.degreeSequence = [1, 2, 3, 4, 4, 4, 4] then
      exact exception_not_hOutOK_card7_seq4444321 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS) (hBig := hBig) (hNotOutOK := hNotOutOK)
        (hCard := by simpa [hn]) ⟨e, by rw [he, hS1234444]; rfl⟩
    else if hS1144444 : G.degreeSequence = [1, 1, 4, 4, 4, 4, 4] then
      exact exception_not_hOutOK_card7_seq4444411 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS) (hBig := hBig) (hNotOutOK := hNotOutOK)
        (hCard := by simpa [hn]) ⟨e, by rw [he, hS1144444]; rfl⟩
    else if hS1244445 : G.degreeSequence = [1, 2, 4, 4, 4, 4, 5] then
      exact exception_not_hOutOK_card7_seq5444421 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS) (hBig := hBig) (hNotOutOK := hNotOutOK)
        (hCard := by simpa [hn]) ⟨e, by rw [he, hS1244445]; rfl⟩
    else
      sorry
  | 8 =>
    obtain ⟨e, he⟩ := AbsLink.exists_ofFn_eq_reverse (n := 8) G (by omega)
    if hS33333344 : G.degreeSequence = [3, 3, 3, 3, 3, 3, 4, 4] then
      exact exception_not_hOutOK_card8_seq44333333 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS) (hBig := hBig) (hNotOutOK := hNotOutOK)
        (hCard := by simpa [hn]) ⟨e, by rw [he, hS33333344]; rfl⟩
    else if hS23333444 : G.degreeSequence = [2, 3, 3, 3, 3, 4, 4, 4] then
      exact exception_not_hOutOK_card8_seq44433332 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS) (hBig := hBig) (hNotOutOK := hNotOutOK)
        (hCard := by simpa [hn]) ⟨e, by rw [he, hS23333444]; rfl⟩
    else if hS22334444 : G.degreeSequence = [2, 2, 3, 3, 4, 4, 4, 4] then
      exact exception_not_hOutOK_card8_seq44443322 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS) (hBig := hBig) (hNotOutOK := hNotOutOK)
        (hCard := by simpa [hn]) ⟨e, by rw [he, hS22334444]; rfl⟩
    else if hS33334444 : G.degreeSequence = [3, 3, 3, 3, 4, 4, 4, 4] then
      exact exception_not_hOutOK_card8_seq44443333 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS) (hBig := hBig) (hNotOutOK := hNotOutOK)
        (hCard := by simpa [hn]) ⟨e, by rw [he, hS33334444]; rfl⟩
    else if hS22244444 : G.degreeSequence = [2, 2, 2, 4, 4, 4, 4, 4] then
      exact exception_not_hOutOK_card8_seq44444222 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS) (hBig := hBig) (hNotOutOK := hNotOutOK)
        (hCard := by simpa [hn]) ⟨e, by rw [he, hS22244444]; rfl⟩
    else if hS23344444 : G.degreeSequence = [2, 3, 3, 4, 4, 4, 4, 4] then
      exact exception_not_hOutOK_card8_seq44444332 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS) (hBig := hBig) (hNotOutOK := hNotOutOK)
        (hCard := by simpa [hn]) ⟨e, by rw [he, hS23344444]; rfl⟩
    else if hS33333445 : G.degreeSequence = [3, 3, 3, 3, 3, 4, 4, 5] then
      exact exception_not_hOutOK_card8_seq54433333 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS) (hBig := hBig) (hNotOutOK := hNotOutOK)
        (hCard := by simpa [hn]) ⟨e, by rw [he, hS33333445]; rfl⟩
    else if hS23334445 : G.degreeSequence = [2, 3, 3, 3, 4, 4, 4, 5] then
      exact exception_not_hOutOK_card8_seq54443332 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS) (hBig := hBig) (hNotOutOK := hNotOutOK)
        (hCard := by simpa [hn]) ⟨e, by rw [he, hS23334445]; rfl⟩
    else if hS22344445 : G.degreeSequence = [2, 2, 3, 4, 4, 4, 4, 5] then
      exact exception_not_hOutOK_card8_seq54444322 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS) (hBig := hBig) (hNotOutOK := hNotOutOK)
        (hCard := by simpa [hn]) ⟨e, by rw [he, hS22344445]; rfl⟩
    else if hS33334455 : G.degreeSequence = [3, 3, 3, 3, 4, 4, 5, 5] then
      exact exception_not_hOutOK_card8_seq55443333 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS) (hBig := hBig) (hNotOutOK := hNotOutOK)
        (hCard := by simpa [hn]) ⟨e, by rw [he, hS33334455]; rfl⟩
    else if hS23344455 : G.degreeSequence = [2, 3, 3, 4, 4, 4, 5, 5] then
      exact exception_not_hOutOK_card8_seq55444332 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS) (hBig := hBig) (hNotOutOK := hNotOutOK)
        (hCard := by simpa [hn]) ⟨e, by rw [he, hS23344455]; rfl⟩
    else if hS33335555 : G.degreeSequence = [3, 3, 3, 3, 5, 5, 5, 5] then
      exact exception_not_hOutOK_card8_seq55553333 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS) (hBig := hBig) (hNotOutOK := hNotOutOK)
        (hCard := by simpa [hn]) ⟨e, by rw [he, hS33335555]; rfl⟩
    else if hS13445555 : G.degreeSequence = [1, 3, 4, 4, 5, 5, 5, 5] then
      exact exception_not_hOutOK_card8_seq55554431 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS) (hBig := hBig) (hNotOutOK := hNotOutOK)
        (hCard := by simpa [hn]) ⟨e, by rw [he, hS13445555]; rfl⟩
    else if hS22355555 : G.degreeSequence = [2, 2, 3, 5, 5, 5, 5, 5] then
      exact exception_not_hOutOK_card8_seq55555322 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS) (hBig := hBig) (hNotOutOK := hNotOutOK)
        (hCard := by simpa [hn]) ⟨e, by rw [he, hS22355555]; rfl⟩
    else if hS13355555 : G.degreeSequence = [1, 3, 3, 5, 5, 5, 5, 5] then
      exact exception_not_hOutOK_card8_seq55555331 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS) (hBig := hBig) (hNotOutOK := hNotOutOK)
        (hCard := by simpa [hn]) ⟨e, by rw [he, hS13355555]; rfl⟩
    else if hS12455555 : G.degreeSequence = [1, 2, 4, 5, 5, 5, 5, 5] then
      exact exception_not_hOutOK_card8_seq55555421 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS) (hBig := hBig) (hNotOutOK := hNotOutOK)
        (hCard := by simpa [hn]) ⟨e, by rw [he, hS12455555]; rfl⟩
    else if hS11555555 : G.degreeSequence = [1, 1, 5, 5, 5, 5, 5, 5] then
      exact exception_not_hOutOK_card8_seq55555511 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS) (hBig := hBig) (hNotOutOK := hNotOutOK)
        (hCard := by simpa [hn]) ⟨e, by rw [he, hS11555555]; rfl⟩
    else if hS13555555 : G.degreeSequence = [1, 3, 5, 5, 5, 5, 5, 5] then
      exact exception_not_hOutOK_card8_seq55555531 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS) (hBig := hBig) (hNotOutOK := hNotOutOK)
        (hCard := by simpa [hn]) ⟨e, by rw [he, hS13555555]; rfl⟩
    else if hS33334446 : G.degreeSequence = [3, 3, 3, 3, 4, 4, 4, 6] then
      exact exception_not_hOutOK_card8_seq64443333 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS) (hBig := hBig) (hNotOutOK := hNotOutOK)
        (hCard := by simpa [hn]) ⟨e, by rw [he, hS33334446]; rfl⟩
    else if hS23344446 : G.degreeSequence = [2, 3, 3, 4, 4, 4, 4, 6] then
      exact exception_not_hOutOK_card8_seq64444332 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS) (hBig := hBig) (hNotOutOK := hNotOutOK)
        (hCard := by simpa [hn]) ⟨e, by rw [he, hS23344446]; rfl⟩
    else if hS13455556 : G.degreeSequence = [1, 3, 4, 5, 5, 5, 5, 6] then
      exact exception_not_hOutOK_card8_seq65555431 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS) (hBig := hBig) (hNotOutOK := hNotOutOK)
        (hCard := by simpa [hn]) ⟨e, by rw [he, hS13455556]; rfl⟩
    else if hS12555556 : G.degreeSequence = [1, 2, 5, 5, 5, 5, 5, 6] then
      exact exception_not_hOutOK_card8_seq65555521 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS) (hBig := hBig) (hNotOutOK := hNotOutOK)
        (hCard := by simpa [hn]) ⟨e, by rw [he, hS12555556]; rfl⟩
    else if hS13555566 : G.degreeSequence = [1, 3, 5, 5, 5, 5, 6, 6] then
      exact exception_not_hOutOK_card8_seq66555531 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS) (hBig := hBig) (hNotOutOK := hNotOutOK)
        (hCard := by simpa [hn]) ⟨e, by rw [he, hS13555566]; rfl⟩
    else
      sorry
  | 9 =>
    obtain ⟨e, he⟩ := AbsLink.exists_ofFn_eq_reverse (n := 9) G (by omega)
    if hS333344444 : G.degreeSequence = [3, 3, 3, 3, 4, 4, 4, 4, 4] then
      exact exception_not_hOutOK_card9_seq444443333 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS) (hBig := hBig) (hNotOutOK := hNotOutOK)
        (hCard := by simpa [hn]) ⟨e, by rw [he, hS333344444]; rfl⟩
    else if hS333345555 : G.degreeSequence = [3, 3, 3, 3, 4, 5, 5, 5, 5] then
      exact exception_not_hOutOK_card9_seq555543333 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS) (hBig := hBig) (hNotOutOK := hNotOutOK)
        (hCard := by simpa [hn]) ⟨e, by rw [he, hS333345555]; rfl⟩
    else if hS233445555 : G.degreeSequence = [2, 3, 3, 4, 4, 5, 5, 5, 5] then
      exact exception_not_hOutOK_card9_seq555544332 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS) (hBig := hBig) (hNotOutOK := hNotOutOK)
        (hCard := by simpa [hn]) ⟨e, by rw [he, hS233445555]; rfl⟩
    else if hS233355555 : G.degreeSequence = [2, 3, 3, 3, 5, 5, 5, 5, 5] then
      exact exception_not_hOutOK_card9_seq555553332 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS) (hBig := hBig) (hNotOutOK := hNotOutOK)
        (hCard := by simpa [hn]) ⟨e, by rw [he, hS233355555]; rfl⟩
    else if hS223455555 : G.degreeSequence = [2, 2, 3, 4, 5, 5, 5, 5, 5] then
      exact exception_not_hOutOK_card9_seq555554322 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS) (hBig := hBig) (hNotOutOK := hNotOutOK)
        (hCard := by simpa [hn]) ⟨e, by rw [he, hS223455555]; rfl⟩
    else if hS222555555 : G.degreeSequence = [2, 2, 2, 5, 5, 5, 5, 5, 5] then
      exact exception_not_hOutOK_card9_seq555555222 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS) (hBig := hBig) (hNotOutOK := hNotOutOK)
        (hCard := by simpa [hn]) ⟨e, by rw [he, hS222555555]; rfl⟩
    else if hS233555555 : G.degreeSequence = [2, 3, 3, 5, 5, 5, 5, 5, 5] then
      exact exception_not_hOutOK_card9_seq555555332 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS) (hBig := hBig) (hNotOutOK := hNotOutOK)
        (hCard := by simpa [hn]) ⟨e, by rw [he, hS233555555]; rfl⟩
    else if hS333355556 : G.degreeSequence = [3, 3, 3, 3, 5, 5, 5, 5, 6] then
      exact exception_not_hOutOK_card9_seq655553333 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS) (hBig := hBig) (hNotOutOK := hNotOutOK)
        (hCard := by simpa [hn]) ⟨e, by rw [he, hS333355556]; rfl⟩
    else if hS233455556 : G.degreeSequence = [2, 3, 3, 4, 5, 5, 5, 5, 6] then
      exact exception_not_hOutOK_card9_seq655554332 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS) (hBig := hBig) (hNotOutOK := hNotOutOK)
        (hCard := by simpa [hn]) ⟨e, by rw [he, hS233455556]; rfl⟩
    else if hS223555556 : G.degreeSequence = [2, 2, 3, 5, 5, 5, 5, 5, 6] then
      exact exception_not_hOutOK_card9_seq655555322 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS) (hBig := hBig) (hNotOutOK := hNotOutOK)
        (hCard := by simpa [hn]) ⟨e, by rw [he, hS223555556]; rfl⟩
    else if hS233555566 : G.degreeSequence = [2, 3, 3, 5, 5, 5, 5, 6, 6] then
      exact exception_not_hOutOK_card9_seq665555332 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS) (hBig := hBig) (hNotOutOK := hNotOutOK)
        (hCard := by simpa [hn]) ⟨e, by rw [he, hS233555566]; rfl⟩
    else if hS135566666 : G.degreeSequence = [1, 3, 5, 5, 6, 6, 6, 6, 6] then
      exact exception_not_hOutOK_card9_seq666665531 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS) (hBig := hBig) (hNotOutOK := hNotOutOK)
        (hCard := by simpa [hn]) ⟨e, by rw [he, hS135566666]; rfl⟩
    else if hS134666666 : G.degreeSequence = [1, 3, 4, 6, 6, 6, 6, 6, 6] then
      exact exception_not_hOutOK_card9_seq666666431 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS) (hBig := hBig) (hNotOutOK := hNotOutOK)
        (hCard := by simpa [hn]) ⟨e, by rw [he, hS134666666]; rfl⟩
    else if hS125666666 : G.degreeSequence = [1, 2, 5, 6, 6, 6, 6, 6, 6] then
      exact exception_not_hOutOK_card9_seq666666521 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS) (hBig := hBig) (hNotOutOK := hNotOutOK)
        (hCard := by simpa [hn]) ⟨e, by rw [he, hS125666666]; rfl⟩
    else if hS116666666 : G.degreeSequence = [1, 1, 6, 6, 6, 6, 6, 6, 6] then
      exact exception_not_hOutOK_card9_seq666666611 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS) (hBig := hBig) (hNotOutOK := hNotOutOK)
        (hCard := by simpa [hn]) ⟨e, by rw [he, hS116666666]; rfl⟩
    else if hS136666666 : G.degreeSequence = [1, 3, 6, 6, 6, 6, 6, 6, 6] then
      exact exception_not_hOutOK_card9_seq666666631 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS) (hBig := hBig) (hNotOutOK := hNotOutOK)
        (hCard := by simpa [hn]) ⟨e, by rw [he, hS136666666]; rfl⟩
    else
      sorry
  | 10 =>
    obtain ⟨e, he⟩ := AbsLink.exists_ofFn_eq_reverse (n := 10) G (by omega)
    if hS4444444455 : G.degreeSequence = [4, 4, 4, 4, 4, 4, 4, 4, 5, 5] then
      exact exception_not_hOutOK_card10_seq5544444444 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS) (hBig := hBig) (hNotOutOK := hNotOutOK)
        (hCard := by simpa [hn]) ⟨e, by rw [he, hS4444444455]; rfl⟩
    else if hS3444444555 : G.degreeSequence = [3, 4, 4, 4, 4, 4, 4, 5, 5, 5] then
      exact exception_not_hOutOK_card10_seq5554444443 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS) (hBig := hBig) (hNotOutOK := hNotOutOK)
        (hCard := by simpa [hn]) ⟨e, by rw [he, hS3444444555]; rfl⟩
    else if hS3344445555 : G.degreeSequence = [3, 3, 4, 4, 4, 4, 5, 5, 5, 5] then
      exact exception_not_hOutOK_card10_seq5555444433 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS) (hBig := hBig) (hNotOutOK := hNotOutOK)
        (hCard := by simpa [hn]) ⟨e, by rw [he, hS3344445555]; rfl⟩
    else if hS4444445555 : G.degreeSequence = [4, 4, 4, 4, 4, 4, 5, 5, 5, 5] then
      exact exception_not_hOutOK_card10_seq5555444444 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS) (hBig := hBig) (hNotOutOK := hNotOutOK)
        (hCard := by simpa [hn]) ⟨e, by rw [he, hS4444445555]; rfl⟩
    else if hS3334455555 : G.degreeSequence = [3, 3, 3, 4, 4, 5, 5, 5, 5, 5] then
      exact exception_not_hOutOK_card10_seq5555544333 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS) (hBig := hBig) (hNotOutOK := hNotOutOK)
        (hCard := by simpa [hn]) ⟨e, by rw [he, hS3334455555]; rfl⟩
    else if hS3444455555 : G.degreeSequence = [3, 4, 4, 4, 4, 5, 5, 5, 5, 5] then
      exact exception_not_hOutOK_card10_seq5555544443 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS) (hBig := hBig) (hNotOutOK := hNotOutOK)
        (hCard := by simpa [hn]) ⟨e, by rw [he, hS3444455555]; rfl⟩
    else if hS3333555555 : G.degreeSequence = [3, 3, 3, 3, 5, 5, 5, 5, 5, 5] then
      exact exception_not_hOutOK_card10_seq5555553333 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS) (hBig := hBig) (hNotOutOK := hNotOutOK)
        (hCard := by simpa [hn]) ⟨e, by rw [he, hS3333555555]; rfl⟩
    else if hS3344555555 : G.degreeSequence = [3, 3, 4, 4, 5, 5, 5, 5, 5, 5] then
      exact exception_not_hOutOK_card10_seq5555554433 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS) (hBig := hBig) (hNotOutOK := hNotOutOK)
        (hCard := by simpa [hn]) ⟨e, by rw [he, hS3344555555]; rfl⟩
    else if hS2444555555 : G.degreeSequence = [2, 4, 4, 4, 5, 5, 5, 5, 5, 5] then
      exact exception_not_hOutOK_card10_seq5555554442 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS) (hBig := hBig) (hNotOutOK := hNotOutOK)
        (hCard := by simpa [hn]) ⟨e, by rw [he, hS2444555555]; rfl⟩
    else if hS4444444556 : G.degreeSequence = [4, 4, 4, 4, 4, 4, 4, 5, 5, 6] then
      exact exception_not_hOutOK_card10_seq6554444444 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS) (hBig := hBig) (hNotOutOK := hNotOutOK)
        (hCard := by simpa [hn]) ⟨e, by rw [he, hS4444444556]; rfl⟩
    else if hS3444445556 : G.degreeSequence = [3, 4, 4, 4, 4, 4, 5, 5, 5, 6] then
      exact exception_not_hOutOK_card10_seq6555444443 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS) (hBig := hBig) (hNotOutOK := hNotOutOK)
        (hCard := by simpa [hn]) ⟨e, by rw [he, hS3444445556]; rfl⟩
    else if hS3344455556 : G.degreeSequence = [3, 3, 4, 4, 4, 5, 5, 5, 5, 6] then
      exact exception_not_hOutOK_card10_seq6555544433 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS) (hBig := hBig) (hNotOutOK := hNotOutOK)
        (hCard := by simpa [hn]) ⟨e, by rw [he, hS3344455556]; rfl⟩
    else if hS4444455556 : G.degreeSequence = [4, 4, 4, 4, 4, 5, 5, 5, 5, 6] then
      exact exception_not_hOutOK_card10_seq6555544444 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS) (hBig := hBig) (hNotOutOK := hNotOutOK)
        (hCard := by simpa [hn]) ⟨e, by rw [he, hS4444455556]; rfl⟩
    else if hS3334555556 : G.degreeSequence = [3, 3, 3, 4, 5, 5, 5, 5, 5, 6] then
      exact exception_not_hOutOK_card10_seq6555554333 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS) (hBig := hBig) (hNotOutOK := hNotOutOK)
        (hCard := by simpa [hn]) ⟨e, by rw [he, hS3334555556]; rfl⟩
    else if hS3444555556 : G.degreeSequence = [3, 4, 4, 4, 5, 5, 5, 5, 5, 6] then
      exact exception_not_hOutOK_card10_seq6555554443 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS) (hBig := hBig) (hNotOutOK := hNotOutOK)
        (hCard := by simpa [hn]) ⟨e, by rw [he, hS3444555556]; rfl⟩
    else if hS4444445566 : G.degreeSequence = [4, 4, 4, 4, 4, 4, 5, 5, 6, 6] then
      exact exception_not_hOutOK_card10_seq6655444444 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS) (hBig := hBig) (hNotOutOK := hNotOutOK)
        (hCard := by simpa [hn]) ⟨e, by rw [he, hS4444445566]; rfl⟩
    else if hS3444455566 : G.degreeSequence = [3, 4, 4, 4, 4, 5, 5, 5, 6, 6] then
      exact exception_not_hOutOK_card10_seq6655544443 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS) (hBig := hBig) (hNotOutOK := hNotOutOK)
        (hCard := by simpa [hn]) ⟨e, by rw [he, hS3444455566]; rfl⟩
    else if hS3344555566 : G.degreeSequence = [3, 3, 4, 4, 5, 5, 5, 5, 6, 6] then
      exact exception_not_hOutOK_card10_seq6655554433 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS) (hBig := hBig) (hNotOutOK := hNotOutOK)
        (hCard := by simpa [hn]) ⟨e, by rw [he, hS3344555566]; rfl⟩
    else if hS4444455666 : G.degreeSequence = [4, 4, 4, 4, 4, 5, 5, 6, 6, 6] then
      exact exception_not_hOutOK_card10_seq6665544444 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS) (hBig := hBig) (hNotOutOK := hNotOutOK)
        (hCard := by simpa [hn]) ⟨e, by rw [he, hS4444455666]; rfl⟩
    else if hS3444555666 : G.degreeSequence = [3, 4, 4, 4, 5, 5, 5, 6, 6, 6] then
      exact exception_not_hOutOK_card10_seq6665554443 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS) (hBig := hBig) (hNotOutOK := hNotOutOK)
        (hCard := by simpa [hn]) ⟨e, by rw [he, hS3444555666]; rfl⟩
    else if hS3444456666 : G.degreeSequence = [3, 4, 4, 4, 4, 5, 6, 6, 6, 6] then
      exact exception_not_hOutOK_card10_seq6666544443 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS) (hBig := hBig) (hNotOutOK := hNotOutOK)
        (hCard := by simpa [hn]) ⟨e, by rw [he, hS3444456666]; rfl⟩
    else if hS3344556666 : G.degreeSequence = [3, 3, 4, 4, 5, 5, 6, 6, 6, 6] then
      exact exception_not_hOutOK_card10_seq6666554433 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS) (hBig := hBig) (hNotOutOK := hNotOutOK)
        (hCard := by simpa [hn]) ⟨e, by rw [he, hS3344556666]; rfl⟩
    else if hS2444556666 : G.degreeSequence = [2, 4, 4, 4, 5, 5, 6, 6, 6, 6] then
      exact exception_not_hOutOK_card10_seq6666554442 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS) (hBig := hBig) (hNotOutOK := hNotOutOK)
        (hCard := by simpa [hn]) ⟨e, by rw [he, hS2444556666]; rfl⟩
    else if hS3344466666 : G.degreeSequence = [3, 3, 4, 4, 4, 6, 6, 6, 6, 6] then
      exact exception_not_hOutOK_card10_seq6666644433 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS) (hBig := hBig) (hNotOutOK := hNotOutOK)
        (hCard := by simpa [hn]) ⟨e, by rw [he, hS3344466666]; rfl⟩
    else if hS2444466666 : G.degreeSequence = [2, 4, 4, 4, 4, 6, 6, 6, 6, 6] then
      exact exception_not_hOutOK_card10_seq6666644442 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS) (hBig := hBig) (hNotOutOK := hNotOutOK)
        (hCard := by simpa [hn]) ⟨e, by rw [he, hS2444466666]; rfl⟩
    else if hS4444466666 : G.degreeSequence = [4, 4, 4, 4, 4, 6, 6, 6, 6, 6] then
      exact exception_not_hOutOK_card10_seq6666644444 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS) (hBig := hBig) (hNotOutOK := hNotOutOK)
        (hCard := by simpa [hn]) ⟨e, by rw [he, hS4444466666]; rfl⟩
    else if hS3334566666 : G.degreeSequence = [3, 3, 3, 4, 5, 6, 6, 6, 6, 6] then
      exact exception_not_hOutOK_card10_seq6666654333 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS) (hBig := hBig) (hNotOutOK := hNotOutOK)
        (hCard := by simpa [hn]) ⟨e, by rw [he, hS3334566666]; rfl⟩
    else if hS2335566666 : G.degreeSequence = [2, 3, 3, 5, 5, 6, 6, 6, 6, 6] then
      exact exception_not_hOutOK_card10_seq6666655332 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS) (hBig := hBig) (hNotOutOK := hNotOutOK)
        (hCard := by simpa [hn]) ⟨e, by rw [he, hS2335566666]; rfl⟩
    else if hS2245566666 : G.degreeSequence = [2, 2, 4, 5, 5, 6, 6, 6, 6, 6] then
      exact exception_not_hOutOK_card10_seq6666655422 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS) (hBig := hBig) (hNotOutOK := hNotOutOK)
        (hCard := by simpa [hn]) ⟨e, by rw [he, hS2245566666]; rfl⟩
    else if hS3333666666 : G.degreeSequence = [3, 3, 3, 3, 6, 6, 6, 6, 6, 6] then
      exact exception_not_hOutOK_card10_seq6666663333 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS) (hBig := hBig) (hNotOutOK := hNotOutOK)
        (hCard := by simpa [hn]) ⟨e, by rw [he, hS3333666666]; rfl⟩
    else if hS2334666666 : G.degreeSequence = [2, 3, 3, 4, 6, 6, 6, 6, 6, 6] then
      exact exception_not_hOutOK_card10_seq6666664332 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS) (hBig := hBig) (hNotOutOK := hNotOutOK)
        (hCard := by simpa [hn]) ⟨e, by rw [he, hS2334666666]; rfl⟩
    else if hS2244666666 : G.degreeSequence = [2, 2, 4, 4, 6, 6, 6, 6, 6, 6] then
      exact exception_not_hOutOK_card10_seq6666664422 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS) (hBig := hBig) (hNotOutOK := hNotOutOK)
        (hCard := by simpa [hn]) ⟨e, by rw [he, hS2244666666]; rfl⟩
    else if hS2235666666 : G.degreeSequence = [2, 2, 3, 5, 6, 6, 6, 6, 6, 6] then
      exact exception_not_hOutOK_card10_seq6666665322 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS) (hBig := hBig) (hNotOutOK := hNotOutOK)
        (hCard := by simpa [hn]) ⟨e, by rw [he, hS2235666666]; rfl⟩
    else if hS2226666666 : G.degreeSequence = [2, 2, 2, 6, 6, 6, 6, 6, 6, 6] then
      exact exception_not_hOutOK_card10_seq6666666222 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS) (hBig := hBig) (hNotOutOK := hNotOutOK)
        (hCard := by simpa [hn]) ⟨e, by rw [he, hS2226666666]; rfl⟩
    else if hS2336666666 : G.degreeSequence = [2, 3, 3, 6, 6, 6, 6, 6, 6, 6] then
      exact exception_not_hOutOK_card10_seq6666666332 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS) (hBig := hBig) (hNotOutOK := hNotOutOK)
        (hCard := by simpa [hn]) ⟨e, by rw [he, hS2336666666]; rfl⟩
    else if hS2246666666 : G.degreeSequence = [2, 2, 4, 6, 6, 6, 6, 6, 6, 6] then
      exact exception_not_hOutOK_card10_seq6666666422 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS) (hBig := hBig) (hNotOutOK := hNotOutOK)
        (hCard := by simpa [hn]) ⟨e, by rw [he, hS2246666666]; rfl⟩
    else
      sorry
  | 11 =>
    obtain ⟨e, he⟩ := AbsLink.exists_ofFn_eq_reverse (n := 11) G (by omega)
    if hS44444555555 : G.degreeSequence = [4, 4, 4, 4, 4, 5, 5, 5, 5, 5, 5] then
      exact exception_not_hOutOK_card11_seq55555544444 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS) (hBig := hBig) (hNotOutOK := hNotOutOK)
        (hCard := by simpa [hn]) ⟨e, by rw [he, hS44444555555]; rfl⟩
    else if hS44444556666 : G.degreeSequence = [4, 4, 4, 4, 4, 5, 5, 6, 6, 6, 6] then
      exact exception_not_hOutOK_card11_seq66665544444 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS) (hBig := hBig) (hNotOutOK := hNotOutOK)
        (hCard := by simpa [hn]) ⟨e, by rw [he, hS44444556666]; rfl⟩
    else if hS34445556666 : G.degreeSequence = [3, 4, 4, 4, 5, 5, 5, 6, 6, 6, 6] then
      exact exception_not_hOutOK_card11_seq66665554443 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS) (hBig := hBig) (hNotOutOK := hNotOutOK)
        (hCard := by simpa [hn]) ⟨e, by rw [he, hS34445556666]; rfl⟩
    else if hS44444466666 : G.degreeSequence = [4, 4, 4, 4, 4, 4, 6, 6, 6, 6, 6] then
      exact exception_not_hOutOK_card11_seq66666444444 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS) (hBig := hBig) (hNotOutOK := hNotOutOK)
        (hCard := by simpa [hn]) ⟨e, by rw [he, hS44444466666]; rfl⟩
    else if hS34444566666 : G.degreeSequence = [3, 4, 4, 4, 4, 5, 6, 6, 6, 6, 6] then
      exact exception_not_hOutOK_card11_seq66666544443 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS) (hBig := hBig) (hNotOutOK := hNotOutOK)
        (hCard := by simpa [hn]) ⟨e, by rw [he, hS34444566666]; rfl⟩
    else if hS33445566666 : G.degreeSequence = [3, 3, 4, 4, 5, 5, 6, 6, 6, 6, 6] then
      exact exception_not_hOutOK_card11_seq66666554433 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS) (hBig := hBig) (hNotOutOK := hNotOutOK)
        (hCard := by simpa [hn]) ⟨e, by rw [he, hS33445566666]; rfl⟩
    else if hS33444666666 : G.degreeSequence = [3, 3, 4, 4, 4, 6, 6, 6, 6, 6, 6] then
      exact exception_not_hOutOK_card11_seq66666644433 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS) (hBig := hBig) (hNotOutOK := hNotOutOK)
        (hCard := by simpa [hn]) ⟨e, by rw [he, hS33444666666]; rfl⟩
    else if hS44444666666 : G.degreeSequence = [4, 4, 4, 4, 4, 6, 6, 6, 6, 6, 6] then
      exact exception_not_hOutOK_card11_seq66666644444 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS) (hBig := hBig) (hNotOutOK := hNotOutOK)
        (hCard := by simpa [hn]) ⟨e, by rw [he, hS44444666666]; rfl⟩
    else if hS33345666666 : G.degreeSequence = [3, 3, 3, 4, 5, 6, 6, 6, 6, 6, 6] then
      exact exception_not_hOutOK_card11_seq66666654333 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS) (hBig := hBig) (hNotOutOK := hNotOutOK)
        (hCard := by simpa [hn]) ⟨e, by rw [he, hS33345666666]; rfl⟩
    else if hS34445666666 : G.degreeSequence = [3, 4, 4, 4, 5, 6, 6, 6, 6, 6, 6] then
      exact exception_not_hOutOK_card11_seq66666654443 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS) (hBig := hBig) (hNotOutOK := hNotOutOK)
        (hCard := by simpa [hn]) ⟨e, by rw [he, hS34445666666]; rfl⟩
    else if hS33336666666 : G.degreeSequence = [3, 3, 3, 3, 6, 6, 6, 6, 6, 6, 6] then
      exact exception_not_hOutOK_card11_seq66666663333 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS) (hBig := hBig) (hNotOutOK := hNotOutOK)
        (hCard := by simpa [hn]) ⟨e, by rw [he, hS33336666666]; rfl⟩
    else if hS33446666666 : G.degreeSequence = [3, 3, 4, 4, 6, 6, 6, 6, 6, 6, 6] then
      exact exception_not_hOutOK_card11_seq66666664433 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS) (hBig := hBig) (hNotOutOK := hNotOutOK)
        (hCard := by simpa [hn]) ⟨e, by rw [he, hS33446666666]; rfl⟩
    else if hS24446666666 : G.degreeSequence = [2, 4, 4, 4, 6, 6, 6, 6, 6, 6, 6] then
      exact exception_not_hOutOK_card11_seq66666664442 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS) (hBig := hBig) (hNotOutOK := hNotOutOK)
        (hCard := by simpa [hn]) ⟨e, by rw [he, hS24446666666]; rfl⟩
    else
      sorry
  | 12 =>
    obtain ⟨e, he⟩ := AbsLink.exists_ofFn_eq_reverse (n := 12) G (by omega)
    if hS555555555566 : G.degreeSequence = [5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 6, 6] then
      exact exception_not_hOutOK_card12_seq665555555555 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS) (hBig := hBig) (hNotOutOK := hNotOutOK)
        (hCard := by simpa [hn]) ⟨e, by rw [he, hS555555555566]; rfl⟩
    else if hS455555555666 : G.degreeSequence = [4, 5, 5, 5, 5, 5, 5, 5, 5, 6, 6, 6] then
      exact exception_not_hOutOK_card12_seq666555555554 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS) (hBig := hBig) (hNotOutOK := hNotOutOK)
        (hCard := by simpa [hn]) ⟨e, by rw [he, hS455555555666]; rfl⟩
    else if hS445555556666 : G.degreeSequence = [4, 4, 5, 5, 5, 5, 5, 5, 6, 6, 6, 6] then
      exact exception_not_hOutOK_card12_seq666655555544 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS) (hBig := hBig) (hNotOutOK := hNotOutOK)
        (hCard := by simpa [hn]) ⟨e, by rw [he, hS445555556666]; rfl⟩
    else if hS555555556666 : G.degreeSequence = [5, 5, 5, 5, 5, 5, 5, 5, 6, 6, 6, 6] then
      exact exception_not_hOutOK_card12_seq666655555555 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS) (hBig := hBig) (hNotOutOK := hNotOutOK)
        (hCard := by simpa [hn]) ⟨e, by rw [he, hS555555556666]; rfl⟩
    else if hS444555566666 : G.degreeSequence = [4, 4, 4, 5, 5, 5, 5, 6, 6, 6, 6, 6] then
      exact exception_not_hOutOK_card12_seq666665555444 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS) (hBig := hBig) (hNotOutOK := hNotOutOK)
        (hCard := by simpa [hn]) ⟨e, by rw [he, hS444555566666]; rfl⟩
    else if hS455555566666 : G.degreeSequence = [4, 5, 5, 5, 5, 5, 5, 6, 6, 6, 6, 6] then
      exact exception_not_hOutOK_card12_seq666665555554 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS) (hBig := hBig) (hNotOutOK := hNotOutOK)
        (hCard := by simpa [hn]) ⟨e, by rw [he, hS455555566666]; rfl⟩
    else if hS444455666666 : G.degreeSequence = [4, 4, 4, 4, 5, 5, 6, 6, 6, 6, 6, 6] then
      exact exception_not_hOutOK_card12_seq666666554444 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS) (hBig := hBig) (hNotOutOK := hNotOutOK)
        (hCard := by simpa [hn]) ⟨e, by rw [he, hS444455666666]; rfl⟩
    else if hS445555666666 : G.degreeSequence = [4, 4, 5, 5, 5, 5, 6, 6, 6, 6, 6, 6] then
      exact exception_not_hOutOK_card12_seq666666555544 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS) (hBig := hBig) (hNotOutOK := hNotOutOK)
        (hCard := by simpa [hn]) ⟨e, by rw [he, hS445555666666]; rfl⟩
    else if hS355555666666 : G.degreeSequence = [3, 5, 5, 5, 5, 5, 6, 6, 6, 6, 6, 6] then
      exact exception_not_hOutOK_card12_seq666666555553 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS) (hBig := hBig) (hNotOutOK := hNotOutOK)
        (hCard := by simpa [hn]) ⟨e, by rw [he, hS355555666666]; rfl⟩
    else if hS555555666666 : G.degreeSequence = [5, 5, 5, 5, 5, 5, 6, 6, 6, 6, 6, 6] then
      exact exception_not_hOutOK_card12_seq666666555555 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS) (hBig := hBig) (hNotOutOK := hNotOutOK)
        (hCard := by simpa [hn]) ⟨e, by rw [he, hS555555666666]; rfl⟩
    else if hS444446666666 : G.degreeSequence = [4, 4, 4, 4, 4, 6, 6, 6, 6, 6, 6, 6] then
      exact exception_not_hOutOK_card12_seq666666644444 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS) (hBig := hBig) (hNotOutOK := hNotOutOK)
        (hCard := by simpa [hn]) ⟨e, by rw [he, hS444446666666]; rfl⟩
    else if hS444556666666 : G.degreeSequence = [4, 4, 4, 5, 5, 6, 6, 6, 6, 6, 6, 6] then
      exact exception_not_hOutOK_card12_seq666666655444 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS) (hBig := hBig) (hNotOutOK := hNotOutOK)
        (hCard := by simpa [hn]) ⟨e, by rw [he, hS444556666666]; rfl⟩
    else if hS345556666666 : G.degreeSequence = [3, 4, 5, 5, 5, 6, 6, 6, 6, 6, 6, 6] then
      exact exception_not_hOutOK_card12_seq666666655543 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS) (hBig := hBig) (hNotOutOK := hNotOutOK)
        (hCard := by simpa [hn]) ⟨e, by rw [he, hS345556666666]; rfl⟩
    else if hS455556666666 : G.degreeSequence = [4, 5, 5, 5, 5, 6, 6, 6, 6, 6, 6, 6] then
      exact exception_not_hOutOK_card12_seq666666655554 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS) (hBig := hBig) (hNotOutOK := hNotOutOK)
        (hCard := by simpa [hn]) ⟨e, by rw [he, hS455556666666]; rfl⟩
    else
      sorry
  | _ => sorry

theorem exception_not_hBig
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (connected : G.Connected)
    (hCard : Fintype.card V ≤ 12)
    (hResidue : residue G = 2)
    (hMaxDeg : G.maxDegree ≤ 6)
    (t : ℕ)
    (S : Finset V) (hS : ∀ v, v ∈ S ↔ t ≤ G.degree v)
    (hNotBig : ¬ (Fintype.card V - 1 ≤ 2 * (card S - 1) ∧ 1 ≤ card S))
    : ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  have hCard12 : Fintype.card V ≤ 12 := by assumption
  match hn : Fintype.card V with
  | 4 =>
    obtain ⟨e, he⟩ := AbsLink.exists_ofFn_eq_reverse (n := 4) G (by omega)
    if hS1122 : G.degreeSequence = [1, 1, 2, 2] then
      exact exception_not_hBig_card4_seq2211 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS)
        (hNotBig := hNotBig) (hCard := by simpa [hn]) ⟨e, by rw [he, hS1122]; rfl⟩
    else
      sorry
  | 5 =>
    obtain ⟨e, he⟩ := AbsLink.exists_ofFn_eq_reverse (n := 5) G (by omega)
    if hS11222 : G.degreeSequence = [1, 1, 2, 2, 2] then
      exact exception_not_hBig_card5_seq22211 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS)
        (hNotBig := hNotBig) (hCard := by simpa [hn]) ⟨e, by rw [he, hS11222]; rfl⟩
    else
      sorry
  | 6 =>
    obtain ⟨e, he⟩ := AbsLink.exists_ofFn_eq_reverse (n := 6) G (by omega)
    if hS222233 : G.degreeSequence = [2, 2, 2, 2, 3, 3] then
      exact exception_not_hBig_card6_seq332222 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS)
        (hNotBig := hNotBig) (hCard := by simpa [hn]) ⟨e, by rw [he, hS222233]; rfl⟩
    else if hS122333 : G.degreeSequence = [1, 2, 2, 3, 3, 3] then
      exact exception_not_hBig_card6_seq333221 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS)
        (hNotBig := hNotBig) (hCard := by simpa [hn]) ⟨e, by rw [he, hS122333]; rfl⟩
    else if hS113333 : G.degreeSequence = [1, 1, 3, 3, 3, 3] then
      exact exception_not_hBig_card6_seq333311 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS)
        (hNotBig := hNotBig) (hCard := by simpa [hn]) ⟨e, by rw [he, hS113333]; rfl⟩
    else if hS222334 : G.degreeSequence = [2, 2, 2, 3, 3, 4] then
      exact exception_not_hBig_card6_seq433222 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS)
        (hNotBig := hNotBig) (hCard := by simpa [hn]) ⟨e, by rw [he, hS222334]; rfl⟩
    else if hS123334 : G.degreeSequence = [1, 2, 3, 3, 3, 4] then
      exact exception_not_hBig_card6_seq433321 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS)
        (hNotBig := hNotBig) (hCard := by simpa [hn]) ⟨e, by rw [he, hS123334]; rfl⟩
    else
      sorry
  | 7 =>
    obtain ⟨e, he⟩ := AbsLink.exists_ofFn_eq_reverse (n := 7) G (by omega)
    if hS2223333 : G.degreeSequence = [2, 2, 2, 3, 3, 3, 3] then
      exact exception_not_hBig_card7_seq3333222 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS)
        (hNotBig := hNotBig) (hCard := by simpa [hn]) ⟨e, by rw [he, hS2223333]; rfl⟩
    else if hS2224444 : G.degreeSequence = [2, 2, 2, 4, 4, 4, 4] then
      exact exception_not_hBig_card7_seq4444222 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS)
        (hNotBig := hNotBig) (hCard := by simpa [hn]) ⟨e, by rw [he, hS2224444]; rfl⟩
    else if hS1234444 : G.degreeSequence = [1, 2, 3, 4, 4, 4, 4] then
      exact exception_not_hBig_card7_seq4444321 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS)
        (hNotBig := hNotBig) (hCard := by simpa [hn]) ⟨e, by rw [he, hS1234444]; rfl⟩
    else if hS1144444 : G.degreeSequence = [1, 1, 4, 4, 4, 4, 4] then
      exact exception_not_hBig_card7_seq4444411 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS)
        (hNotBig := hNotBig) (hCard := by simpa [hn]) ⟨e, by rw [he, hS1144444]; rfl⟩
    else if hS1244445 : G.degreeSequence = [1, 2, 4, 4, 4, 4, 5] then
      exact exception_not_hBig_card7_seq5444421 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS)
        (hNotBig := hNotBig) (hCard := by simpa [hn]) ⟨e, by rw [he, hS1244445]; rfl⟩
    else
      sorry
  | 8 =>
    obtain ⟨e, he⟩ := AbsLink.exists_ofFn_eq_reverse (n := 8) G (by omega)
    if hS33333344 : G.degreeSequence = [3, 3, 3, 3, 3, 3, 4, 4] then
      exact exception_not_hBig_card8_seq44333333 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS)
        (hNotBig := hNotBig) (hCard := by simpa [hn]) ⟨e, by rw [he, hS33333344]; rfl⟩
    else if hS23333444 : G.degreeSequence = [2, 3, 3, 3, 3, 4, 4, 4] then
      exact exception_not_hBig_card8_seq44433332 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS)
        (hNotBig := hNotBig) (hCard := by simpa [hn]) ⟨e, by rw [he, hS23333444]; rfl⟩
    else if hS22334444 : G.degreeSequence = [2, 2, 3, 3, 4, 4, 4, 4] then
      exact exception_not_hBig_card8_seq44443322 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS)
        (hNotBig := hNotBig) (hCard := by simpa [hn]) ⟨e, by rw [he, hS22334444]; rfl⟩
    else if hS33334444 : G.degreeSequence = [3, 3, 3, 3, 4, 4, 4, 4] then
      exact exception_not_hBig_card8_seq44443333 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS)
        (hNotBig := hNotBig) (hCard := by simpa [hn]) ⟨e, by rw [he, hS33334444]; rfl⟩
    else if hS22244444 : G.degreeSequence = [2, 2, 2, 4, 4, 4, 4, 4] then
      exact exception_not_hBig_card8_seq44444222 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS)
        (hNotBig := hNotBig) (hCard := by simpa [hn]) ⟨e, by rw [he, hS22244444]; rfl⟩
    else if hS23344444 : G.degreeSequence = [2, 3, 3, 4, 4, 4, 4, 4] then
      exact exception_not_hBig_card8_seq44444332 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS)
        (hNotBig := hNotBig) (hCard := by simpa [hn]) ⟨e, by rw [he, hS23344444]; rfl⟩
    else if hS33333445 : G.degreeSequence = [3, 3, 3, 3, 3, 4, 4, 5] then
      exact exception_not_hBig_card8_seq54433333 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS)
        (hNotBig := hNotBig) (hCard := by simpa [hn]) ⟨e, by rw [he, hS33333445]; rfl⟩
    else if hS23334445 : G.degreeSequence = [2, 3, 3, 3, 4, 4, 4, 5] then
      exact exception_not_hBig_card8_seq54443332 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS)
        (hNotBig := hNotBig) (hCard := by simpa [hn]) ⟨e, by rw [he, hS23334445]; rfl⟩
    else if hS22344445 : G.degreeSequence = [2, 2, 3, 4, 4, 4, 4, 5] then
      exact exception_not_hBig_card8_seq54444322 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS)
        (hNotBig := hNotBig) (hCard := by simpa [hn]) ⟨e, by rw [he, hS22344445]; rfl⟩
    else if hS33334455 : G.degreeSequence = [3, 3, 3, 3, 4, 4, 5, 5] then
      exact exception_not_hBig_card8_seq55443333 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS)
        (hNotBig := hNotBig) (hCard := by simpa [hn]) ⟨e, by rw [he, hS33334455]; rfl⟩
    else if hS23344455 : G.degreeSequence = [2, 3, 3, 4, 4, 4, 5, 5] then
      exact exception_not_hBig_card8_seq55444332 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS)
        (hNotBig := hNotBig) (hCard := by simpa [hn]) ⟨e, by rw [he, hS23344455]; rfl⟩
    else if hS33335555 : G.degreeSequence = [3, 3, 3, 3, 5, 5, 5, 5] then
      exact exception_not_hBig_card8_seq55553333 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS)
        (hNotBig := hNotBig) (hCard := by simpa [hn]) ⟨e, by rw [he, hS33335555]; rfl⟩
    else if hS13445555 : G.degreeSequence = [1, 3, 4, 4, 5, 5, 5, 5] then
      exact exception_not_hBig_card8_seq55554431 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS)
        (hNotBig := hNotBig) (hCard := by simpa [hn]) ⟨e, by rw [he, hS13445555]; rfl⟩
    else if hS22355555 : G.degreeSequence = [2, 2, 3, 5, 5, 5, 5, 5] then
      exact exception_not_hBig_card8_seq55555322 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS)
        (hNotBig := hNotBig) (hCard := by simpa [hn]) ⟨e, by rw [he, hS22355555]; rfl⟩
    else if hS13355555 : G.degreeSequence = [1, 3, 3, 5, 5, 5, 5, 5] then
      exact exception_not_hBig_card8_seq55555331 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS)
        (hNotBig := hNotBig) (hCard := by simpa [hn]) ⟨e, by rw [he, hS13355555]; rfl⟩
    else if hS12455555 : G.degreeSequence = [1, 2, 4, 5, 5, 5, 5, 5] then
      exact exception_not_hBig_card8_seq55555421 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS)
        (hNotBig := hNotBig) (hCard := by simpa [hn]) ⟨e, by rw [he, hS12455555]; rfl⟩
    else if hS11555555 : G.degreeSequence = [1, 1, 5, 5, 5, 5, 5, 5] then
      exact exception_not_hBig_card8_seq55555511 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS)
        (hNotBig := hNotBig) (hCard := by simpa [hn]) ⟨e, by rw [he, hS11555555]; rfl⟩
    else if hS13555555 : G.degreeSequence = [1, 3, 5, 5, 5, 5, 5, 5] then
      exact exception_not_hBig_card8_seq55555531 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS)
        (hNotBig := hNotBig) (hCard := by simpa [hn]) ⟨e, by rw [he, hS13555555]; rfl⟩
    else if hS33334446 : G.degreeSequence = [3, 3, 3, 3, 4, 4, 4, 6] then
      exact exception_not_hBig_card8_seq64443333 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS)
        (hNotBig := hNotBig) (hCard := by simpa [hn]) ⟨e, by rw [he, hS33334446]; rfl⟩
    else if hS23344446 : G.degreeSequence = [2, 3, 3, 4, 4, 4, 4, 6] then
      exact exception_not_hBig_card8_seq64444332 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS)
        (hNotBig := hNotBig) (hCard := by simpa [hn]) ⟨e, by rw [he, hS23344446]; rfl⟩
    else if hS13455556 : G.degreeSequence = [1, 3, 4, 5, 5, 5, 5, 6] then
      exact exception_not_hBig_card8_seq65555431 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS)
        (hNotBig := hNotBig) (hCard := by simpa [hn]) ⟨e, by rw [he, hS13455556]; rfl⟩
    else if hS12555556 : G.degreeSequence = [1, 2, 5, 5, 5, 5, 5, 6] then
      exact exception_not_hBig_card8_seq65555521 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS)
        (hNotBig := hNotBig) (hCard := by simpa [hn]) ⟨e, by rw [he, hS12555556]; rfl⟩
    else if hS13555566 : G.degreeSequence = [1, 3, 5, 5, 5, 5, 6, 6] then
      exact exception_not_hBig_card8_seq66555531 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS)
        (hNotBig := hNotBig) (hCard := by simpa [hn]) ⟨e, by rw [he, hS13555566]; rfl⟩
    else
      sorry
  | 9 =>
    obtain ⟨e, he⟩ := AbsLink.exists_ofFn_eq_reverse (n := 9) G (by omega)
    if hS333344444 : G.degreeSequence = [3, 3, 3, 3, 4, 4, 4, 4, 4] then
      exact exception_not_hBig_card9_seq444443333 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS)
        (hNotBig := hNotBig) (hCard := by simpa [hn]) ⟨e, by rw [he, hS333344444]; rfl⟩
    else if hS333345555 : G.degreeSequence = [3, 3, 3, 3, 4, 5, 5, 5, 5] then
      exact exception_not_hBig_card9_seq555543333 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS)
        (hNotBig := hNotBig) (hCard := by simpa [hn]) ⟨e, by rw [he, hS333345555]; rfl⟩
    else if hS233445555 : G.degreeSequence = [2, 3, 3, 4, 4, 5, 5, 5, 5] then
      exact exception_not_hBig_card9_seq555544332 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS)
        (hNotBig := hNotBig) (hCard := by simpa [hn]) ⟨e, by rw [he, hS233445555]; rfl⟩
    else if hS233355555 : G.degreeSequence = [2, 3, 3, 3, 5, 5, 5, 5, 5] then
      exact exception_not_hBig_card9_seq555553332 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS)
        (hNotBig := hNotBig) (hCard := by simpa [hn]) ⟨e, by rw [he, hS233355555]; rfl⟩
    else if hS223455555 : G.degreeSequence = [2, 2, 3, 4, 5, 5, 5, 5, 5] then
      exact exception_not_hBig_card9_seq555554322 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS)
        (hNotBig := hNotBig) (hCard := by simpa [hn]) ⟨e, by rw [he, hS223455555]; rfl⟩
    else if hS222555555 : G.degreeSequence = [2, 2, 2, 5, 5, 5, 5, 5, 5] then
      exact exception_not_hBig_card9_seq555555222 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS)
        (hNotBig := hNotBig) (hCard := by simpa [hn]) ⟨e, by rw [he, hS222555555]; rfl⟩
    else if hS233555555 : G.degreeSequence = [2, 3, 3, 5, 5, 5, 5, 5, 5] then
      exact exception_not_hBig_card9_seq555555332 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS)
        (hNotBig := hNotBig) (hCard := by simpa [hn]) ⟨e, by rw [he, hS233555555]; rfl⟩
    else if hS333355556 : G.degreeSequence = [3, 3, 3, 3, 5, 5, 5, 5, 6] then
      exact exception_not_hBig_card9_seq655553333 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS)
        (hNotBig := hNotBig) (hCard := by simpa [hn]) ⟨e, by rw [he, hS333355556]; rfl⟩
    else if hS233455556 : G.degreeSequence = [2, 3, 3, 4, 5, 5, 5, 5, 6] then
      exact exception_not_hBig_card9_seq655554332 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS)
        (hNotBig := hNotBig) (hCard := by simpa [hn]) ⟨e, by rw [he, hS233455556]; rfl⟩
    else if hS223555556 : G.degreeSequence = [2, 2, 3, 5, 5, 5, 5, 5, 6] then
      exact exception_not_hBig_card9_seq655555322 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS)
        (hNotBig := hNotBig) (hCard := by simpa [hn]) ⟨e, by rw [he, hS223555556]; rfl⟩
    else if hS233555566 : G.degreeSequence = [2, 3, 3, 5, 5, 5, 5, 6, 6] then
      exact exception_not_hBig_card9_seq665555332 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS)
        (hNotBig := hNotBig) (hCard := by simpa [hn]) ⟨e, by rw [he, hS233555566]; rfl⟩
    else if hS135566666 : G.degreeSequence = [1, 3, 5, 5, 6, 6, 6, 6, 6] then
      exact exception_not_hBig_card9_seq666665531 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS)
        (hNotBig := hNotBig) (hCard := by simpa [hn]) ⟨e, by rw [he, hS135566666]; rfl⟩
    else if hS134666666 : G.degreeSequence = [1, 3, 4, 6, 6, 6, 6, 6, 6] then
      exact exception_not_hBig_card9_seq666666431 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS)
        (hNotBig := hNotBig) (hCard := by simpa [hn]) ⟨e, by rw [he, hS134666666]; rfl⟩
    else if hS125666666 : G.degreeSequence = [1, 2, 5, 6, 6, 6, 6, 6, 6] then
      exact exception_not_hBig_card9_seq666666521 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS)
        (hNotBig := hNotBig) (hCard := by simpa [hn]) ⟨e, by rw [he, hS125666666]; rfl⟩
    else if hS116666666 : G.degreeSequence = [1, 1, 6, 6, 6, 6, 6, 6, 6] then
      exact exception_not_hBig_card9_seq666666611 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS)
        (hNotBig := hNotBig) (hCard := by simpa [hn]) ⟨e, by rw [he, hS116666666]; rfl⟩
    else if hS136666666 : G.degreeSequence = [1, 3, 6, 6, 6, 6, 6, 6, 6] then
      exact exception_not_hBig_card9_seq666666631 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS)
        (hNotBig := hNotBig) (hCard := by simpa [hn]) ⟨e, by rw [he, hS136666666]; rfl⟩
    else
      sorry
  | 10 =>
    obtain ⟨e, he⟩ := AbsLink.exists_ofFn_eq_reverse (n := 10) G (by omega)
    if hS4444444455 : G.degreeSequence = [4, 4, 4, 4, 4, 4, 4, 4, 5, 5] then
      exact exception_not_hBig_card10_seq5544444444 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS)
        (hNotBig := hNotBig) (hCard := by simpa [hn]) ⟨e, by rw [he, hS4444444455]; rfl⟩
    else if hS3444444555 : G.degreeSequence = [3, 4, 4, 4, 4, 4, 4, 5, 5, 5] then
      exact exception_not_hBig_card10_seq5554444443 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS)
        (hNotBig := hNotBig) (hCard := by simpa [hn]) ⟨e, by rw [he, hS3444444555]; rfl⟩
    else if hS3344445555 : G.degreeSequence = [3, 3, 4, 4, 4, 4, 5, 5, 5, 5] then
      exact exception_not_hBig_card10_seq5555444433 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS)
        (hNotBig := hNotBig) (hCard := by simpa [hn]) ⟨e, by rw [he, hS3344445555]; rfl⟩
    else if hS4444445555 : G.degreeSequence = [4, 4, 4, 4, 4, 4, 5, 5, 5, 5] then
      exact exception_not_hBig_card10_seq5555444444 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS)
        (hNotBig := hNotBig) (hCard := by simpa [hn]) ⟨e, by rw [he, hS4444445555]; rfl⟩
    else if hS3334455555 : G.degreeSequence = [3, 3, 3, 4, 4, 5, 5, 5, 5, 5] then
      exact exception_not_hBig_card10_seq5555544333 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS)
        (hNotBig := hNotBig) (hCard := by simpa [hn]) ⟨e, by rw [he, hS3334455555]; rfl⟩
    else if hS3444455555 : G.degreeSequence = [3, 4, 4, 4, 4, 5, 5, 5, 5, 5] then
      exact exception_not_hBig_card10_seq5555544443 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS)
        (hNotBig := hNotBig) (hCard := by simpa [hn]) ⟨e, by rw [he, hS3444455555]; rfl⟩
    else if hS3333555555 : G.degreeSequence = [3, 3, 3, 3, 5, 5, 5, 5, 5, 5] then
      exact exception_not_hBig_card10_seq5555553333 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS)
        (hNotBig := hNotBig) (hCard := by simpa [hn]) ⟨e, by rw [he, hS3333555555]; rfl⟩
    else if hS3344555555 : G.degreeSequence = [3, 3, 4, 4, 5, 5, 5, 5, 5, 5] then
      exact exception_not_hBig_card10_seq5555554433 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS)
        (hNotBig := hNotBig) (hCard := by simpa [hn]) ⟨e, by rw [he, hS3344555555]; rfl⟩
    else if hS2444555555 : G.degreeSequence = [2, 4, 4, 4, 5, 5, 5, 5, 5, 5] then
      exact exception_not_hBig_card10_seq5555554442 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS)
        (hNotBig := hNotBig) (hCard := by simpa [hn]) ⟨e, by rw [he, hS2444555555]; rfl⟩
    else if hS4444444556 : G.degreeSequence = [4, 4, 4, 4, 4, 4, 4, 5, 5, 6] then
      exact exception_not_hBig_card10_seq6554444444 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS)
        (hNotBig := hNotBig) (hCard := by simpa [hn]) ⟨e, by rw [he, hS4444444556]; rfl⟩
    else if hS3444445556 : G.degreeSequence = [3, 4, 4, 4, 4, 4, 5, 5, 5, 6] then
      exact exception_not_hBig_card10_seq6555444443 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS)
        (hNotBig := hNotBig) (hCard := by simpa [hn]) ⟨e, by rw [he, hS3444445556]; rfl⟩
    else if hS3344455556 : G.degreeSequence = [3, 3, 4, 4, 4, 5, 5, 5, 5, 6] then
      exact exception_not_hBig_card10_seq6555544433 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS)
        (hNotBig := hNotBig) (hCard := by simpa [hn]) ⟨e, by rw [he, hS3344455556]; rfl⟩
    else if hS4444455556 : G.degreeSequence = [4, 4, 4, 4, 4, 5, 5, 5, 5, 6] then
      exact exception_not_hBig_card10_seq6555544444 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS)
        (hNotBig := hNotBig) (hCard := by simpa [hn]) ⟨e, by rw [he, hS4444455556]; rfl⟩
    else if hS3334555556 : G.degreeSequence = [3, 3, 3, 4, 5, 5, 5, 5, 5, 6] then
      exact exception_not_hBig_card10_seq6555554333 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS)
        (hNotBig := hNotBig) (hCard := by simpa [hn]) ⟨e, by rw [he, hS3334555556]; rfl⟩
    else if hS3444555556 : G.degreeSequence = [3, 4, 4, 4, 5, 5, 5, 5, 5, 6] then
      exact exception_not_hBig_card10_seq6555554443 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS)
        (hNotBig := hNotBig) (hCard := by simpa [hn]) ⟨e, by rw [he, hS3444555556]; rfl⟩
    else if hS4444445566 : G.degreeSequence = [4, 4, 4, 4, 4, 4, 5, 5, 6, 6] then
      exact exception_not_hBig_card10_seq6655444444 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS)
        (hNotBig := hNotBig) (hCard := by simpa [hn]) ⟨e, by rw [he, hS4444445566]; rfl⟩
    else if hS3444455566 : G.degreeSequence = [3, 4, 4, 4, 4, 5, 5, 5, 6, 6] then
      exact exception_not_hBig_card10_seq6655544443 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS)
        (hNotBig := hNotBig) (hCard := by simpa [hn]) ⟨e, by rw [he, hS3444455566]; rfl⟩
    else if hS3344555566 : G.degreeSequence = [3, 3, 4, 4, 5, 5, 5, 5, 6, 6] then
      exact exception_not_hBig_card10_seq6655554433 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS)
        (hNotBig := hNotBig) (hCard := by simpa [hn]) ⟨e, by rw [he, hS3344555566]; rfl⟩
    else if hS4444455666 : G.degreeSequence = [4, 4, 4, 4, 4, 5, 5, 6, 6, 6] then
      exact exception_not_hBig_card10_seq6665544444 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS)
        (hNotBig := hNotBig) (hCard := by simpa [hn]) ⟨e, by rw [he, hS4444455666]; rfl⟩
    else if hS3444555666 : G.degreeSequence = [3, 4, 4, 4, 5, 5, 5, 6, 6, 6] then
      exact exception_not_hBig_card10_seq6665554443 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS)
        (hNotBig := hNotBig) (hCard := by simpa [hn]) ⟨e, by rw [he, hS3444555666]; rfl⟩
    else if hS3444456666 : G.degreeSequence = [3, 4, 4, 4, 4, 5, 6, 6, 6, 6] then
      exact exception_not_hBig_card10_seq6666544443 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS)
        (hNotBig := hNotBig) (hCard := by simpa [hn]) ⟨e, by rw [he, hS3444456666]; rfl⟩
    else if hS3344556666 : G.degreeSequence = [3, 3, 4, 4, 5, 5, 6, 6, 6, 6] then
      exact exception_not_hBig_card10_seq6666554433 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS)
        (hNotBig := hNotBig) (hCard := by simpa [hn]) ⟨e, by rw [he, hS3344556666]; rfl⟩
    else if hS2444556666 : G.degreeSequence = [2, 4, 4, 4, 5, 5, 6, 6, 6, 6] then
      exact exception_not_hBig_card10_seq6666554442 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS)
        (hNotBig := hNotBig) (hCard := by simpa [hn]) ⟨e, by rw [he, hS2444556666]; rfl⟩
    else if hS3344466666 : G.degreeSequence = [3, 3, 4, 4, 4, 6, 6, 6, 6, 6] then
      exact exception_not_hBig_card10_seq6666644433 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS)
        (hNotBig := hNotBig) (hCard := by simpa [hn]) ⟨e, by rw [he, hS3344466666]; rfl⟩
    else if hS2444466666 : G.degreeSequence = [2, 4, 4, 4, 4, 6, 6, 6, 6, 6] then
      exact exception_not_hBig_card10_seq6666644442 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS)
        (hNotBig := hNotBig) (hCard := by simpa [hn]) ⟨e, by rw [he, hS2444466666]; rfl⟩
    else if hS4444466666 : G.degreeSequence = [4, 4, 4, 4, 4, 6, 6, 6, 6, 6] then
      exact exception_not_hBig_card10_seq6666644444 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS)
        (hNotBig := hNotBig) (hCard := by simpa [hn]) ⟨e, by rw [he, hS4444466666]; rfl⟩
    else if hS3334566666 : G.degreeSequence = [3, 3, 3, 4, 5, 6, 6, 6, 6, 6] then
      exact exception_not_hBig_card10_seq6666654333 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS)
        (hNotBig := hNotBig) (hCard := by simpa [hn]) ⟨e, by rw [he, hS3334566666]; rfl⟩
    else if hS2335566666 : G.degreeSequence = [2, 3, 3, 5, 5, 6, 6, 6, 6, 6] then
      exact exception_not_hBig_card10_seq6666655332 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS)
        (hNotBig := hNotBig) (hCard := by simpa [hn]) ⟨e, by rw [he, hS2335566666]; rfl⟩
    else if hS2245566666 : G.degreeSequence = [2, 2, 4, 5, 5, 6, 6, 6, 6, 6] then
      exact exception_not_hBig_card10_seq6666655422 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS)
        (hNotBig := hNotBig) (hCard := by simpa [hn]) ⟨e, by rw [he, hS2245566666]; rfl⟩
    else if hS3333666666 : G.degreeSequence = [3, 3, 3, 3, 6, 6, 6, 6, 6, 6] then
      exact exception_not_hBig_card10_seq6666663333 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS)
        (hNotBig := hNotBig) (hCard := by simpa [hn]) ⟨e, by rw [he, hS3333666666]; rfl⟩
    else if hS2334666666 : G.degreeSequence = [2, 3, 3, 4, 6, 6, 6, 6, 6, 6] then
      exact exception_not_hBig_card10_seq6666664332 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS)
        (hNotBig := hNotBig) (hCard := by simpa [hn]) ⟨e, by rw [he, hS2334666666]; rfl⟩
    else if hS2244666666 : G.degreeSequence = [2, 2, 4, 4, 6, 6, 6, 6, 6, 6] then
      exact exception_not_hBig_card10_seq6666664422 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS)
        (hNotBig := hNotBig) (hCard := by simpa [hn]) ⟨e, by rw [he, hS2244666666]; rfl⟩
    else if hS2235666666 : G.degreeSequence = [2, 2, 3, 5, 6, 6, 6, 6, 6, 6] then
      exact exception_not_hBig_card10_seq6666665322 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS)
        (hNotBig := hNotBig) (hCard := by simpa [hn]) ⟨e, by rw [he, hS2235666666]; rfl⟩
    else if hS2226666666 : G.degreeSequence = [2, 2, 2, 6, 6, 6, 6, 6, 6, 6] then
      exact exception_not_hBig_card10_seq6666666222 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS)
        (hNotBig := hNotBig) (hCard := by simpa [hn]) ⟨e, by rw [he, hS2226666666]; rfl⟩
    else if hS2336666666 : G.degreeSequence = [2, 3, 3, 6, 6, 6, 6, 6, 6, 6] then
      exact exception_not_hBig_card10_seq6666666332 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS)
        (hNotBig := hNotBig) (hCard := by simpa [hn]) ⟨e, by rw [he, hS2336666666]; rfl⟩
    else if hS2246666666 : G.degreeSequence = [2, 2, 4, 6, 6, 6, 6, 6, 6, 6] then
      exact exception_not_hBig_card10_seq6666666422 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS)
        (hNotBig := hNotBig) (hCard := by simpa [hn]) ⟨e, by rw [he, hS2246666666]; rfl⟩
    else
      sorry
  | 11 =>
    obtain ⟨e, he⟩ := AbsLink.exists_ofFn_eq_reverse (n := 11) G (by omega)
    if hS44444555555 : G.degreeSequence = [4, 4, 4, 4, 4, 5, 5, 5, 5, 5, 5] then
      exact exception_not_hBig_card11_seq55555544444 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS)
        (hNotBig := hNotBig) (hCard := by simpa [hn]) ⟨e, by rw [he, hS44444555555]; rfl⟩
    else if hS44444556666 : G.degreeSequence = [4, 4, 4, 4, 4, 5, 5, 6, 6, 6, 6] then
      exact exception_not_hBig_card11_seq66665544444 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS)
        (hNotBig := hNotBig) (hCard := by simpa [hn]) ⟨e, by rw [he, hS44444556666]; rfl⟩
    else if hS34445556666 : G.degreeSequence = [3, 4, 4, 4, 5, 5, 5, 6, 6, 6, 6] then
      exact exception_not_hBig_card11_seq66665554443 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS)
        (hNotBig := hNotBig) (hCard := by simpa [hn]) ⟨e, by rw [he, hS34445556666]; rfl⟩
    else if hS44444466666 : G.degreeSequence = [4, 4, 4, 4, 4, 4, 6, 6, 6, 6, 6] then
      exact exception_not_hBig_card11_seq66666444444 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS)
        (hNotBig := hNotBig) (hCard := by simpa [hn]) ⟨e, by rw [he, hS44444466666]; rfl⟩
    else if hS34444566666 : G.degreeSequence = [3, 4, 4, 4, 4, 5, 6, 6, 6, 6, 6] then
      exact exception_not_hBig_card11_seq66666544443 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS)
        (hNotBig := hNotBig) (hCard := by simpa [hn]) ⟨e, by rw [he, hS34444566666]; rfl⟩
    else if hS33445566666 : G.degreeSequence = [3, 3, 4, 4, 5, 5, 6, 6, 6, 6, 6] then
      exact exception_not_hBig_card11_seq66666554433 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS)
        (hNotBig := hNotBig) (hCard := by simpa [hn]) ⟨e, by rw [he, hS33445566666]; rfl⟩
    else if hS33444666666 : G.degreeSequence = [3, 3, 4, 4, 4, 6, 6, 6, 6, 6, 6] then
      exact exception_not_hBig_card11_seq66666644433 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS)
        (hNotBig := hNotBig) (hCard := by simpa [hn]) ⟨e, by rw [he, hS33444666666]; rfl⟩
    else if hS44444666666 : G.degreeSequence = [4, 4, 4, 4, 4, 6, 6, 6, 6, 6, 6] then
      exact exception_not_hBig_card11_seq66666644444 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS)
        (hNotBig := hNotBig) (hCard := by simpa [hn]) ⟨e, by rw [he, hS44444666666]; rfl⟩
    else if hS33345666666 : G.degreeSequence = [3, 3, 3, 4, 5, 6, 6, 6, 6, 6, 6] then
      exact exception_not_hBig_card11_seq66666654333 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS)
        (hNotBig := hNotBig) (hCard := by simpa [hn]) ⟨e, by rw [he, hS33345666666]; rfl⟩
    else if hS34445666666 : G.degreeSequence = [3, 4, 4, 4, 5, 6, 6, 6, 6, 6, 6] then
      exact exception_not_hBig_card11_seq66666654443 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS)
        (hNotBig := hNotBig) (hCard := by simpa [hn]) ⟨e, by rw [he, hS34445666666]; rfl⟩
    else if hS33336666666 : G.degreeSequence = [3, 3, 3, 3, 6, 6, 6, 6, 6, 6, 6] then
      exact exception_not_hBig_card11_seq66666663333 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS)
        (hNotBig := hNotBig) (hCard := by simpa [hn]) ⟨e, by rw [he, hS33336666666]; rfl⟩
    else if hS33446666666 : G.degreeSequence = [3, 3, 4, 4, 6, 6, 6, 6, 6, 6, 6] then
      exact exception_not_hBig_card11_seq66666664433 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS)
        (hNotBig := hNotBig) (hCard := by simpa [hn]) ⟨e, by rw [he, hS33446666666]; rfl⟩
    else if hS24446666666 : G.degreeSequence = [2, 4, 4, 4, 6, 6, 6, 6, 6, 6, 6] then
      exact exception_not_hBig_card11_seq66666664442 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS)
        (hNotBig := hNotBig) (hCard := by simpa [hn]) ⟨e, by rw [he, hS24446666666]; rfl⟩
    else
      sorry
  | 12 =>
    obtain ⟨e, he⟩ := AbsLink.exists_ofFn_eq_reverse (n := 12) G (by omega)
    if hS555555555566 : G.degreeSequence = [5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 6, 6] then
      exact exception_not_hBig_card12_seq665555555555 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS)
        (hNotBig := hNotBig) (hCard := by simpa [hn]) ⟨e, by rw [he, hS555555555566]; rfl⟩
    else if hS455555555666 : G.degreeSequence = [4, 5, 5, 5, 5, 5, 5, 5, 5, 6, 6, 6] then
      exact exception_not_hBig_card12_seq666555555554 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS)
        (hNotBig := hNotBig) (hCard := by simpa [hn]) ⟨e, by rw [he, hS455555555666]; rfl⟩
    else if hS445555556666 : G.degreeSequence = [4, 4, 5, 5, 5, 5, 5, 5, 6, 6, 6, 6] then
      exact exception_not_hBig_card12_seq666655555544 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS)
        (hNotBig := hNotBig) (hCard := by simpa [hn]) ⟨e, by rw [he, hS445555556666]; rfl⟩
    else if hS555555556666 : G.degreeSequence = [5, 5, 5, 5, 5, 5, 5, 5, 6, 6, 6, 6] then
      exact exception_not_hBig_card12_seq666655555555 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS)
        (hNotBig := hNotBig) (hCard := by simpa [hn]) ⟨e, by rw [he, hS555555556666]; rfl⟩
    else if hS444555566666 : G.degreeSequence = [4, 4, 4, 5, 5, 5, 5, 6, 6, 6, 6, 6] then
      exact exception_not_hBig_card12_seq666665555444 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS)
        (hNotBig := hNotBig) (hCard := by simpa [hn]) ⟨e, by rw [he, hS444555566666]; rfl⟩
    else if hS455555566666 : G.degreeSequence = [4, 5, 5, 5, 5, 5, 5, 6, 6, 6, 6, 6] then
      exact exception_not_hBig_card12_seq666665555554 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS)
        (hNotBig := hNotBig) (hCard := by simpa [hn]) ⟨e, by rw [he, hS455555566666]; rfl⟩
    else if hS444455666666 : G.degreeSequence = [4, 4, 4, 4, 5, 5, 6, 6, 6, 6, 6, 6] then
      exact exception_not_hBig_card12_seq666666554444 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS)
        (hNotBig := hNotBig) (hCard := by simpa [hn]) ⟨e, by rw [he, hS444455666666]; rfl⟩
    else if hS445555666666 : G.degreeSequence = [4, 4, 5, 5, 5, 5, 6, 6, 6, 6, 6, 6] then
      exact exception_not_hBig_card12_seq666666555544 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS)
        (hNotBig := hNotBig) (hCard := by simpa [hn]) ⟨e, by rw [he, hS445555666666]; rfl⟩
    else if hS355555666666 : G.degreeSequence = [3, 5, 5, 5, 5, 5, 6, 6, 6, 6, 6, 6] then
      exact exception_not_hBig_card12_seq666666555553 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS)
        (hNotBig := hNotBig) (hCard := by simpa [hn]) ⟨e, by rw [he, hS355555666666]; rfl⟩
    else if hS555555666666 : G.degreeSequence = [5, 5, 5, 5, 5, 5, 6, 6, 6, 6, 6, 6] then
      exact exception_not_hBig_card12_seq666666555555 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS)
        (hNotBig := hNotBig) (hCard := by simpa [hn]) ⟨e, by rw [he, hS555555666666]; rfl⟩
    else if hS444446666666 : G.degreeSequence = [4, 4, 4, 4, 4, 6, 6, 6, 6, 6, 6, 6] then
      exact exception_not_hBig_card12_seq666666644444 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS)
        (hNotBig := hNotBig) (hCard := by simpa [hn]) ⟨e, by rw [he, hS444446666666]; rfl⟩
    else if hS444556666666 : G.degreeSequence = [4, 4, 4, 5, 5, 6, 6, 6, 6, 6, 6, 6] then
      exact exception_not_hBig_card12_seq666666655444 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS)
        (hNotBig := hNotBig) (hCard := by simpa [hn]) ⟨e, by rw [he, hS444556666666]; rfl⟩
    else if hS345556666666 : G.degreeSequence = [3, 4, 5, 5, 5, 6, 6, 6, 6, 6, 6, 6] then
      exact exception_not_hBig_card12_seq666666655543 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS)
        (hNotBig := hNotBig) (hCard := by simpa [hn]) ⟨e, by rw [he, hS345556666666]; rfl⟩
    else if hS455556666666 : G.degreeSequence = [4, 5, 5, 5, 5, 6, 6, 6, 6, 6, 6, 6] then
      exact exception_not_hBig_card12_seq666666655554 (G := G) (connected := connected) (hCard12 := hCard12)
        (hResidue := hResidue) (t := t) (S := S) (hS := hS)
        (hNotBig := hNotBig) (hCard := by simpa [hn]) ⟨e, by rw [he, hS455556666666]; rfl⟩
    else
      sorry
  | _ => sorry

end WOWII217SmallNExceptions
