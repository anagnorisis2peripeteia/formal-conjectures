import WOWII217Encoding13
import WOWII217Finite13ClosureSharedDegCert

/-!
Instantiate the relational order-13 certificate with semantic closure rounds,
then transport its complete final graph back to a Hamiltonian path in the
original graph.
-/

namespace WOWII217ClosureCertificateSemantics

open SimpleGraph
open WOWII217FiniteBase WOWII217Closure
open WOWII217BondyChvatal WOWII217ClosureSemantics
open WOWII217Encoding13
open WOWII217Finite13
-- Prefer ClosureSemantics for boolFourValue; SharedDeg for residual cert API.
open WOWII217Finite13ClosureSharedDeg
  (hasHighLowEdge13 pathClosureParallelRel13 degreeTableConsistent13 degreeTableAt13
    boolFourSumAtLeast12
    crossEdge_degreeSequence_6666666555555_shared_degree_closure)

def semanticRound13 (g : BitVec 78) : SimpleGraph (Fin 13) :=
  addEligibleEdgesFrom (graphOfUpper (n := 13) g) allPairs13
    (graphOfUpper (n := 13) g)

noncomputable instance semanticRound13_decidableRel (g : BitVec 78) :
    DecidableRel (semanticRound13 g).Adj := Classical.decRel _

noncomputable def nextUpper13 (g : BitVec 78) : BitVec 78 :=
  encodeUpper13 (semanticRound13 g)

theorem graphOfUpper_nextUpper13 (g : BitVec 78) :
    graphOfUpper (n := 13) (nextUpper13 g) = semanticRound13 g := by
  simpa [nextUpper13] using graphOfUpper_encodeUpper13 (semanticRound13 g)

theorem canonicalThreshold13 (g : BitVec 78) {u v : Nat}
    (hu : u < 13) (hv : v < 13) :
    boolFourSumAtLeast12
        (degreeTableAt13 (degreeTableOfUpper13 g) u)
        (degreeTableAt13 (degreeTableOfUpper13 g) v) =
      decide (12 ≤ degreeUpperNat (n := 13) g u +
        degreeUpperNat (n := 13) g v) := by
  have degreeU := degreeTableAt13_ofUpper g u hu
  have degreeV := degreeTableAt13_ofUpper g v hv
  apply Bool.eq_iff_iff.mpr
  simpa [degreeU, degreeV,
    boolFourValue_degreeBitsUpper_eq (n := 13) (by decide)] using
    (boolFourSumAtLeast12_iff
      (degreeTableAt13 (degreeTableOfUpper13 g) u)
      (degreeTableAt13 (degreeTableOfUpper13 g) v))

theorem boolFourValue_injective : Function.Injective boolFourValue := by
  intro x y valueEq
  rcases x with ⟨x0, x1, x2, x3⟩
  rcases y with ⟨y0, y1, y2, y3⟩
  fin_cases x0 <;> fin_cases x1 <;> fin_cases x2 <;> fin_cases x3 <;>
    fin_cases y0 <;> fin_cases y1 <;> fin_cases y2 <;> fin_cases y3 <;>
    simp [boolFourValue] at valueEq ⊢ <;> omega

theorem boolFourValue_ofNat_of_lt_sixteen (d : Nat) (hd : d < 16) :
    boolFourValue (BoolFour.ofNat d) = d := by
  interval_cases d <;> native_decide

theorem degreeBitsUpper_same_of_degree_eq {n d : Nat} (hn : n < 16)
    (g : BitVec (edgeCount n)) (u : Nat) (hd : d < 16)
    (degreeEq : degreeUpperNat g u = d) :
    (degreeBitsUpper g u).same (BoolFour.ofNat d) = true := by
  apply (boolFourSame_eq_true_iff _ _).mpr
  apply boolFourValue_injective
  rw [boolFourValue_degreeBitsUpper_eq hn, degreeEq,
    boolFourValue_ofNat_of_lt_sixteen d hd]

theorem degreeUpperNat_encodeUpper13_eq (G : SimpleGraph (Fin 13))
    [DecidableRel G.Adj] (u : Fin 13) :
    degreeUpperNat (n := 13) (encodeUpper13 G) u = G.degree u := by
  let iso : graphOfUpper (n := 13) (encodeUpper13 G) ≃g G :=
    { toEquiv := Equiv.refl _
      map_rel_iff' := by
        intro x y
        rw [graphOfUpper_encodeUpper13]
        simp }
  calc
    degreeUpperNat (n := 13) (encodeUpper13 G) u =
        (graphOfUpper (n := 13) (encodeUpper13 G)).degree u :=
      (degree_graphOfUpper_eq (n := 13) (encodeUpper13 G) u).symm
    _ = G.degree u := (iso.degree_eq u).symm

theorem degreeBitsUpper_encodeUpper13_same (G : SimpleGraph (Fin 13))
    [DecidableRel G.Adj] (u : Fin 13) (d : Nat) (hd : d < 16)
    (degreeEq : G.degree u = d) :
    (degreeBitsUpper (n := 13) (encodeUpper13 G) u).same
      (BoolFour.ofNat d) = true := by
  apply degreeBitsUpper_same_of_degree_eq (n := 13) (d := d) (by decide)
    (encodeUpper13 G) u hd
  rw [degreeUpperNat_encodeUpper13_eq, degreeEq]

theorem fixedDegreeSequenceUpper_encodeUpper13_of_labeledDegrees
    (G : SimpleGraph (Fin 13)) [DecidableRel G.Adj]
    (labeledDegrees : ∀ v : Fin 13,
      G.degree v = if v.val < 7 then 6 else 5) :
    fixedDegreeSequenceUpper (n := 13) (encodeUpper13 G)
      [6, 6, 6, 6, 6, 6, 6, 5, 5, 5, 5, 5, 5] = true := by
  have degree0 : G.degree (0 : Fin 13) = 6 := by simpa using labeledDegrees 0
  have degree1 : G.degree (1 : Fin 13) = 6 := by simpa using labeledDegrees 1
  have degree2 : G.degree (2 : Fin 13) = 6 := by simpa using labeledDegrees 2
  have degree3 : G.degree (3 : Fin 13) = 6 := by simpa using labeledDegrees 3
  have degree4 : G.degree (4 : Fin 13) = 6 := by simpa using labeledDegrees 4
  have degree5 : G.degree (5 : Fin 13) = 6 := by simpa using labeledDegrees 5
  have degree6 : G.degree (6 : Fin 13) = 6 := by simpa using labeledDegrees 6
  have degree7 : G.degree (7 : Fin 13) = 5 := by simpa using labeledDegrees 7
  have degree8 : G.degree (8 : Fin 13) = 5 := by simpa using labeledDegrees 8
  have degree9 : G.degree (9 : Fin 13) = 5 := by simpa using labeledDegrees 9
  have degree10 : G.degree (10 : Fin 13) = 5 := by simpa using labeledDegrees 10
  have degree11 : G.degree (11 : Fin 13) = 5 := by simpa using labeledDegrees 11
  have degree12 : G.degree (12 : Fin 13) = 5 := by simpa using labeledDegrees 12
  have match0 := degreeBitsUpper_encodeUpper13_same G 0 6 (by decide) degree0
  have match1 := degreeBitsUpper_encodeUpper13_same G 1 6 (by decide) degree1
  have match2 := degreeBitsUpper_encodeUpper13_same G 2 6 (by decide) degree2
  have match3 := degreeBitsUpper_encodeUpper13_same G 3 6 (by decide) degree3
  have match4 := degreeBitsUpper_encodeUpper13_same G 4 6 (by decide) degree4
  have match5 := degreeBitsUpper_encodeUpper13_same G 5 6 (by decide) degree5
  have match6 := degreeBitsUpper_encodeUpper13_same G 6 6 (by decide) degree6
  have match7 := degreeBitsUpper_encodeUpper13_same G 7 5 (by decide) degree7
  have match8 := degreeBitsUpper_encodeUpper13_same G 8 5 (by decide) degree8
  have match9 := degreeBitsUpper_encodeUpper13_same G 9 5 (by decide) degree9
  have match10 := degreeBitsUpper_encodeUpper13_same G 10 5 (by decide) degree10
  have match11 := degreeBitsUpper_encodeUpper13_same G 11 5 (by decide) degree11
  have match12 := degreeBitsUpper_encodeUpper13_same G 12 5 (by decide) degree12
  norm_num [fixedDegreeSequenceUpper, matchesDegreesFromUpper]
  constructor
  · simpa using match0
  constructor
  · simpa using match1
  constructor
  · simpa using match2
  constructor
  · simpa using match3
  constructor
  · simpa using match4
  constructor
  · simpa using match5
  constructor
  · simpa using match6
  constructor
  · simpa using match7
  constructor
  · simpa using match8
  constructor
  · simpa using match9
  constructor
  · simpa using match10
  constructor
  · simpa using match11
  · simpa using match12

theorem Walk.exists_high_low_edge {G : SimpleGraph (Fin 13)}
    {s t : Fin 13} (p : G.Walk s t) (hs : s.val < 7) (ht : ¬t.val < 7) :
    ∃ u v : Fin 13, u.val < 7 ∧ ¬v.val < 7 ∧ G.Adj u v := by
  induction p with
  | nil => exact (ht hs).elim
  | @cons u v w adjacent rest ih =>
      by_cases hv : v.val < 7
      · exact ih hv ht
      · exact ⟨u, v, hs, hv, adjacent⟩

theorem Connected.exists_high_low_edge {G : SimpleGraph (Fin 13)}
    (connected : G.Connected) :
    ∃ u v : Fin 13, u.val < 7 ∧ ¬v.val < 7 ∧ G.Adj u v := by
  exact (connected (0 : Fin 13) (7 : Fin 13)).elim fun p =>
    Walk.exists_high_low_edge p (by decide) (by decide)

theorem hasHighLowEdge13_encodeUpper13_of_connected
    (G : SimpleGraph (Fin 13)) [DecidableRel G.Adj]
    (connected : G.Connected) :
    hasHighLowEdge13 (encodeUpper13 G) = true := by
  obtain ⟨u, v, hu, hv, adjacent⟩ :=
    Connected.exists_high_low_edge connected
  have hvLower : 7 ≤ v.val := by omega
  have offsetLt : v.val - 7 < 6 := by omega
  rw [hasHighLowEdge13, List.any_eq_true]
  refine ⟨u.val, List.mem_range.mpr hu, ?_⟩
  rw [List.any_eq_true]
  refine ⟨v.val - 7, List.mem_range.mpr offsetLt, ?_⟩
  have offsetEq : v.val - 7 + 7 = v.val := by omega
  rw [offsetEq]
  change adjUpper (n := 13) (encodeUpper13 G) u v = true
  rw [adjUpper_encodeUpper13]
  exact decide_eq_true adjacent

theorem nextUpper13_related (g : BitVec 78) :
    pathClosureParallelRel13 g (nextUpper13 g) (degreeTableOfUpper13 g) = true := by
  rw [pathClosureParallelRel13, List.all_eq_true]
  intro edge hedge
  rcases mem_upperPairs_iff.mp hedge with ⟨hv, huv⟩
  let u : Fin 13 := ⟨edge.1, Nat.lt_trans huv hv⟩
  let v : Fin 13 := ⟨edge.2, hv⟩
  apply (boolNotXor_eq_true_iff _ _).mpr
  have encoded := adjUpper_encodeUpper13 (semanticRound13 g) u v
  have threshold := canonicalThreshold13 g (Nat.lt_trans huv hv) hv
  have threshold' :
      boolFourSumAtLeast12
          (degreeTableAt13 (degreeTableOfUpper13 g) u)
          (degreeTableAt13 (degreeTableOfUpper13 g) v) =
        decide (12 ≤ degreeUpperNat (n := 13) g u +
          degreeUpperNat (n := 13) g v) := by
    simpa [u, v] using threshold
  have degreeU := degree_graphOfUpper_eq (n := 13) g u
  have degreeV := degree_graphOfUpper_eq (n := 13) g v
  have hne : u ≠ v := Fin.ne_of_lt huv
  have encoded' :
      adjUpper (n := 13) (nextUpper13 g) edge.1 edge.2 =
        decide ((semanticRound13 g).Adj u v) := by
    simpa [nextUpper13, u, v] using encoded
  rw [encoded']
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq, Bool.or_eq_true_iff]
  change (semanticRound13 g).Adj u v ↔
    (adjUpper (n := 13) g u v = true ∨
      boolFourSumAtLeast12
        (degreeTableAt13 (degreeTableOfUpper13 g) u)
        (degreeTableAt13 (degreeTableOfUpper13 g) v) = true)
  unfold semanticRound13
  rw [adj_addEligibleEdges13_iff]
  rw [degreeU, degreeV, threshold']
  simp [hne, graphOfUpper]

theorem traceable_of_crossEdge_degreeSequence_6666666555555
    (g : BitVec 78)
    (crossEdge : hasHighLowEdge13 g = true)
    (degreeSequence :
      fixedDegreeSequenceUpper (n := 13) g
        [6, 6, 6, 6, 6, 6, 6, 5, 5, 5, 5, 5, 5] = true) :
    Traceable (graphOfUpper (n := 13) g) := by
  let g1 := nextUpper13 g
  let g2 := nextUpper13 g1
  let g3 := nextUpper13 g2
  let g4 := nextUpper13 g3
  have consistent0 := degreeTableOfUpper13_consistent g
  have consistent1 := degreeTableOfUpper13_consistent g1
  have consistent2 := degreeTableOfUpper13_consistent g2
  have consistent3 := degreeTableOfUpper13_consistent g3
  have related0 :
      pathClosureParallelRel13 g g1 (degreeTableOfUpper13 g) = true := by
    simpa [g1] using nextUpper13_related g
  have related1 :
      pathClosureParallelRel13 g1 g2 (degreeTableOfUpper13 g1) = true := by
    simpa [g2] using nextUpper13_related g1
  have related2 :
      pathClosureParallelRel13 g2 g3 (degreeTableOfUpper13 g2) = true := by
    simpa [g3] using nextUpper13_related g2
  have related3 :
      pathClosureParallelRel13 g3 g4 (degreeTableOfUpper13 g3) = true := by
    simpa [g4] using nextUpper13_related g3
  have complete4 : completeUpper (n := 13) g4 = true :=
    crossEdge_degreeSequence_6666666555555_shared_degree_closure
      g g1 g2 g3 g4
    (degreeTableOfUpper13 g) (degreeTableOfUpper13 g1)
      (degreeTableOfUpper13 g2) (degreeTableOfUpper13 g3)
      crossEdge degreeSequence consistent0 related0 consistent1 related1
      consistent2 related2 consistent3 related3
  have trace4 : Traceable (graphOfUpper (n := 13) g4) :=
    traceable_graphOfUpper_of_completeUpper13 g4 complete4
  have trace3 : Traceable (graphOfUpper (n := 13) g3) :=
    (traceable_graphOfUpper_rel13_iff g3 g4 (degreeTableOfUpper13 g3)
      consistent3 related3).mp trace4
  have trace2 : Traceable (graphOfUpper (n := 13) g2) :=
    (traceable_graphOfUpper_rel13_iff g2 g3 (degreeTableOfUpper13 g2)
      consistent2 related2).mp trace3
  have trace1 : Traceable (graphOfUpper (n := 13) g1) :=
    (traceable_graphOfUpper_rel13_iff g1 g2 (degreeTableOfUpper13 g1)
      consistent1 related1).mp trace2
  exact (traceable_graphOfUpper_rel13_iff g g1 (degreeTableOfUpper13 g)
    consistent0 related0).mp trace1

theorem traceable_of_connected_labeled_degreeSequence_6666666555555
    (G : SimpleGraph (Fin 13)) [DecidableRel G.Adj]
    (connected : G.Connected)
    (labeledDegrees : ∀ v : Fin 13,
      G.degree v = if v.val < 7 then 6 else 5) :
    Traceable G := by
  have traceEncoded := traceable_of_crossEdge_degreeSequence_6666666555555
    (encodeUpper13 G)
    (hasHighLowEdge13_encodeUpper13_of_connected G connected)
    (fixedDegreeSequenceUpper_encodeUpper13_of_labeledDegrees G labeledDegrees)
  rw [graphOfUpper_encodeUpper13] at traceEncoded
  exact traceEncoded

end WOWII217ClosureCertificateSemantics
