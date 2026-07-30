import WOWII217Bridge.Certified
import WOWII217Bridge.DegreeSort
import WOWII217FiniteSmallExceptionsChunks.Chunk013

namespace WOWII217Bridge

open SimpleGraph WOWII217FiniteBase WOWII217Closure WOWII217ClosureSemantics
open WOWII217BondyChvatal WOWII217FiniteSmallExceptions

/-! # Corrected pattern for `WOWII217SmallNExceptions`

The current file does

```
if hSeq : G_fin.degreeSequence = [2, 2, 1, 1] then ... else sorry
```

which can NEVER fire: `degreeSequence` is sorted *ascending* (`Multiset.sort (· ≤ ·)`),
so a path on 4 vertices gives `[1, 1, 2, 2]`, not `[2, 2, 1, 1]`.

Worse, even a corrected sorted comparison would not suffice: `fixedDegreeSequenceUpper`
is indexed *by vertex* (`matchesDegreesFromUpper` walks `i = 0, 1, 2, …`), so the chunk
theorems constrain a particular labelling. The graph must be relabelled first.

The pattern below does it properly:
  abstract `V`  --(equivFinOfCardEq)-->  `Fin n`  --(certified_n)-->  `Traceable`.
-/

/-- Transfer an abstract graph to `Fin n` and apply a certified chain.
This is the `hFinTrans` step of `WOWII217SmallNExceptions`, done correctly. -/
theorem traceable_of_card_eq {V : Type*} [Fintype V] [DecidableEq V] {n : Nat}
    (G : SimpleGraph V) [DecidableRel G.Adj] (ds : List Nat)
    (certified : ∀ (H : SimpleGraph (Fin n)) [DecidableRel H.Adj],
        H.Connected → List.ofFn (fun v : Fin n => H.degree v) = ds → Traceable H)
    (conn : G.Connected)
    (hdegs : ∃ e : Fin n ≃ V, List.ofFn (fun v : Fin n => G.degree (e v)) = ds) :
    Traceable G := by
  classical
  obtain ⟨e, hds⟩ := hdegs
  let G' : SimpleGraph (Fin n) := G.comap e.toEmbedding
  let iso : G' ≃g G := SimpleGraph.Iso.comap e G
  letI : DecidableRel G'.Adj := fun u v => by
    change Decidable (G.Adj (e u) (e v)); infer_instance
  have conn' : G'.Connected := iso.connected_iff.mpr conn
  have hds' : List.ofFn (fun v : Fin n => G'.degree v) = ds := by
    rw [← hds]; congr 1; funext v; exact (iso.degree_eq v).symm
  obtain ⟨a, b, p, hp⟩ := certified G' conn' hds'
  exact ⟨e a, e b, p.map iso.toHom, hp.map iso.toHom e.bijective⟩


/-- A COMPLETE corrected case, replacing one `| n =>` arm of
`WOWII217SmallNExceptions`. Compare the current code, which tests
`G_fin.degreeSequence = [6,6,5,5,5,5,3,1]` (never true) and falls through to `sorry`. -/
theorem case_card8_66555531 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (conn : G.Connected)
    (hdegs : ∃ e : Fin 8 ≃ V,
      List.ofFn (fun v : Fin 8 => G.degree (e v)) = [6, 6, 5, 5, 5, 5, 3, 1]) :
    Traceable G :=
  traceable_of_card_eq G _
    (fun H _ hconn hds => certified_8 _ H connected_degreeSequence_66555531_closes hconn hds)
    conn hdegs

end WOWII217Bridge

