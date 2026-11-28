module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.Composite.Padding.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Completion.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.Completion

/-! # One-square uniformity along any surjective finite tag map

No seed is added. Everything here is derived from `fold_simulation_padded`.

## Setting

Classes are indexed by `Fin (m + 2)` and class `c` carries the payload
type `A c`. A tag map `f : Fin (N + 1) → Fin (m + 2)` lists the source
states: state `k` has class `f k` and payload `A (f k)`. The source
states are summed in the written order, so the classes may be interleaved
in any way and may have any multiplicities. `tagFold A f` is the class
map (`famInj_tagFold`).

## Proved

* `tag_fold_uniform`: if `f` is surjective, `WithPhaseUniformity` is
  uniform along `tagFold A f` for every square
  `J ≫ (id + tagFold A f) = tagFold A f ≫ T` of default Paper. This is the
  only premise on the tables.
* `Padding.uniform`: the same for any state map with a supplied
  completion and section. This separates the bookkeeping from the
  simulation theorem.
* `class_fold_uniform`: the statement on phases of one payload type,
  which is the shape of the literal tables. It is transported along isos
  of default Paper by `uniform_conj`.

## How the completion is built

`tagPadding` gives each source state one phase of the class sum: the
state in the slot of its class and padding in the other slots. Every
summand of a right-nested sum of at least two classes has a complement
(`famSplit`), and the phases are assembled with the interchange
`(M + P) + (L + X) ≅ (M + L) + (P + X)`. The completion therefore has as
many phases as source states. It does not pad each class to the largest
multiplicity, which would use fewer phases. The padding is unreachable and
does not appear in the statements.

Surjectivity is used once, for the section `tagSection`. The completion
itself exists for every tag map.

## Not proved

* A tag map that is not surjective. The padded table needs a source state
  of every class.
* One class only. Then the class map is the phase fold up to `constIso`,
  which is the seed itself (`fold_uniform`).
* Nothing is claimed about packed dispatchers in general, or about maps
  that are not sums of class injections.
-/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity

open CategoryTheory CategoryTheory.Limits
open Paper.TypeCategory (ofType iterate phaseType famSum tagFold classFold constIso)
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking

universe u v w
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε)

/-- A state map with a completion and a section is uniform, from the one
square for the original table. -/
theorem _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory.Padding.uniform {X Z Y : τ}
    {h : ofType (Φ := Φ) X ⟶ ofType Z} (c : Paper.TypeCategory.Padding h)
    (s : ofType (Φ := Φ) Z ⟶ ofType X) (sect : s ≫ h = 𝟙 _)
    (J : ofType (Φ := Φ) X ⟶ ofType Y ⨿ ofType X) (T : ofType (Φ := Φ) Z ⟶ ofType Y ⨿ ofType Z)
    (square : J ≫ coprod.map (𝟙 _) h = h ≫ T) :
    (projection pe).map (iterate J) = (projection pe).map (h ≫ iterate T) :=
  PhaseUniformity.padding_uniform pe c s sect J T square

/-- Uniformity along the class map of any surjective finite tag map into
at least two classes, each source state carrying its class's payload type. -/
theorem tag_fold_uniform {m N : Nat} {Y : τ} (A : Fin (m + 2) → τ) (f : Fin (N + 1) → Fin (m + 2))
    (surj : Function.Surjective f)
    (J : ofType (Φ := Φ) (famSum N fun k => A (f k)) ⟶ ofType Y ⨿ ofType (famSum N fun k => A (f k)))
    (T : ofType (Φ := Φ) (famSum (m + 1) A) ⟶ ofType Y ⨿ ofType (famSum (m + 1) A))
    (square : J ≫ coprod.map (𝟙 _) (tagFold A f) = tagFold A f ≫ T) :
    (projection pe).map (iterate J) = (projection pe).map (tagFold A f ≫ iterate T) :=
  PhaseUniformity.tag_uniform pe A f surj J T square

/-- Uniformity along a map is stable under isos of default Paper on both
sides. -/
theorem uniform_conj {X X' Z Z' Y : τ} (α : ofType (Φ := Φ) X ≅ ofType X') (β : ofType (Φ := Φ) Z' ≅ ofType Z)
    (h' : ofType (Φ := Φ) X' ⟶ ofType Z')
    (uni : ∀ (J' : ofType (Φ := Φ) X' ⟶ ofType Y ⨿ ofType X') (T' : ofType (Φ := Φ) Z' ⟶ ofType Y ⨿ ofType Z'),
      J' ≫ coprod.map (𝟙 _) h' = h' ≫ T' →
        (projection pe).map (iterate J') = (projection pe).map (h' ≫ iterate T'))
    (J : ofType (Φ := Φ) X ⟶ ofType Y ⨿ ofType X) (T : ofType (Φ := Φ) Z ⟶ ofType Y ⨿ ofType Z)
    (square : J ≫ coprod.map (𝟙 _) (α.hom ≫ h' ≫ β.hom) = (α.hom ≫ h' ≫ β.hom) ≫ T) :
    (projection pe).map (iterate J) = (projection pe).map ((α.hom ≫ h' ≫ β.hom) ≫ iterate T) :=
  PhaseUniformity.conj pe α β h' uni J T square

/-- Uniformity along the class map of any surjective map between phases of
one payload type, onto at least two phases. -/
theorem class_fold_uniform (A : τ) {K m : Nat} {Y : τ} (cls : Fin (K + 1) → Fin (m + 2))
    (surj : Function.Surjective cls)
    (J : ofType (Φ := Φ) (phaseType A K) ⟶ ofType Y ⨿ ofType (phaseType A K))
    (T : ofType (Φ := Φ) (phaseType A (m + 1)) ⟶ ofType Y ⨿ ofType (phaseType A (m + 1)))
    (square : J ≫ coprod.map (𝟙 _) (classFold A cls) = classFold A cls ≫ T) :
    (projection pe).map (iterate J) = (projection pe).map (classFold A cls ≫ iterate T) :=
  PhaseUniformity.class_uniform pe A cls surj J T square

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity
