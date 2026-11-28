module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.Composite.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Padding.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.Padding

/-! # Folds with unequal fibres, from one overall square

No seed is added.

## The simulation theorem

`fold_simulation_padded` takes a state map `h : X → Z` and one equation of
default Paper, `J ≫ (id + h) = h ≫ T`. The remaining data only describe
how `X` completes to phases of `Z`:

* padding states `U` with a class map `u : U → Z`,
* a section `s` of `h`, one state of each class,
* an iso `ψ` of default Paper from `U + X` to `n + 1` phases of `Z` under
  which the phase fold is `[u, h]`.

None of them mentions the tables. The padded table is built inside the
proof. Its new states are unreachable, so entering it at an old state is
the original loop (`iterate_padStep`).

## Bookkeeping supplied here

`pair_fold_short`: two classes with `n + 1` duplicates of `A` and `n + 2`
of `B`, in the interleaved layout that starts with a `B` state. The
padding is one `A` state in front.

## Other fibres

This file supplies the data for one layout only. `Composite/Completion/Thms.lean`
builds `U`, `u`, `s` and `ψ` for every surjective finite tag map into at
least two classes.
-/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity

open CategoryTheory CategoryTheory.Limits
open Paper.TypeCategory (ofType iterate phaseType phaseFold pairPhases sumDesc shortFold)
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking

universe u v w
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε)

/-- A state map that becomes a total fold after unreachable padding and an
iso is uniform, from the one square for the original table. -/
theorem fold_simulation_padded (n : Nat) {X U Z Y : τ} (h : ofType (Φ := Φ) X ⟶ ofType Z)
    (u : ofType (Φ := Φ) U ⟶ ofType Z) (s : ofType (Φ := Φ) Z ⟶ ofType X) (sect : s ≫ h = 𝟙 _)
    (ψ : ofType (Φ := Φ) (Silmaril.coprod U X) ≅ ofType (phaseType Z n))
    (fold : ψ.hom ≫ phaseFold Z n = sumDesc u h)
    (J : ofType (Φ := Φ) X ⟶ ofType Y ⨿ ofType X) (T : ofType (Φ := Φ) Z ⟶ ofType Y ⨿ ofType Z)
    (square : J ≫ coprod.map (𝟙 _) h = h ≫ T) :
    (projection pe).map (iterate J) = (projection pe).map (h ≫ iterate T) :=
  PhaseUniformity.padded pe n h u s sect ψ fold J T square

/-- Two classes with `n + 1` and `n + 2` duplicates fold together, from
the one square for their class fold. -/
theorem pair_fold_short (A B : τ) (n : Nat) {Y : τ}
    (J : ofType (Φ := Φ) (Silmaril.coprod B (pairPhases A B n)) ⟶
      ofType Y ⨿ ofType (Silmaril.coprod B (pairPhases A B n)))
    (T : ofType (Φ := Φ) (Silmaril.coprod A B) ⟶ ofType Y ⨿ ofType (Silmaril.coprod A B))
    (square : J ≫ coprod.map (𝟙 _) (shortFold A B n) = shortFold A B n ≫ T) :
    (projection pe).map (iterate J) = (projection pe).map (shortFold A B n ≫ iterate T) :=
  PhaseUniformity.pair_short pe A B n J T square

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity
