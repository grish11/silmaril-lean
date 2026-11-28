module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.FoldSimulation

/-! # A checked state-fold simulation gives equality of the written loops

The premise is one equation of default Paper between guarded step regions:
the fold of the phases is a simulation of the step on the phases onto the
step on the state. The conclusion is an equation of `WithPhaseUniformity`
between the literal one-label loops.
-/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity

open Silmaril Silmaril.Isotope.LambdaSSA
open Silmaril.DeBruijn (lift)
open CategoryTheory CategoryTheory.Limits
open Paper.TypeCategory (ofType ofRegion phaseType phaseFold sumIso)

universe u v w
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε)
  (k : Nat) {A B : τ} {p q : Region Φ}
  (hp : ValueBranches [phaseType A k] p [Silmaril.coprod B (phaseType A k)])
  (hq : ValueBranches [A] q [Silmaril.coprod B A])
  (square : (ofRegion hp ≫ (sumIso (Φ := Φ) B (phaseType A k)).hom) ≫
      coprod.map (𝟙 _) (phaseFold A k) =
    phaseFold A k ≫ (ofRegion hq ≫ (sumIso (Φ := Φ) B A).hom))

include square in
/-- The loop on the phases is the fold followed by the loop on the state. -/
theorem fold_simulation :
    (projection pe).map (ofRegion (SyntacticCategory.iterateRegion_valueBranches hp)) =
      (projection pe).map
        (phaseFold A k ≫ ofRegion (SyntacticCategory.iterateRegion_valueBranches hq)) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.fold_simulation pe k hp hq square

include square in
/-- Entered through any guarded section of the fold, the loop on the
phases equals the loop on the state. -/
theorem fold_simulation_entered {e : Region Φ} (he : ValueBranches [A] e [phaseType A k])
    (sect : ofRegion he ≫ phaseFold (Φ := Φ) A k = 𝟙 _) :
    Eqv pe [A] (e.lsubst (fun _ =>
        (SyntacticCategory.iterateRegion (phaseType A k) p).renameVars (lift Nat.succ)))
      (SyntacticCategory.iterateRegion A q) [B] :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.fold_simulation_entered pe k hp hq square he sect

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity
