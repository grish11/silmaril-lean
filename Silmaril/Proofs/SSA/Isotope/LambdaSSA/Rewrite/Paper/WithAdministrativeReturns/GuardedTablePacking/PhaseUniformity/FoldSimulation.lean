module

public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.Rounds
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Thms

/-! # A checked fold simulation gives equality of the written loops -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open Silmaril.DeBruijn (lift)
open CfgEta.TypeCategory (seqValueBranches)
open Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity (Step Eqv)
open Paper.Extension.Singleton (projection)
open Paper.TypeCategory (ofType ofRegion iterate iterateSum iterateSum_ofRegion phaseType phaseFold sumIso)

universe u v w
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε)

set_option hygiene false in
local notation "N" => Step (τ := τ) (Φ := Φ) pe

set_option backward.isDefEq.respectTransparency false

/-- The default Paper loop of a guarded step at the chosen coproduct is
its literal one-label table. -/
theorem iterate_exact {A B : τ} {p : Region Φ} (hp : ValueBranches [A] p [Silmaril.coprod B A]) :
    iterate (ofRegion hp ≫ (sumIso (Φ := Φ) B A).hom) =
      ofRegion (SyntacticCategory.iterateRegion_valueBranches hp) := by
  change iterateSum ((ofRegion hp ≫ (sumIso (Φ := Φ) B A).hom) ≫ (sumIso (Φ := Φ) B A).inv) = _
  rw [Category.assoc, Iso.hom_inv_id, Category.comp_id, iterateSum_ofRegion]

variable (k : Nat) {A B : τ} {p q : Region Φ}
  (hp : ValueBranches [phaseType A k] p [Silmaril.coprod B (phaseType A k)])
  (hq : ValueBranches [A] q [Silmaril.coprod B A])
  (square : (ofRegion hp ≫ (sumIso (Φ := Φ) B (phaseType A k)).hom) ≫
      coprod.map (𝟙 _) (phaseFold A k) =
    phaseFold A k ≫ (ofRegion hq ≫ (sumIso (Φ := Φ) B A).hom))

include square in
theorem fold_simulation :
    (projection N).map (ofRegion (SyntacticCategory.iterateRegion_valueBranches hp)) =
      (projection N).map (phaseFold A k ≫ ofRegion (SyntacticCategory.iterateRegion_valueBranches hq)) := by
  have uniform := fold_uniform pe k _ _ square
  rwa [iterate_exact hp, iterate_exact hq] at uniform

include square in
theorem fold_simulation_entered {e : Region Φ} (he : ValueBranches [A] e [phaseType A k])
    (sect : ofRegion he ≫ phaseFold (Φ := Φ) A k = 𝟙 _) :
    Eqv pe [A] (e.lsubst (fun _ =>
        (SyntacticCategory.iterateRegion (phaseType A k) p).renameVars (lift Nat.succ)))
      (SyntacticCategory.iterateRegion A q) [B] := by
  let hl := SyntacticCategory.iterateRegion_valueBranches hp
  let hr := SyntacticCategory.iterateRegion_valueBranches hq
  apply (Paper.Extension.Singleton.ofRegion_eq_iff N (seqValueBranches he hl) hr).1
  have comp : ofRegion (seqValueBranches he hl) = ofRegion he ≫ ofRegion hl :=
    (Paper.TypeCategory.ofRegion_comp he hl (seqValueBranches he hl)).symm
  have loops := fold_simulation pe k hp hq square
  calc
    (projection N).map (ofRegion (seqValueBranches he hl)) =
        (projection N).map (ofRegion he) ≫ (projection N).map (ofRegion hl) :=
      (congrArg (projection N).map comp).trans ((projection N).map_comp _ _)
    _ = (projection N).map (ofRegion he) ≫ (projection N).map (phaseFold A k ≫ ofRegion hr) :=
      congrArg ((projection N).map (ofRegion he) ≫ ·) loops
    _ = (projection N).map ((ofRegion he ≫ phaseFold A k) ≫ ofRegion hr) := by
      rw [← Functor.map_comp, Category.assoc]
    _ = (projection N).map (ofRegion hr) := by rw [sect, Category.id_comp]

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity
