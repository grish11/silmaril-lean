module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Iteration.Rounds.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.WithTripling.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Tripling.Components.Thms

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open Paper.WithAdministrativeReturns.WithGuardedTablePacking (Step)
open Paper.Extension.Singleton
open Paper.Extension.Singleton.Rounds
open Paper.Extension.Singleton.ThreeCycle (triple projectStep_thenOnRepeat)
open Paper.TypeCategory.ComponentTripling (thenOnRepeat)

universe u v w
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε)

set_option hygiene false in
local notation "N" => Step (τ := τ) (Φ := Φ) pe
set_option hygiene false in
local notation "E" => Paper.WithCaseReturns.BinaryFold.JoinedStep (τ := τ) (Φ := Φ) pe
set_option hygiene false in
local notation "T" => Paper.WithCaseReturns.BinaryFold.WithTripling.Step (τ := τ) (Φ := Φ) pe

set_option backward.isDefEq.respectTransparency false

/-- The binary-fold seed is among the seeds of the table-packing quotient. -/
theorem of_binaryFold {Γ : VCtx τ} {r s : Region Φ} {L : LCtx τ}
    (h : Paper.WithCaseReturns.BinaryFold.JoinedStep pe Γ r s L) : Step pe Γ r s L :=
  .inl (.inl (.inl (.inl (.inl h))))

theorem of_tripling {Γ : VCtx τ} {r s : Region Φ} {L : LCtx τ}
    (h : Paper.WithCaseReturns.BinaryFold.WithTripling.Step pe Γ r s L) : Step pe Γ r s L :=
  .inl (.inl (.inl (.inl h)))

theorem doubles : Doubles (Step (τ := τ) (Φ := Φ) pe) := by
  intro X Y g
  obtain ⟨f, rfl⟩ := exists_projectStep N g
  have old := Paper.WithCaseReturns.BinaryFold.double_step pe (projectStep E f)
  rw [← projectStep_thenOnRepeat, iterateChosen_projectStep, iterateChosen_projectStep] at old
  exact (congrArg (iterateChosen N) (projectStep_thenOnRepeat N f f).symm).trans
    ((iterateChosen_projectStep N (thenOnRepeat f f)).trans
      ((projection_map_of_le N (fun h => of_binaryFold pe h) old).trans
        (iterateChosen_projectStep N f).symm))

theorem triples : Triples (Step (τ := τ) (Φ := Φ) pe) := by
  intro X Y g
  obtain ⟨f, rfl⟩ := exists_projectStep N g
  let f₃ := thenOnRepeat f (thenOnRepeat f f)
  have batch (U : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop) :
      projectStep U f₃ = triple (projectStep U f) := by
    rw [show f₃ = thenOnRepeat f (thenOnRepeat f f) from rfl,
      projectStep_thenOnRepeat, projectStep_thenOnRepeat]
  have old := Paper.WithCaseReturns.BinaryFold.WithTripling.triple_step pe (projectStep T f)
  rw [← batch T, iterateChosen_projectStep, iterateChosen_projectStep] at old
  exact (congrArg (iterateChosen N) (batch N).symm).trans
    ((iterateChosen_projectStep N f₃).trans
      ((projection_map_of_le N (fun h => of_tripling pe h) old).trans
        (iterateChosen_projectStep N f).symm))

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking
