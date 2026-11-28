module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedProductProducers.Intrinsic.Selected.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Family.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.PackedBody.Thms
public import Silmaril.SSA.Isotope.LetIter.Categorical.Context.Iteration.Defs

/-! # Selected LambdaSSA sum cases with typed outward exits -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithComputedProductProducers.Intrinsic

open Silmaril Silmaril.Isotope.LambdaSSA
open Semantics.Categorical
open CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (caseWithContext)
open scoped MonoidalCategory

universe u v m n x y

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

/-- A branch receives the original input and the selected payload. Its body
returns to a recorded position in the ordered outward label context. -/
structure CaseArm (Φ : Type v) [HasTy Φ τ] (X A : τ) (L : LCtx τ) where
  result : τ
  exit : Nat
  atExit : At L exit result
  body : Program Φ (product X A) result

/-- Native case on a selected computation with independently typed arms. -/
structure SumCase (Φ : Type v) [HasTy Φ τ] (X : τ) (L : LCtx τ) where
  leftType : τ
  rightType : τ
  discriminator : Term Φ X (coprod leftType rightType)
  onLeft : CaseArm Φ X leftType L
  onRight : CaseArm Φ X rightType L

variable {X A : τ} {L : LCtx τ}

omit [TypeFormers τ] in
/-- Send a singleton return to its selected position in the outward context. -/
theorem singletonExitRen {D : τ} {exit : Nat} (atExit : At L exit D) :
    Ren [D] L (fun _ => exit) := by
  intro i E hi
  cases i with
  | zero => exact Option.some.inj hi ▸ atExit
  | succ i => simp [At] at hi

/-- Move the singleton return to this arm's chosen outward label. -/
theorem CaseArm.exitRen (arm : CaseArm Φ X A L) :
    Ren [arm.result] L (fun _ => arm.exit) :=
  singletonExitRen arm.atExit

/-- Supply the actual retained input and payload to the guarded body, then
retarget its singleton exit. -/
def CaseArm.elaborate (arm : CaseArm Φ X A L) : {r : Region Φ // ValueBranches [A, X] r L} :=
  ⟨(PackedBody.applyPacked arm.body.elaborate.val).renameLabels (fun _ => arm.exit), by
    rw [renameLabels_eq_lsubst]
    exact (PackedBody.applyPacked_typed arm.body.elaborate.property).lsubst
      (fun _ _ hi => .br (arm.exitRen hi) (.var (i := 0) rfl))⟩

/-- Emit a single native region case with the selected discriminator and arms. -/
def SumCase.elaborate (p : SumCase Φ X L) : {r : Region Φ // ValueBranches [X] r L} :=
  ⟨_, .case p.discriminator.elaborate.property p.onLeft.elaborate.property p.onRight.elaborate.property⟩

variable {V : Type m} {C : Type n} [Category.{x} V] [Category.{y} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V] [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C] [DistributiveTensor V] [DistributivePremonoidalCategory C]
  (J : V ⥤ C) [DistributiveFreydCategory J]
  (M : TypeModel τ V) [InstructionModel J M Φ]

/-- Pack the original input and branch payload for the body, then inject its
result into the selected outward summand. -/
noncomputable def CaseArm.targetArrow (arm : CaseArm Φ X A L) :
    J.obj (M.obj X ⊗ M.obj A) ⟶ J.obj (labelObj M L) :=
  J.map (M.productIso X A).inv ≫ arm.body.targetArrow J M ≫ J.map (labelInject M arm.exit arm.atExit)

/-- Run the discriminator once and route its payload with the retained input
through the chosen distributive coproduct comparison to the selected arm. -/
noncomputable def SumCase.targetArrow (p : SumCase Φ X L) :
    J.obj (M.obj X) ⟶ J.obj (labelObj M L) :=
  caseWithContext J (p.discriminator.targetArrow J M ≫ J.map (M.coprodIso p.leftType p.rightType).hom)
    (p.onLeft.targetArrow J M) (p.onRight.targetArrow J M)

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithComputedProductProducers.Intrinsic
