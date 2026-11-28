module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedProductProducers.Intrinsic.SumCase.Example.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedProductProducers.Intrinsic.SumCase.Thms
import Silmaril.SSA.Isotope.LetIter.Categorical.Kleisli.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Categorical.Thms

/-! # Regression proofs for the selected sum case -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SelectedSumCaseExample

open Silmaril.Isotope.LambdaSSA.Region
open Paper.WithComputedProductProducers.Intrinsic
open SumCase.Example
open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA
open Semantics.Categorical Semantics.Interaction.Typed
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (typeJ)
open Silmaril.Elgot.ITree CategoryTheory
open scoped MonoidalCategory

open CategoryTheory.Limits
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (caseWithContext_of)

attribute [local instance] typeModel categoricalInstructions

local notation "J" => typeJ (m := Model)
local notation "M" => ofMonadicTypeModel (τ := Ty Atom)

private theorem pack_exit0 (n : Nat) :
    packLabel M Labels (exit0 n) = Sum.inl (ULift.up n) := by
  have h := ConcreteCategory.congr_hom
    (labelInject_packLabel M (rfl : At Labels 0 Payload)) (show PayloadValue from ULift.up n)
  refine h.trans ?_
  simp only [packedLabelInject, eqToHom_refl, Category.id_comp]
  exact ConcreteCategory.congr_hom (Types.binaryCoproductIso_inl_comp_hom PayloadValue
    ((M).obj (packedExitType [Payload]))) (show PayloadValue from ULift.up n)

private theorem pack_exit1 (n : Nat) :
    packLabel M Labels (exit1 n) = Sum.inr (Sum.inl (ULift.up n)) := by
  have h := ConcreteCategory.congr_hom
    (labelInject_packLabel M (rfl : At Labels 1 Payload)) (show PayloadValue from ULift.up n)
  refine h.trans ?_
  simp only [packedLabelInject, eqToHom_refl, Category.id_comp]
  let D := ((M).obj (packedExitType [Payload]))
  have outer := Types.binaryCoproductIso_inr_comp_hom PayloadValue D
  have inner := Types.binaryCoproductIso_inl_comp_hom PayloadValue ((M).obj (empty : Ty Atom))
  exact ConcreteCategory.congr_hom
    (congrArg₂ CategoryStruct.comp inner outer) (show PayloadValue from ULift.up n)

theorem distinctSlots (left right : Nat) : exit1 left ≠ exit0 right := by
  intro h
  have tags := (pack_exit1 left).symm.trans ((congrArg (packLabel M Labels) h).trans (pack_exit0 right))
  cases tags

set_option backward.isDefEq.respectTransparency false in
private theorem left_of (x a : PayloadValue) :
    (program.onLeft.targetArrow J M).of (x, a) =
      vis (Request.left x.down a.down) (fun n => pure (exit1 n)) := by
  simp only [program, CaseArm.targetArrow, Program.targetArrow, Term.targetArrow, Category.id_comp,
    Kleisli.Type.comp_of_eq_kleisliRight, Bind.kleisliRight]
  change Bind.bind (m := Model) (pure (x, a)) (fun p =>
    Bind.bind (m := Model) (vis (Request.left p.1.down p.2.down) (fun n => pure (ULift.up n)))
      (fun n => pure (exit1 n.down))) = _
  simp only [vis_bind, pure_bind]

set_option backward.isDefEq.respectTransparency false in
private theorem right_of (x b : PayloadValue) :
    (program.onRight.targetArrow J M).of (x, b) =
      vis (Request.right x.down b.down) (fun n => pure (exit0 n)) := by
  simp only [program, CaseArm.targetArrow, Program.targetArrow, Term.targetArrow, Category.id_comp,
    Kleisli.Type.comp_of_eq_kleisliRight, Bind.kleisliRight]
  change Bind.bind (m := Model) (pure (x, b)) (fun p =>
    Bind.bind (m := Model) (vis (Request.right p.1.down p.2.down) (fun n => pure (ULift.up n)))
      (fun n => pure (exit0 n.down))) = _
  simp only [vis_bind, pure_bind]

set_option backward.isDefEq.respectTransparency false in
private theorem discriminator_of (x : PayloadValue) :
    ((program.discriminator.targetArrow J M) ≫ (J).map ((M).coprodIso Payload Payload).hom).of x =
      vis (Request.choose x.down) (fun n => pure (((M).coprodIso Payload Payload).hom (n.map ULift.up ULift.up))) := by
  simp only [program, Term.targetArrow, Category.id_comp, Kleisli.Type.comp_of_eq_kleisliRight, Bind.kleisliRight]
  change Bind.bind (m := Model) (vis (Request.choose x.down) (fun n => pure (n.map ULift.up ULift.up)))
    (fun s => pure (((M).coprodIso Payload Payload).hom s)) = _
  simp only [vis_bind, pure_bind]

set_option backward.isDefEq.respectTransparency false in
private theorem visible (x : PayloadValue) : (program.targetArrow J M).of x = expected x := by
  unfold SumCase.targetArrow
  rw [caseWithContext_of (m := Model)]
  simp only [Bind.kleisliRight]
  erw [discriminator_of]
  let sIso := Types.binaryCoproductIso ((M).obj program.leftType) ((M).obj program.rightType)
  have decode (s : PayloadValue ⊕ PayloadValue) :
      sIso.hom (((M).coprodIso Payload Payload).hom s) = s :=
    ConcreteCategory.congr_hom sIso.inv_hom_id s
  unfold sIso at decode
  simp only [vis_bind, pure_bind, expected]
  congr 1
  funext choice
  erw [decode]
  cases choice with
  | inl a => exact left_of x (ULift.up a)
  | inr b => exact right_of x (ULift.up b)

set_option backward.isDefEq.respectTransparency false in
theorem visibleElaboration (x : PayloadValue) :
    ∃ f, RegionDenotes J M program.elaborate.property.hasType f ∧
      f.of (PUnit.unit, x) = expected x := by
  refine ⟨_, program.targetDenotes J M (fun _ _ => ⟨rfl, rfl⟩), ?_⟩
  rw [Kleisli.Type.comp_of_eq_kleisliRight]
  change Bind.bind (m := Model) (pure x) (fun y => (program.targetArrow J M).of y) = _
  rw [pure_bind]
  exact visible x

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SelectedSumCaseExample
