module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedProductProducers.Intrinsic.SumCase.Tree.Example.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedProductProducers.Intrinsic.SumCase.Tree.Thms
import Silmaril.SSA.Isotope.LetIter.Categorical.Kleisli.Thms

/-! # The selected nested case runs the inner discriminator only on the left reply -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SelectedCaseTreeExample

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Semantics.Categorical Semantics.Interaction.Typed
open Paper.WithComputedProductProducers.Intrinsic
open SumCase.Example (Atom Payload Labels PayloadValue Model Op Request exit0 exit1)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (typeJ caseWithContext caseWithContext_of)
open Silmaril.Elgot.ITree CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory

open CaseTree.Example

attribute [local instance] typeModel categoricalInstructions

local notation "J" => typeJ (m := Model)
local notation "M" => ofMonadicTypeModel (τ := Ty Atom)

set_option backward.isDefEq.respectTransparency false in
private theorem choose_case_of {R D : Type 1}
    (f : (J).obj R ⟶ (J).obj ((M).obj (coprod Payload Payload)))
    (l r : (J).obj (R × PayloadValue) ⟶ (J).obj D)
    (x : R) (v : PayloadValue)
    (hf : (f.of x : Model _) = vis (Request.choose v.down) (fun n => pure (n.map ULift.up ULift.up))) :
    (caseWithContext J (f ≫ (J).map ((M).coprodIso Payload Payload).hom) l r).of x =
      vis (Request.choose v.down) (fun
        | .inl a => l.of (x, ULift.up a)
        | .inr b => r.of (x, ULift.up b)) := by
  rw [caseWithContext_of (m := Model)]
  simp only [Kleisli.Type.comp_of_eq_kleisliRight, Bind.kleisliRight]
  erw [hf]
  let sIso := Types.binaryCoproductIso PayloadValue PayloadValue
  have coordinate (s : PayloadValue ⊕ PayloadValue) :
      sIso.hom (((M).coprodIso Payload Payload).hom s) = s :=
    ConcreteCategory.congr_hom sIso.inv_hom_id s
  unfold sIso at coordinate
  simp only [mapTree_of, vis_bind, pure_bind]
  congr 1
  funext reply
  erw [coordinate]
  cases reply <;> rfl

set_option backward.isDefEq.respectTransparency false in
private theorem inner_visible (x a : PayloadValue) : (inner.targetArrow J M).of (x, a) = expectedInner x a := by
  simp only [inner, CaseTree.targetArrow]
  erw [choose_case_of _ _ _ (x, a) a]
  · congr 1
    funext reply
    cases reply <;> simp only [Program.targetArrow, Term.targetArrow, ← (J).map_comp] <;> rfl
  · simp only [Term.targetArrow, Kleisli.Type.comp_of_eq_kleisliRight, Bind.kleisliRight]
    change Bind.bind (m := Model) (pure a) (fun (b : PayloadValue) =>
      vis (Request.choose b.down) (fun n => pure (n.map ULift.up ULift.up))) = _
    rw [pure_bind]

set_option backward.isDefEq.respectTransparency false in
private theorem visible (x : PayloadValue) : (nested.targetArrow J M).of x = expected x := by
  simp only [nested, CaseTree.targetArrow]
  erw [choose_case_of _ _ _ x x]
  · congr 1
    funext reply
    cases reply with
    | inl a =>
      simp only [Kleisli.Type.comp_of_eq_kleisliRight, Bind.kleisliRight]
      change Bind.bind (m := Model) (pure (x, ULift.up a))
        (fun p => (inner.targetArrow J M).of p) = _
      simpa only [pure_bind] using inner_visible x (ULift.up a)
    | inr b =>
      simp only [Program.targetArrow, Term.targetArrow, ← (J).map_comp]
      rfl
  · simp only [Term.targetArrow, Category.id_comp]
    rfl

set_option backward.isDefEq.respectTransparency false in
theorem visible_elaboration (x : PayloadValue) :
    ∃ f, RegionDenotes J M nested.elaborate.property.hasType f ∧
      f.of (PUnit.unit, x) = expected x := by
  refine ⟨_, nested.targetDenotes J M (fun _ _ => ⟨rfl, rfl⟩), ?_⟩
  rw [Kleisli.Type.comp_of_eq_kleisliRight]
  change Bind.bind (m := Model) (pure x) (fun y => (nested.targetArrow J M).of y) = _
  rw [pure_bind]
  exact visible x

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SelectedCaseTreeExample
