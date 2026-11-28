module

public import Silmaril.SSA.Isotope.LambdaSSA.Semantics.ITree.Typed.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Categorical.Singleton.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Semantics.ITree.TypedRegion
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Semantics.ITree.TypedTerm
import Silmaril.SSA.Isotope.LambdaSSA.Semantics.Erasure.Defs

/-! # Singleton coordinates of exact categorical ITree denotation -/

public section

universe v q

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Interaction.Typed

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Semantics
open Silmaril.Isotope.LambdaSSA.Semantics.Interaction
open Silmaril.Isotope.LambdaSSA.Semantics.Interaction.Typed
open Silmaril.Isotope.LambdaSSA.Semantics.Agreement
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics (InstructionModel)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (typeJ)
open Silmaril.Isotope.Semantics (encodeValue)
open Silmaril.Elgot.ITree

variable {κ : Type (v + 1)} [AtomValues κ] {E : Type v → Type v}
  {Φ : Type q} [HasTy Φ (Ty κ)] [HasEff Φ Bool]

attribute [local instance] typeModel

variable [InstructionModel Φ (Ty κ) Bool (ModelTree E)]
  (raw : Primitive E Φ (Sigma (AtomValues.carrier (κ := κ))))

local notation "V" => AtomValues.carrier (κ := κ)
local notation "TM" => ModelTree E
local notation "J" => typeJ (m := TM)
local notation "T" => Categorical.ofMonadicTypeModel (τ := Ty κ)

attribute [local instance] categoricalInstructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

omit [HasTy Φ (Ty κ)] [HasEff Φ Bool] [InstructionModel Φ (Ty κ) Bool TM] in
private theorem term_erasure_tree (env : Env (Sigma V)) (t : Tm Φ) :
    Erasure.term (m := TM) diverge raw env t = term raw env t := by
  induction t generalizing env <;> simp [Erasure.term, term, *]
  all_goals rfl

omit [HasTy Φ (Ty κ)] [HasEff Φ Bool] [InstructionModel Φ (Ty κ) Bool TM] in
private theorem region_erasure_tree (env : Env (Sigma V)) (r : Region Φ) :
    Erasure.region (m := TM) diverge diverge raw env r = region raw env r := by
  induction r generalizing env <;> simp [Erasure.region, region, term_erasure_tree, *]
  all_goals rfl

private theorem encodeSingleton (A : Ty κ) (x : Categorical.labelObj T [A]) :
    encodeCategoricalLabel [A] x =
      (0, encodeValue V A (Categorical.singletonLabelPayload T A x)) := by
  obtain ⟨x, rfl⟩ := (Monadic.LabelValue.categoricalEquiv [A]).surjective x
  change Sum (Ty.denote V A) PEmpty at x
  rcases x with a | z
  · have hinj : (Monadic.LabelValue.categoricalEquiv [A]) (Sum.inl a) =
        Categorical.labelInject T 0 (rfl : At [A] 0 A) a :=
      Monadic.LabelValue.categoricalEquiv_inject 0 (rfl : At [A] 0 A) a
    rw [hinj, encodeCategoricalLabel_inject]
    have drop : Categorical.labelInject T 0 (rfl : At [A] 0 A) ≫
        Categorical.singletonLabelPayload T A = 𝟙 _ := by
      rw [Categorical.labelInject_eq_sigma]
      rw [Category.assoc, Categorical.singletonLabelPayload, Sigma.ι_comp_desc]
      simp
    have ha := ConcreteCategory.congr_hom drop (show (T).obj A from a)
    change Categorical.singletonLabelPayload T A (Categorical.labelInject T 0 (rfl : At [A] 0 A) a) =
      a at ha
    rw [ha]
  · exact z.elim

theorem singletonDenote_tree
    (compat : Compatible (κ' := κ) ⟨fun f x =>
      InstructionModel.denote (τ := Ty κ) (ε := Bool) (m := TM) f x⟩ raw)
    {A B : Ty κ} {r : Region Φ} (hr : Region.HasType [A] r [B])
    (a : Ty.denote V A) (env : Env (Sigma V)) :
    ((show TM _ from (Categorical.denoteSingletonRegion J T hr).of a) >>=
      fun b => pure (0, encodeValue V B b)) =
        region raw (extend env (encodeValue V A a)) r := by
  have empty : EncodesEnv (Γ := []) PUnit.unit env := by
    intro i D h
    simp [At] at h
  have agree := regionDenotes_erased raw diverge diverge compat (Categorical.denoteRegion_spec J T hr)
    (PUnit.unit, a) (extend env (encodeValue V A a)) (encodesEnv_extend empty a)
  rw [region_erasure_tree] at agree
  unfold Categorical.denoteSingletonRegion
  simp only [Kleisli.Type.comp_of_eq_kleisliRight, Bind.kleisliRight, mapTree_of, bind_assoc, pure_bind]
  have input : (λ_ ((T).obj A)).inv a = (PUnit.unit, a) := rfl
  rw [input]
  simp only [encodeSingleton, envToCategorical] at agree
  exact agree

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Interaction.Typed
