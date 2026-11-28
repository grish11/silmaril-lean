module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.StructuralValues.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Iteration.Chosen.Blocks.ThreeCycle.Factorization.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Semantics.ITree.Typed.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Denotation.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Categorical.Singleton.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Semantics.Erasure.Thms
public import Silmaril.Semantics.Calco2019.Maybe.Types.Thms

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BinaryFoldThreeCycle

open Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Semantics.Categorical
open Semantics.Interaction.Typed (AtomValues typeModel)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics (InstructionModel)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (typeJ)
open Paper.WithCaseReturns.BinaryFold (JoinedStep)
open Paper.Extension.Singleton
open Paper.Extension.Singleton.ThreeCycle
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory

universe u v w
variable {κ : Type u} [AtomValues κ] {Φ : Type v} [HasTy Φ (Ty κ)]
  {ε : Type w} [HasEff Φ ε] (pe : ε)

local notation "S" => JoinedStep (τ := Ty κ) (Φ := Φ) pe
local notation "Obj" => ofType S
local notation "Val" => Ty.denote (AtomValues.carrier (κ := κ))
set_option hygiene false in
set_option quotPrecheck false in
local notation "Maybe" => (Silmaril.Calco2019.Maybe.Types.Model : Type u → Type u)
local notation "M" => ofMonadicTypeModel (τ := Ty κ)
local notation "K" => typeJ (m := Maybe)

attribute [local instance] typeModel

local instance : HasEff Φ Bool where
  eff _ := true

local instance : InstructionModel Φ (Ty κ) Bool Maybe where
  denote _ _ := .inr PUnit.unit
  denotePure _ h := by cases h
  denote_pure _ h := by cases h

local instance : Silmaril.Isotope.LetIter.Semantics.Categorical.InstructionModel K M Φ :=
  ofMonadicInstructionModel (ε := Bool)

local instance : RegionTypingCoherent (Φ := Φ) K M :=
  Semantics.Erasure.regionTypingCoherent (κ := κ) (Φ := Φ) (m := Maybe)
    (fun _ _ => .inr PUnit.unit) (.inr PUnit.unit) (.inr PUnit.unit)
    (fun _ _ => rfl)

private theorem seedDenotes : SeedDenotes (Seed := S) K M := by
  intro Γ r s h seed hr hs
  have eq := Paper.WithCaseReturns.BinaryFold.Eqv.sound pe K M (fun _ _ => ⟨rfl, rfl⟩)
    (.extra hr hs seed) hr hs
  exact ⟨_, denoteRegion_spec K M hr, eq.symm ▸ denoteRegion_spec K M hs⟩

set_option backward.isDefEq.respectTransparency false in
private theorem distinct_tags {A : Ty κ} (a : Val A) :
    (coprod.inl : Obj A ⟶ Obj A ⨿ Obj A) ≠ coprod.inr := by
  intro eq
  have exactEq : (sumCofan S A A).inl = (sumCofan S A A).inr := by
    apply (cancel_mono (sumIso S A A).hom).mp
    simpa only [sumCofan_inl_sumIso_hom, sumCofan_inr_sumIso_hom] using eq
  let F := denoteFunctor K M (fun _ _ => ⟨rfl, rfl⟩) (seedDenotes (Φ := Φ) pe)
  have observed := congrArg (fun f => F.map f) exactEq
  change F.map ((projection S).map (Paper.TypeCategory.sumCofan A A).inl) =
    F.map ((projection S).map (Paper.TypeCategory.sumCofan A A).inr) at observed
  rw [Paper.TypeCategory.sumCofan_inl, Paper.TypeCategory.sumCofan_inr] at observed
  dsimp only [F] at observed
  rw [denoteFunctor_map_ofRegion, denoteFunctor_map_ofRegion,
    denoteSingletonRegion_br K M (.inl (.var (i := 0) rfl)),
    denoteSingletonRegion_br K M (.inr (.var (i := 0) rfl))] at observed
  simp only [lookup, ← Functor.map_comp] at observed
  change (K).map (coprod.inl ≫ (Types.binaryCoproductIso (Val A) (Val A)).hom) =
    (K).map (coprod.inr ≫ (Types.binaryCoproductIso (Val A) (Val A)).hom) at observed
  rw [Types.binaryCoproductIso_inl_comp_hom, Types.binaryCoproductIso_inr_comp_hom] at observed
  have out := congrArg (fun f => f.of a) observed
  change (Sum.inl (Sum.inl a) : Maybe (Val (Silmaril.coprod A A))) = Sum.inl (Sum.inr a) at out
  cases Sum.inl.inj out

theorem no_partial_fold_on_repeat {A : Ty κ} (a : Val A) (keep : Fin 3)
    (next : Obj A ⨿ Obj A ⟶ Obj A ⨿ (Obj A ⨿ Obj A)) :
    step (coprod.inr : Obj A ⟶ Obj A ⨿ Obj A) ≫ coprod.map (𝟙 (Obj A)) (partialFold (Obj A) keep) ≠
      partialFold (Obj A) keep ≫ next :=
  no_partial_fold_square _ (𝟙 _) rfl (by simpa only [Category.id_comp] using distinct_tags pe a)
    coprod.inl keep next

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BinaryFoldThreeCycle
