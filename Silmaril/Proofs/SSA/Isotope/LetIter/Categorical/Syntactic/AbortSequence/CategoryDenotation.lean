module

public import Silmaril.SSA.Isotope.LetIter.Categorical.Syntactic.AbortSequence.Category.Iteration.Thms
public import Silmaril.SSA.Isotope.LetIter.Categorical.Syntactic.AbortSequence.Category.Tensor.Thms
public import Silmaril.SSA.Isotope.LetIter.Categorical.Syntactic.Packing.Defs

/-! # Denotation through the repaired computation projection -/

public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.PremonoidalCategory
open scoped MonoidalCategory

namespace Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic.DenotationProofs

open Silmaril.Isotope.LetIter.LocallyNameless (Derivation Tm)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical
  (duplicate extend retainLeft retainedContext splitMapCoprod caseWithContext contextualLoop)
local notation "bindArrow" => Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind
local notation "pairArrow" => Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.pair

universe u₀ u₁ u₂ v₀ v₁ v₂ uτ uΦ uν u w

section CoproductComparison

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [HasFiniteCoproducts C] [HasFiniteCoproducts D] (P : C ⥤ D)

private theorem comparisonInlInv {X Y : C} (κ : P.obj (X ⨿ Y) ≅ P.obj X ⨿ P.obj Y)
    (inl : P.map (coprod.inl : X ⟶ X ⨿ Y) ≫ κ.hom = coprod.inl) :
    coprod.inl ≫ κ.inv = P.map (coprod.inl : X ⟶ X ⨿ Y) := by
  rw [← inl, Category.assoc, Iso.hom_inv_id, Category.comp_id]

private theorem comparisonInrInv {X Y : C} (κ : P.obj (X ⨿ Y) ≅ P.obj X ⨿ P.obj Y)
    (inr : P.map (coprod.inr : Y ⟶ X ⨿ Y) ≫ κ.hom = coprod.inr) :
    coprod.inr ≫ κ.inv = P.map (coprod.inr : Y ⟶ X ⨿ Y) := by
  rw [← inr, Category.assoc, Iso.hom_inv_id, Category.comp_id]

private theorem mapDesc {X Y Z : C} (κ : P.obj (X ⨿ Y) ≅ P.obj X ⨿ P.obj Y)
    (inl : P.map (coprod.inl : X ⟶ X ⨿ Y) ≫ κ.hom = coprod.inl)
    (inr : P.map (coprod.inr : Y ⟶ X ⨿ Y) ≫ κ.hom = coprod.inr)
    (f : X ⟶ Z) (g : Y ⟶ Z) :
    P.map (coprod.desc f g) = κ.hom ≫ coprod.desc (P.map f) (P.map g) := by
  apply (cancel_epi κ.inv).mp
  rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  apply coprod.hom_ext
  · rw [← Category.assoc, comparisonInlInv P κ inl, ← P.map_comp, coprod.inl_desc, coprod.inl_desc]
  · rw [← Category.assoc, comparisonInrInv P κ inr, ← P.map_comp, coprod.inr_desc, coprod.inr_desc]

end CoproductComparison

section SameValues

variable {V : Type u₀} {C : Type u₁} {D : Type u₂}
  [Category.{v₀} V] [Category.{v₁} C] [Category.{v₂} D]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [PremonoidalCategory D] [SymmetricPremonoidalCategory D]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C] [HasFiniteCoproducts D]
  [DistributiveTensor V] [DistributivePremonoidalCategory C] [DistributivePremonoidalCategory D]
  [Iteration C] [ElgotCategory C] [Iteration D] [ElgotCategory D]
  (J : V ⥤ C) (P : C ⥤ D) [StrongElgotFreydCategory J] [StrongElgotFreydCategory (J ⋙ P)]

/-- Preservation at exactly the interfaces used by native contextual control. -/
structure PreservesControl : Prop where
  retain {R A B : V} (f : J.obj A ⟶ J.obj B) :
    P.map (retainLeft J (R := R) f) = retainLeft (J ⋙ P) (R := R) (P.map f)
  chooseCoprod : ∀ X Y : C,
    ∃ κ : P.obj (X ⨿ Y) ≅ P.obj X ⨿ P.obj Y,
      (P.map (coprod.inl : X ⟶ X ⨿ Y) ≫ κ.hom = coprod.inl) ∧
      (P.map (coprod.inr : Y ⟶ X ⨿ Y) ≫ κ.hom = coprod.inr) ∧
      (∀ f : Y ⟶ X ⨿ Y, CategoryTheory.iterate (P.map f ≫ κ.hom) =
        P.map (CategoryTheory.iterate f))

variable (H : PreservesControl J P)

include H in
private theorem mapExtend {R A : V} (f : J.obj R ⟶ J.obj A) :
    P.map (extend J f) = extend (J ⋙ P) (P.map f) := by
  change P.map (J.map (duplicate R) ≫ retainLeft J (R := R) f) =
    (J ⋙ P).map (duplicate R) ≫ retainLeft (J ⋙ P) (R := R) (P.map f)
  rw [P.map_comp, H.retain (R := R)]
  rfl

include H in
private theorem mapBind {R A B : V} (f : J.obj R ⟶ J.obj A) (g : J.obj (R ⊗ A) ⟶ J.obj B) :
    P.map (bindArrow J f g) = bindArrow (J ⋙ P) (P.map f) (P.map g) := by
  unfold Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind
  rw [P.map_comp, mapExtend J P H]

include H in
private theorem mapPair {R A B : V} (f : J.obj R ⟶ J.obj A) (g : J.obj R ⟶ J.obj B) :
    P.map (pairArrow J f g) = pairArrow (J ⋙ P) (P.map f) (P.map g) := by
  unfold Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.pair
  simp only [mapBind J P H, retainedContext, Functor.map_comp, Functor.comp_map]

private theorem mapSplit (A B : V) (κ : P.obj (J.obj A ⨿ J.obj B) ≅ P.obj (J.obj A) ⨿ P.obj (J.obj B))
    (inl : P.map (coprod.inl : J.obj A ⟶ J.obj A ⨿ J.obj B) ≫ κ.hom = coprod.inl)
    (inr : P.map (coprod.inr : J.obj B ⟶ J.obj A ⨿ J.obj B) ≫ κ.hom = coprod.inr) :
    P.map (splitMapCoprod J A B) ≫ κ.hom = splitMapCoprod (J ⋙ P) A B := by
  have comparison : κ.inv ≫ P.map (coprodComparison J A B) = coprodComparison (J ⋙ P) A B := by
    apply coprod.hom_ext
    · rw [← Category.assoc, comparisonInlInv P κ inl, ← P.map_comp,
        inl_coprodComparison]
      exact (inl_coprodComparison (J ⋙ P) A B).symm
    · rw [← Category.assoc, comparisonInrInv P κ inr, ← P.map_comp,
        inr_coprodComparison]
      exact (inr_coprodComparison (J ⋙ P) A B).symm
  apply (cancel_mono (coprodComparison (J ⋙ P) A B)).mp
  unfold splitMapCoprod
  rw [IsIso.inv_hom_id, ← comparison]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← P.map_comp, IsIso.inv_hom_id, P.map_id]

include H in
private theorem mapCase {R A B Z : V} (e : J.obj R ⟶ J.obj (A ⨿ B))
    (l : J.obj (R ⊗ A) ⟶ J.obj Z) (r : J.obj (R ⊗ B) ⟶ J.obj Z) :
    P.map (caseWithContext J e l r) = caseWithContext (J ⋙ P) (P.map e) (P.map l) (P.map r) := by
  obtain ⟨κ, hl, hr, _⟩ := H.chooseCoprod (J.obj (R ⊗ A)) (J.obj (R ⊗ B))
  unfold caseWithContext
  rw [mapBind J P H]
  simp only [Functor.map_comp, Functor.comp_map, mapDesc P κ hl hr]
  rw [← Category.assoc (P.map (splitMapCoprod J (R ⊗ A) (R ⊗ B))) κ.hom,
    mapSplit J P _ _ κ hl hr]
  rfl

include H in
private theorem mapLoop {R A B : V} (f : J.obj (R ⊗ A) ⟶ J.obj (B ⨿ A)) :
    P.map (contextualLoop J (R := R) f) = contextualLoop (J ⋙ P) (R := R) (P.map f) := by
  obtain ⟨κ, hl, hr, it⟩ := H.chooseCoprod (J.obj (R ⊗ B)) (J.obj (R ⊗ A))
  unfold contextualLoop
  rw [P.map_comp, ← it]
  simp only [Functor.map_comp, Functor.comp_map, H.retain (R := R), Category.assoc]
  rw [mapSplit J P _ _ κ hl hr]

variable {τ : Type uτ} [TypeFormers τ] (M : TypeModel τ V)
  {ν : Type uν} [DecidableEq ν] {Φ : Type uΦ} [HasTy Φ τ]
  [InstructionModel J M Φ] [InstructionModel (J ⋙ P) M Φ]
  (instr : ∀ f : Φ, P.map (InstructionModel.denote (J := J) (M := M) f) =
    InstructionModel.denote (J := J ⋙ P) (M := M) f)

include H instr

/-- Cross-model naturality at a fixed value/type interpretation. -/
private theorem mapDenote {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n} {t : Tm ν Φ n} {A : τ}
    (d : Derivation Φ Γ β t A) :
    P.map (denote J M d) = denote (J ⋙ P) M d := by
  induction d <;>
    simp only [denote, Functor.map_comp, Functor.comp_map, mapBind J P H,
      mapPair J P H, mapCase J P H, mapLoop J P H, *]

/-- Precompose the denotation comparison by any common pure environment map. -/
private theorem mapPrecomposeDenote {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n} {t : Tm ν Φ n} {A : τ}
    {E : V} (k : E ⟶ envObj M Γ β) (d : Derivation Φ Γ β t A) :
    P.map (J.map k ≫ denote J M d) = (J ⋙ P).map k ≫ denote (J ⋙ P) M d := by
  rw [P.map_comp, mapDenote J P H M instr d]
  rfl

end SameValues

section RepairedRetention

open Silmaril.Thesis.LambdaIter.Syn.SynCat (ValueCat values)

variable {τ Φ ε : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] (pe : ε)
  [SymmetricPremonoidalCategory (RepairedSynCat (τ := τ) (Φ := Φ) pe)]
  [FreydCategory (repairedValues (τ := τ) (Φ := Φ) pe)]

local notation "S" => signature (τ := τ) (Φ := Φ) pe
local notation "I" => values S
local notation "P" => repairedProjection (τ := τ) (Φ := Φ) pe
local notation "Jq" => repairedValues (τ := τ) (Φ := Φ) pe
local notation "tIso" K => Functor.StrongPremonoidal.tensorIso (J := K)

theorem repairedProjection_retainLeft {R A B : ValueCat S} (f : (I).obj A ⟶ (I).obj B)
    (tensorA : (P).map ((tIso I) R A).hom = ((tIso Jq) R A).hom)
    (tensorB : (P).map ((tIso I) R B).hom = ((tIso Jq) R B).hom) :
    (P).map (retainLeft I (R := R) f) = retainLeft Jq (R := R) ((P).map f) := by
  have tensorInv : (P).map ((tIso I) R A).inv = ((tIso Jq) R A).inv := by
    apply (cancel_mono ((tIso Jq) R A).hom).mp
    rw [← tensorA, ← (P).map_comp, Iso.inv_hom_id, (P).map_id, tensorA, Iso.inv_hom_id]
  simp only [retainLeft, leftTensor, id_whiskerRight, Category.id_comp, Functor.map_comp]
  rw [tensorInv, tensorB, ← repairedWhiskerLeft_map pe ((I).obj R) f]
  rfl

end RepairedRetention

section RepairedSyntactic

open Silmaril.Thesis.LambdaIter.Syn.SynCat (ValueCat values)

variable {τ Φ ε : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] (pe : ε)
  [SymmetricPremonoidalCategory (RepairedSynCat (τ := τ) (Φ := Φ) pe)]
  [DistributivePremonoidalCategory (RepairedSynCat (τ := τ) (Φ := Φ) pe)]
  [StrongElgotFreydCategory (repairedValues (τ := τ) (Φ := Φ) pe)]

local notation "modelSig" => signature (τ := τ) (Φ := Φ) pe
local notation "P" => repairedProjection (τ := τ) (Φ := Φ) pe
local notation "Jq" => repairedValues (τ := τ) (Φ := Φ) pe
local notation "model" => typeModel (τ := τ) (Φ := Φ) pe

variable
  (tensorHom : ∀ R A : ValueCat (signature (τ := τ) (Φ := Φ) pe),
    (repairedProjection pe).map
      (Functor.StrongPremonoidal.tensorIso (J := values (signature pe)) R A).hom =
    (Functor.StrongPremonoidal.tensorIso (J := repairedValues pe) R A).hom)

include tensorHom in

private theorem repairedControl : PreservesControl (values modelSig) P where
  retain {R A B} f := repairedProjection_retainLeft pe f (tensorHom R A) (tensorHom R B)
  chooseCoprod X Y := ⟨repairedProjectionCoprodIso pe X Y,
    repairedProjection_coprodIso_inl pe X Y, repairedProjection_coprodIso_inr pe X Y,
    repairedIteration_map pe⟩

variable
  [InstructionModel (repairedValues (τ := τ) (Φ := Φ) pe) (typeModel (τ := τ) (Φ := Φ) pe) Φ]
  (instr : ∀ f : Φ, (repairedProjection pe).map ((instructionModel (τ := τ) pe).denote f) =
    InstructionModel.denote (J := repairedValues pe) (M := typeModel (τ := τ) (Φ := Φ) pe) f)

include tensorHom instr

theorem repairedDenote_map {ν : Type w} [DecidableEq ν] {Γ : Ctx ν τ}
    {n : Nat} {β : BoundCtx τ n} {t : Tm ν Φ n} {A : τ}
    (d : Derivation Φ Γ β t A) :
    (P).map (denoteInSyntax pe d) = denote Jq model d := by
  let _ := instructionModel (τ := τ) (Φ := Φ) pe
  exact mapDenote (values modelSig) P (repairedControl pe tensorHom) model instr d

theorem repairedPacked_map {n : Nat} {β : BoundCtx τ n} {t : Tm Empty Φ n} {A : τ}
    (d : Derivation Φ (Ctx.nil : Ctx Empty τ) β t A) :
    (P).map (packedNative pe d) =
      (Jq).map (packedEnvIso (Φ := Φ) pe β).inv ≫ denote Jq model d := by
  let _ := instructionModel (τ := τ) (Φ := Φ) pe
  exact mapPrecomposeDenote (values modelSig) P (repairedControl pe tensorHom) model instr
    (packedEnvIso (Φ := Φ) pe β).inv d

end RepairedSyntactic

end Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic.DenotationProofs
