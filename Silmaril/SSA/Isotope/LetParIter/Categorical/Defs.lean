module

public import Silmaril.SSA.Isotope.LetParIter.Defs
public import Silmaril.SSA.Isotope.LetIter.Categorical.Parallel.Defs

/-! # Categorical denotation of mixed LetParIter derivations -/

@[expose] public section

namespace Silmaril.Isotope.LetParIter.Categorical

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Parallel (Derivation)
open LetIter.Semantics.Categorical
  (TypeModel InstructionModel envObj freeLookup boundVar envSnocIso envPairHom)
open LetIter.ProofRelevant.Semantics.Categorical
  (caseWithContext contextualLoop pair)

local notation "bindArrow" => LetIter.ProofRelevant.Semantics.Categorical.bind

universe v₁ v₂ u₁ u₂ u v w

variable {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] [∀ X Y : C, Preorder (X ⟶ Y)]
  (J : V ⥤ C) [StrongElgotFreydCategory J] (P : FreydCategory.OrderedParallel J)
  {τ : Type u} [TypeFormers τ] (M : TypeModel τ V)
  {ν : Type v} [DecidableEq ν] {Φ : Type w} [HasTy Φ τ] [InstructionModel J M Φ]

/-- Interpret the shared iteration tier, using the native combinators for its inherited
clauses and the pure value diagonal followed by the chosen parallel operation for Par. -/
noncomputable def denote {Γ : Ctx ν τ} : {n : Nat} →
    {β : BoundCtx τ n} → {t : Tm ν Φ n} → {A : τ} →
    Derivation Φ Γ β t A → (J.obj (envObj M Γ β) ⟶ J.obj (M.obj A))
  | _, _, _, _, .fv h => J.map (freeLookup M _ h)
  | _, _, _, _, .bv => J.map (boundVar M _)
  | _, _, _, _, .op ha => denote ha ≫ InstructionModel.denote _
  | _, β, _, _, .let₁ ha hb => bindArrow J (denote ha) <|
      J.map (envSnocIso M Γ β _).hom ≫ denote hb
  | _, _, _, _, .unit =>
      J.map (CartesianMonoidalCategory.toUnit _ ≫ M.unitIso.inv)
  | _, _, _, _, .pair ha hb =>
      pair J (denote ha) (denote hb) ≫ J.map (M.productIso _ _).inv
  | _, β, _, _, .let₂ ha hc => bindArrow J (denote ha) <|
      J.map ((𝟙 _) ⊗ₘ (M.productIso _ _).hom) ≫
        J.map (envPairHom M Γ β _ _) ≫ denote hc
  | _, _, _, _, .inl ha =>
      denote ha ≫ J.map (coprod.inl ≫ (M.coprodIso _ _).inv)
  | _, _, _, _, .inr hb =>
      denote hb ≫ J.map (coprod.inr ≫ (M.coprodIso _ _).inv)
  | _, β, _, _, .case he hl hr =>
      caseWithContext J (denote he ≫ J.map (M.coprodIso _ _).hom)
        (J.map (envSnocIso M Γ β _).hom ≫ denote hl)
        (J.map (envSnocIso M Γ β _).hom ≫ denote hr)
  | _, _, _, _, .abort ha =>
      denote ha ≫ J.map (M.emptyIsInitial.to (M.obj _))
  | _, β, _, _, .iter ha hb => bindArrow J (denote ha) <|
      contextualLoop J
        (J.map (envSnocIso M Γ β _).hom ≫ denote hb ≫
          J.map (M.coprodIso _ _).hom)
  | _, _, _, _, .par ha hb =>
      P.par (denote ha) (denote hb) ≫ J.map (M.productIso _ _).inv
termination_by structural _ _ _ _ d => d

end Silmaril.Isotope.LetParIter.Categorical
