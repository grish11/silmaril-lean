module

public import Silmaril.SSA.Isotope.LetIter.Categorical.Syntactic.AbortSequence.Category.Interpretation.Thms
public import Silmaril.SSA.Isotope.LetIter.Categorical.Syntactic.AbortSequence.Category.Coproducts.Thms

/-! # Binary coproduct comparison for the computation interpretation -/

@[expose] public section

namespace Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic

universe u u₁ u₂ v₁ v₂

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Thesis.LambdaIter.Syn.SynCat (cop copIso)

variable {τ Φ ε : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] (pe : ε)
  {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  [FreydCategory.CentralUnit J] (M : TypeModel τ V) [InstructionModel J M Φ]

local notation "P" => repairedProjection (τ := τ) (Φ := Φ) pe
local notation "Q" => RepairedSynCat (τ := τ) (Φ := Φ) pe

variable
  (coherent : TypingCoherent (ν := Empty) J M Φ)
  (shared : ∀ R T : V, ∃ e : J.obj R ⊗ J.obj T = J.obj (R ⊗ T),
    Functor.StrongPremonoidal.tensorIso (J := J) R T = eqToIso e)
  (pureInstr : ∀ f : Φ, IsPure pe f → ∃ p : M.obj (instrSrc f) ⟶ M.obj (instrTrg f),
    InstructionModel.denote (J := J) (M := M) f = J.map p)

local notation "F" => repairedComputationFunctor pe J M coherent shared pureInstr

/-- The projected object-language sum agrees with the chosen quotient coproduct. -/
noncomputable def repairedSyntaxCoprodIso (X Y : Q) :
    (P).obj (cop X.as Y.as) ≅ X ⨿ Y :=
  (P).mapIso (copIso X.as Y.as) ≪≫ repairedProjectionCoprodIso pe X.as Y.as

/-- Interpret a chosen syntax coproduct using the target type and value coproduct comparisons. -/
noncomputable def repairedComputationCoprodIso (X Y : Q) :
    (F).obj (X ⨿ Y) ≅ (F).obj X ⨿ (F).obj Y :=
  ((F).mapIso (repairedSyntaxCoprodIso pe X Y)).symm ≪≫
    J.mapIso (M.coprodIso X.as.ty Y.as.ty) ≪≫
      (asIso (coprodComparison J (M.obj X.as.ty) (M.obj Y.as.ty))).symm

end Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic
