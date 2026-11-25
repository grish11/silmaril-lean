module

public import Silmaril.SSA.Isotope.LetIter.Categorical.Syntactic.AbortSequence.Category.Interpretation.Coproducts.Defs
import Silmaril.Proofs.SSA.Isotope.LetIter.Categorical.Syntactic.AbortSequence.CategoryInterpretationCoproducts

/-! # Binary coproduct comparison for the computation interpretation -/

public section

namespace Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic

universe u u₁ u₂ v₁ v₂

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Thesis.LambdaIter.Syn.SynCat (injl injr)

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

/-- The projected object-language left injection agrees with the chosen quotient injection. -/
theorem repairedSyntaxCoprodIso_inl (X Y : Q) :
    (P).map (injl X.as Y.as) ≫ (repairedSyntaxCoprodIso pe X Y).hom = coprod.inl :=
  InterpretationCoproductProofs.syntaxInl pe X Y

/-- The projected object-language right injection agrees with the chosen quotient injection. -/
theorem repairedSyntaxCoprodIso_inr (X Y : Q) :
    (P).map (injr X.as Y.as) ≫ (repairedSyntaxCoprodIso pe X Y).hom = coprod.inr :=
  InterpretationCoproductProofs.syntaxInr pe X Y

local notation "χ" => repairedComputationCoprodIso pe J M coherent shared pureInstr

/-- After applying the coproduct comparison, interpretation preserves the left injection. -/
theorem repairedComputationFunctor_map_inl (X Y : Q) :
    (F).map (coprod.inl : X ⟶ X ⨿ Y) ≫ (χ X Y).hom = coprod.inl :=
  InterpretationCoproductProofs.mapInl pe J M coherent shared pureInstr X Y

/-- After applying the coproduct comparison, interpretation preserves the right injection. -/
theorem repairedComputationFunctor_map_inr (X Y : Q) :
    (F).map (coprod.inr : Y ⟶ X ⨿ Y) ≫ (χ X Y).hom = coprod.inr :=
  InterpretationCoproductProofs.mapInr pe J M coherent shared pureInstr X Y

/-- The inverse of the computed isomorphism is the canonical coproduct comparison. -/
theorem repairedComputationCoprodIso_inv (X Y : Q) :
    coprodComparison (F) X Y = (χ X Y).inv :=
  InterpretationCoproductProofs.comparison pe J M coherent shared pureInstr X Y

/-- Interpretation preserves binary case analysis, expressed as a copairing. -/
theorem repairedComputationFunctor_map_desc {X Y Z : Q} (f : X ⟶ Z) (g : Y ⟶ Z) :
    (F).map (coprod.desc f g) = (χ X Y).hom ≫ coprod.desc ((F).map f) ((F).map g) :=
  InterpretationCoproductProofs.mapDesc pe J M coherent shared pureInstr f g

/-- The computation interpretation preserves binary coproducts. -/
instance repairedComputationFunctor_preservesBinaryCoproducts :
    PreservesColimitsOfShape (Discrete WalkingPair) (F) :=
  InterpretationCoproductProofs.preservesBinaryCoproducts pe J M coherent shared pureInstr

end Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic
