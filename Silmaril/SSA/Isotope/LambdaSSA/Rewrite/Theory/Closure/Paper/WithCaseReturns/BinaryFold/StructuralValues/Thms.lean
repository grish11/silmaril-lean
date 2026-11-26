module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Iteration.Chosen.Blocks.ThreeCycle.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.StructuralValues.Freyd.Iteration.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BinaryFoldStructuralValues

/-! # A block fold and the remaining three-round law in BinaryFold -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.BinaryFold

open CategoryTheory CategoryTheory.Limits
open Paper.Extension.Singleton
open Paper.Extension.Singleton.ValueCoproducts (exactCopair)
open Paper.Extension.Singleton.StructuralValues (ofSyntaxType inclusion IncludesUnitEta StructuralUniformity)

universe u v w
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε)

local notation "S" => JoinedStep (τ := τ) (Φ := Φ) pe
local notation "Q" => TypeCategory (τ := τ) (Φ := Φ) pe
local notation "I" => iterateChosen S

instance unitEta : Fact (IncludesUnitEta S) :=
  ⟨fun h => .inl (WithCaseReturns.includeUnit pe h)⟩

/-- Merge the copied block and keep the other block. The right copy can exit
or enter the other block, and any recurrence within the copied block enters
the left copy. The other rows and the quotient square are arbitrary. -/
theorem uniformity_of_right_switch_block {A D B : Q}
    (d : A ⨿ (D ⨿ D) ⟶ (B ⨿ A) ⨿ (D ⨿ D)) (e : A ⨿ D ⟶ (B ⨿ A) ⨿ D)
    (square : d ≫ coprod.map (𝟙 (B ⨿ A)) (coprod.desc (𝟙 D) (𝟙 D)) =
      coprod.map (𝟙 A) (coprod.desc (𝟙 D) (𝟙 D)) ≫ e)
    (switch : coprod.inr ≫ (coprod.inr ≫ d) =
      (coprod.inr ≫ e) ≫ coprod.map (𝟙 (B ⨿ A)) (coprod.inl : D ⟶ D ⨿ D)) :
    I (d ≫ (coprod.associator B A (D ⨿ D)).hom) =
      coprod.map (𝟙 A) (coprod.desc (𝟙 D) (𝟙 D)) ≫ I (e ≫ (coprod.associator B A D).hom) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BinaryFoldStructuralValues.uniformity_of_right_switch_block
    pe d e square switch

local infixr:65 " ⊕ₜ " => Silmaril.coprod

/-- Merge the two copies of the right-hand state and keep the left summand. -/
noncomputable def blockFold (A D : τ) :
    ofSyntaxType S (A ⊕ₜ (D ⊕ₜ D)) ⟶ ofSyntaxType S (A ⊕ₜ D) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BinaryFoldStructuralValues.blockFold pe A D

/-- The chosen-coproduct state map of the block theorem is induced by this structural value. -/
theorem blockFold_eq (A D : τ) :
    (inclusion S).map (blockFold pe A D) ≫ (sumIso S A D).hom =
    ((sumIso S A (D ⊕ₜ D)).hom ≫ coprod.map (𝟙 (ofType S A)) (sumIso S D D).hom) ≫
      coprod.map (𝟙 (ofType S A)) (coprod.desc (𝟙 (ofType S D)) (𝟙 (ofType S D))) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BinaryFoldStructuralValues.blockFold_eq pe A D

/-- The three-copy fold on the exact syntax sum is a structural value. -/
noncomputable def ternaryFold (A : τ) :
    ofSyntaxType S (Silmaril.coprod A (Silmaril.coprod A A)) ⟶ ofSyntaxType S A :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BinaryFoldStructuralValues.ternaryFold pe A

/-- The structural fold forwards all three payloads through the exact coproduct. -/
theorem ternaryFold_arrow (A : τ) :
    (inclusion S).map (ternaryFold pe A) =
      exactCopair S (𝟙 (ofType S A)) (exactCopair S (𝟙 (ofType S A)) (𝟙 (ofType S A))) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BinaryFoldStructuralValues.ternaryFold_arrow pe A

/-- The three-copy step at the exact syntax sum boundary. -/
noncomputable def ternaryStep {A : τ} {B : Q} (g : ofType S A ⟶ B ⨿ ofType S A) :
    ofType S (Silmaril.coprod A (Silmaril.coprod A A)) ⟶
      B ⨿ ofType S (Silmaril.coprod A (Silmaril.coprod A A)) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BinaryFoldStructuralValues.ternaryStep pe g

/-- The three-cycle commutes with the genuine structural fold at the exact syntax types. -/
theorem ternaryFold_square {A : τ} {B : Q} (g : ofType S A ⟶ B ⨿ ofType S A) :
    ternaryStep pe g ≫ coprod.map (𝟙 B) ((inclusion S).map (ternaryFold pe A)) =
      (inclusion S).map (ternaryFold pe A) ≫ g :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BinaryFoldStructuralValues.ternaryFold_square pe g

/-- Enter the exact three-copy step at its first phase. -/
theorem ternaryStep_iterate_first {A : τ} {B : Q} (g : ofType S A ⟶ B ⨿ ofType S A) :
    (sumCofan S A (Silmaril.coprod A A)).inl ≫ I (ternaryStep pe g) = I (ThreeCycle.triple g) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BinaryFoldStructuralValues.ternaryStep_iterate_first pe g

/-- Uniformity for the three-cycle is exactly the three-round law in BinaryFold. -/
theorem ternaryFold_iff_triple {A : τ} {B : Q} (g : ofType S A ⟶ B ⨿ ofType S A) :
    I (ternaryStep pe g) = (inclusion S).map (ternaryFold pe A) ≫ I g ↔
      I (ThreeCycle.triple g) = I g :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BinaryFoldStructuralValues.ternaryFold_iff_triple pe g

/-- The full structural uniformity field implies three-round batching
for arbitrary retained steps in BinaryFold. -/
theorem triple_step_of_uniformity (uniform : StructuralUniformity S)
    {A : τ} {B : Q} (g : ofType S A ⟶ B ⨿ ofType S A) :
    I (ThreeCycle.triple g) = I g :=
  (ternaryFold_iff_triple pe g).mp (uniform _ _ (ternaryFold pe A) (ternaryFold_square pe g))

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.BinaryFold
