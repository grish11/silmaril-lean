module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.WithTripling.NinePhase.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.StructuralValues.Coproducts.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BinaryFoldNinePhase

/-! # Uniformity for two composed three-copy folds -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.BinaryFold.WithTripling.NinePhase

open CategoryTheory CategoryTheory.Limits
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton
  (ofType iterateChosen)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton.ThreeCycle
  (fold step triple batchRows)

universe u v w
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε)

set_option hygiene false in
local notation "T" => Step (τ := τ) (Φ := Φ) pe
set_option hygiene false in
local notation "Q" => Paper.Extension.Singleton.TypeCategory T
local notation "Copies" A:max => (A ⨿ (A ⨿ A))
set_option hygiene false in
local notation "Obj" => ofType T
set_option hygiene false in
local notation "I" => iterateChosen T

open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton.StructuralValues (HomProperty)

/-- Closing the first phase batches exactly three rounds and carries into
the next inner phase only after the third recurrence. -/
theorem batch_eq {A B : Q} (g : A ⟶ B ⨿ A) :
    batchRows (stay pe g) (stay pe g) (step g) = step (triple g) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BinaryFoldNinePhase.batch_eq pe g

/-- The two local phase folds compose their actual squares and iterates. -/
theorem uniformity {A B : Q} (g : A ⟶ B ⨿ A) :
    nineStep pe g ≫ coprod.map (𝟙 B) (foldInner pe A ≫ fold A) = (foldInner pe A ≫ fold A) ≫ g ∧
      I (nineStep pe g) = (foldInner pe A ≫ fold A) ≫ I g :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BinaryFoldNinePhase.uniformity pe g

/-- Each exact fold is a structural value at arbitrary retained types. -/
theorem exactFold_mem (A : τ) : HomProperty T (exactFold pe A) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BinaryFoldNinePhase.exactFold_mem pe A

theorem exactFold_comp_mem (A : τ) : HomProperty T (exactFold pe (phase A) ≫ exactFold pe A) :=
  (HomProperty T).comp_mem _ _ (exactFold_mem pe (phase A)) (exactFold_mem pe A)

/-- The composite pure fold is uniform for the actual nine-phase cycle,
at the literal nested type and with the original outward object. -/
theorem exact_uniformity {A : τ} {B : Q} (g : Obj A ⟶ B ⨿ Obj A) :
    exactStep pe g ≫ coprod.map (𝟙 B) (exactFold pe (phase A) ≫ exactFold pe A) =
        (exactFold pe (phase A) ≫ exactFold pe A) ≫ g ∧
      I (exactStep pe g) = (exactFold pe (phase A) ≫ exactFold pe A) ≫ I g :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BinaryFoldNinePhase.exact_uniformity pe g

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.BinaryFold.WithTripling.NinePhase
