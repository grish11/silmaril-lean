module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.WithTripling.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Tripling.Components.Structural.Defs

/-! # A nine-phase cycle with an explicit carry -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.BinaryFold.WithTripling.NinePhase

open CategoryTheory CategoryTheory.Limits
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton
  (ofType iterateChosen sumIso)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton.ThreeCycle
  (fold step triple cycleRows batchRows transportStep)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton.ValueCoproducts (exactCopair)

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

/-- Execute a round within the same phase on recurrence. -/
noncomputable def stay {A B : Q} (g : A ⟶ B ⨿ A) : Copies A ⟶ B ⨿ Copies A :=
  coprod.desc (g ≫ coprod.map (𝟙 B) coprod.inl)
    (coprod.desc (g ≫ coprod.map (𝟙 B) (coprod.inl ≫ coprod.inr))
      (g ≫ coprod.map (𝟙 B) (coprod.inr ≫ coprod.inr)))

/-- Advance the outer phase each round. Advance the inner phase only on the
outer wrap. Recurrence thus visits all nine phase pairs in one cycle. -/
noncomputable def nineStep {A B : Q} (g : A ⟶ B ⨿ A) : Copies (Copies A) ⟶ B ⨿ Copies (Copies A) :=
  cycleRows (stay pe g) (stay pe g) (step g)

noncomputable abbrev foldInner (A : Q) : Copies (Copies A) ⟶ Copies A :=
  coprod.map (fold A) (coprod.map (fold A) (fold A))

def phase (A : τ) : τ := Silmaril.coprod A (Silmaril.coprod A A)

noncomputable def phaseIso (A : τ) : Obj (phase A) ≅ Copies (Obj A) :=
  sumIso T A (Silmaril.coprod A A) ≪≫ coprod.mapIso (Iso.refl _) (sumIso T A A)

noncomputable def nineIso (A : τ) : Obj (phase (phase A)) ≅ Copies (Copies (Obj A)) :=
  phaseIso pe (phase A) ≪≫
    coprod.mapIso (phaseIso pe A) (coprod.mapIso (phaseIso pe A) (phaseIso pe A))

/-- Fold the literal syntax sum using the three identity payload maps. -/
noncomputable def exactFold (A : τ) : Obj (phase A) ⟶ Obj A :=
  exactCopair T (𝟙 _) (exactCopair T (𝟙 _) (𝟙 _))

/-- Transport the written nine-phase schedule at the exact nested syntax sum. -/
noncomputable def exactStep {A : τ} {B : Q} (g : Obj A ⟶ B ⨿ Obj A) :
    Obj (phase (phase A)) ⟶ B ⨿ Obj (phase (phase A)) :=
  transportStep T (nineIso pe A) (nineStep pe g)

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.BinaryFold.WithTripling.NinePhase
