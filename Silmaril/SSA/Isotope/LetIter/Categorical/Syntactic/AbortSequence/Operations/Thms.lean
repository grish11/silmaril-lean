module

public import Silmaril.SSA.Isotope.LetIter.Categorical.Syntactic.AbortSequence.Thms
import Silmaril.Proofs.SSA.Isotope.LetIter.Categorical.Syntactic.AbortSequence.Operations

/-! # Congruence of syntactic operations for the repaired hom relation -/

public section

universe u

namespace Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Thesis.LambdaIter (Sig)
open Silmaril.Thesis.LambdaIter.Syn (SynCat)
open Silmaril.Thesis.LambdaIter.Syn.SynCat
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical
  (extend retainLeft contextualLoop caseWithContext)
local notation "bindArrow" => Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind

variable {τ Φ ε : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε]

variable (pe : ε)

local notation "modelSig" => signature (τ := τ) (Φ := Φ) pe
local notation "classOf" "(" P "," Q ")" =>
  repairedHomClass (τ := τ) (Φ := Φ) pe (X := P) (Y := Q)

/-- Composition respects the repaired classes of both inputs. -/
theorem repairedHomClass_comp_congr {X Y Z : SynCat modelSig}
    {f f' : X ⟶ Y} {g g' : Y ⟶ Z}
    (hf : classOf (X, Y) f = classOf (X, Y) f')
    (hg : classOf (Y, Z) g = classOf (Y, Z) g') :
    classOf (X, Z) (f ≫ g) = classOf (X, Z) (f' ≫ g') :=
  AbortSequenceProofs.comp_congr pe hf hg

/-- Sequential pairing respects the repaired classes of both inputs. -/
theorem repairedHomClass_pairArrows_congr {X Y Z : SynCat modelSig}
    {f f' : X ⟶ Y} {g g' : X ⟶ Z}
    (hf : classOf (X, Y) f = classOf (X, Y) f')
    (hg : classOf (X, Z) g = classOf (X, Z) g') :
    classOf (X, productObj Y Z) (pairArrows f g) = classOf (X, productObj Y Z) (pairArrows f' g') :=
  AbortSequenceProofs.pair_congr pe hf hg

/-- Copairing from the syntax sum respects the repaired branch classes. -/
theorem repairedHomClass_desc_congr {X Y Z : SynCat modelSig}
    {l l' : X ⟶ Z} {r r' : Y ⟶ Z}
    (hl : classOf (X, Z) l = classOf (X, Z) l')
    (hr : classOf (Y, Z) r = classOf (Y, Z) r') :
    classOf (cop X Y, Z) (desc l r) = classOf (cop X Y, Z) (desc l' r') :=
  AbortSequenceProofs.syntaxDesc_congr pe hl hr

/-- Copairing from the chosen categorical coproduct respects the repaired branch classes. -/
theorem repairedHomClass_coprodDesc_congr {X Y Z : SynCat modelSig}
    {l l' : X ⟶ Z} {r r' : Y ⟶ Z}
    (hl : classOf (X, Z) l = classOf (X, Z) l')
    (hr : classOf (Y, Z) r = classOf (Y, Z) r') :
    classOf (X ⨿ Y, Z) (coprod.desc l r) = classOf (X ⨿ Y, Z) (coprod.desc l' r') :=
  AbortSequenceProofs.desc_congr pe hl hr

/-- Iteration with the syntax sum respects the repaired class of the loop body. -/
theorem repairedHomClass_syntaxIterate_congr {X Y : SynCat modelSig}
    {f f' : X ⟶ cop Y X}
    (hf : classOf (X, cop Y X) f = classOf (X, cop Y X) f') :
    classOf (X, Y) (Silmaril.Thesis.LambdaIter.Syn.SynCat.iterate (A := X) (B := Y) f) =
      classOf (X, Y) (Silmaril.Thesis.LambdaIter.Syn.SynCat.iterate (A := X) (B := Y) f') :=
  AbortSequenceProofs.syntaxIterate_congr pe hf

/-- Iteration with the chosen categorical coproduct respects the repaired class of the loop body. -/
theorem repairedHomClass_iterate_congr {X Y : SynCat modelSig}
    {f f' : X ⟶ Y ⨿ X}
    (hf : classOf (X, Y ⨿ X) f = classOf (X, Y ⨿ X) f') :
    classOf (X, Y) (CategoryTheory.iterate (X := X) (Y := Y) f) =
      classOf (X, Y) (CategoryTheory.iterate (X := X) (Y := Y) f') :=
  AbortSequenceProofs.iterate_congr pe hf

/-- Tensoring with a fixed object on the left respects repaired arrow classes. -/
theorem repairedHomClass_tensorLeft_congr {X Y : SynCat modelSig}
    (R : SynCat modelSig) {f f' : X ⟶ Y}
    (hf : classOf (X, Y) f = classOf (X, Y) f') :
    classOf (productObj R X, productObj R Y) (tensorLeft R f) =
      classOf (productObj R X, productObj R Y) (tensorLeft R f') :=
  AbortSequenceProofs.tensorLeft_congr pe R hf

/-- Tensoring with a fixed object on the right respects repaired arrow classes. -/
theorem repairedHomClass_tensorRight_congr {X Y : SynCat modelSig}
    (R : SynCat modelSig) {f f' : X ⟶ Y}
    (hf : classOf (X, Y) f = classOf (X, Y) f') :
    classOf (productObj X R, productObj Y R) (tensorRight R f) =
      classOf (productObj X R, productObj Y R) (tensorRight R f') :=
  AbortSequenceProofs.tensorRight_congr pe R hf

/-- Retaining a fixed context respects the repaired computation class. -/
theorem repairedHomClass_retainLeft_congr {R A B : ValueCat modelSig}
    {f f' : A.obj ⟶ B.obj}
    (hf : classOf (A.obj, B.obj) f = classOf (A.obj, B.obj) f') :
    classOf ((R ⊗ A).obj, (R ⊗ B).obj) (retainLeft (values modelSig) (R := R) f) =
      classOf ((R ⊗ A).obj, (R ⊗ B).obj) (retainLeft (values modelSig) (R := R) f') :=
  AbortSequenceProofs.retainLeft_congr pe hf

/-- In the syntactic model, retaining the input pairs the identity with the computation. -/
theorem extend_values_eq_pairArrows {S : Sig.{u}} {R A : ValueCat S}
    (f : R.obj ⟶ A.obj) : extend (values S) f = pairArrows (𝟙 R.obj) f :=
  AbortSequenceProofs.extend_values_eq_pairArrows_proof f

/-- Evaluating a computation while retaining its input respects the repaired computation class. -/
theorem repairedHomClass_extend_congr {R A : ValueCat modelSig} {f f' : R.obj ⟶ A.obj}
    (hf : classOf (R.obj, A.obj) f = classOf (R.obj, A.obj) f') :
    classOf (R.obj, (R ⊗ A).obj) (extend (values modelSig) f) =
      classOf (R.obj, (R ⊗ A).obj) (extend (values modelSig) f') :=
  AbortSequenceProofs.extend_congr pe hf

/-- Contextual binding respects the repaired classes of the scrutinee and continuation. -/
theorem repairedHomClass_bind_congr {R A B : ValueCat modelSig}
    {f f' : R.obj ⟶ A.obj} {g g' : (R ⊗ A).obj ⟶ B.obj}
    (hf : classOf (R.obj, A.obj) f = classOf (R.obj, A.obj) f')
    (hg : classOf ((R ⊗ A).obj, B.obj) g = classOf ((R ⊗ A).obj, B.obj) g') :
    classOf (R.obj, B.obj) (bindArrow (values modelSig) f g) =
      classOf (R.obj, B.obj) (bindArrow (values modelSig) f' g') :=
  AbortSequenceProofs.bind_congr pe hf hg

/-- Contextual case analysis respects the repaired classes of the scrutinee and both branches. -/
theorem repairedHomClass_caseWithContext_congr {R A B D : ValueCat modelSig}
    {f f' : R.obj ⟶ (A ⨿ B).obj}
    {l l' : (R ⊗ A).obj ⟶ D.obj} {r r' : (R ⊗ B).obj ⟶ D.obj}
    (hf : classOf (R.obj, (A ⨿ B).obj) f = classOf (R.obj, (A ⨿ B).obj) f')
    (hl : classOf ((R ⊗ A).obj, D.obj) l = classOf ((R ⊗ A).obj, D.obj) l')
    (hr : classOf ((R ⊗ B).obj, D.obj) r = classOf ((R ⊗ B).obj, D.obj) r') :
    classOf (R.obj, D.obj) (caseWithContext (values modelSig) f l r) =
      classOf (R.obj, D.obj) (caseWithContext (values modelSig) f' l' r') :=
  AbortSequenceProofs.caseWithContext_congr pe hf hl hr

/-- Contextual iteration respects the repaired class of the loop body. -/
theorem repairedHomClass_contextualLoop_congr {R A B : ValueCat modelSig}
    {f f' : (R ⊗ A).obj ⟶ (B ⨿ A).obj}
    (hf : classOf ((R ⊗ A).obj, (B ⨿ A).obj) f = classOf ((R ⊗ A).obj, (B ⨿ A).obj) f') :
    classOf ((R ⊗ A).obj, B.obj) (contextualLoop (values modelSig) (R := R) f) =
      classOf ((R ⊗ A).obj, B.obj) (contextualLoop (values modelSig) (R := R) f') :=
  AbortSequenceProofs.contextualLoop_congr pe hf

end Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic
