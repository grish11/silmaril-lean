module

public import Silmaril.SSA.Isotope.LetIter.Categorical.Syntactic.AbortSequence.Thms

/-! # Congruence of syntactic operations for the repaired hom relation -/

public section

universe u

namespace Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic.AbortSequenceProofs

open CategoryTheory CategoryTheory.Limits CategoryTheory.PremonoidalCategory
open scoped MonoidalCategory
open Silmaril.Isotope.LetIter.LocallyNameless (AbortEquiv PureTypedSubst Refinement Tm)
open Silmaril.Thesis.LambdaIter.Syn (SynCat ind)
open Silmaril.Thesis.LambdaIter.Syn.SynCat
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical
  (duplicate extend retainLeft contextualLoop caseWithContext)
local notation "bindArrow" => Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind

variable {τ Φ ε : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε]

local notation "ThesisTm" => Thesis.LambdaIter.LocallyNameless.Tm
local notation "toThesisCtx" => Bridge.BoundCtx.toThesis

local instance repairedOperationProofThesisTypeFormers : Thesis.LambdaIter.TypeFormers τ :=
  Bridge.thesisTypeFormers τ
local instance repairedOperationProofThesisHasTy : Thesis.LambdaIter.HasTy Φ τ :=
  Bridge.thesisHasTy Φ τ
local instance repairedOperationProofThesisHasEff : Thesis.LambdaIter.HasEff Φ ε :=
  Bridge.thesisHasEff Φ ε

variable (pe : ε)

local notation "modelSig" => signature (τ := τ) (Φ := Φ) pe
local notation "classOf" "(" P "," Q ")" =>
  repairedHomClass (τ := τ) (Φ := Φ) pe (X := P) (Y := Q)

private theorem repaired_rename {n m : Nat} {β : BoundCtx τ n} {δ : BoundCtx τ m}
    {a b : ThesisTm Empty Φ n} {A : τ} (h : RepairedEqv pe β a b A)
    (ρ : Thesis.LambdaIter.LocallyNameless.TypedRenaming (toThesisCtx β) (toThesisCtx δ)) :
    RepairedEqv pe δ
      (Thesis.LambdaIter.LocallyNameless.Tm.rename ρ.toFun a)
      (Thesis.LambdaIter.LocallyNameless.Tm.rename ρ.toFun b) A := by
  have sub : PureTypedSubst pe (Ctx.nil : Ctx Empty τ) β δ
      (fun i => (Tm.bv (ρ.toFun i) : Tm Empty Φ m)) :=
    ⟨fun i => by
      have slot : δ.get (ρ.toFun i) = β.get i := by
        simpa only [Bridge.BoundCtx.get_toThesis] using ρ.typed i
      rw [← slot]
      exact .bv, fun _ => .bv⟩
  have translate (t : ThesisTm Empty Φ n) :
      Bridge.ofThesis (Thesis.LambdaIter.LocallyNameless.Tm.rename ρ.toFun t) =
        Tm.rename ρ.toFun (Bridge.ofThesis t) := by
    have h := Bridge.toThesis_rename ρ.toFun (Bridge.ofThesis t)
    simpa only [Bridge.toThesis_ofThesis, Bridge.ofThesis_toThesis] using
      (congrArg Bridge.ofThesis h).symm
  simpa only [RepairedEqv, translate, Tm.bsubst_bv_eq_rename] using AbortEquiv.bsubst h sub

private theorem repaired_underBinder {A B X : τ} {a b : ThesisTm Empty Φ 1}
    (h : RepairedEqv pe (.snoc .nil A) a b B) :
    RepairedEqv pe (.snoc (.snoc .nil X) A)
      (Thesis.LambdaIter.LocallyNameless.Tm.underBinder a)
      (Thesis.LambdaIter.LocallyNameless.Tm.underBinder b) B :=
  repaired_rename pe (δ := .snoc (.snoc .nil X) A) h
    (Thesis.LambdaIter.LocallyNameless.TypedRenaming.underBinder .nil X A)

theorem comp_congr {X Y Z : SynCat modelSig}
    {f f' : X ⟶ Y} {g g' : Y ⟶ Z}
    (hf : classOf (X, Y) f = classOf (X, Y) f')
    (hg : classOf (Y, Z) g = classOf (Y, Z) g') :
    classOf (X, Z) (f ≫ g) = classOf (X, Z) (f' ≫ g') := by
  induction f using ind with
  | H a ha =>
    induction f' using ind with
    | H a' ha' =>
      induction g using ind with
      | H b hb =>
        induction g' using ind with
        | H b' hb' =>
          have left : RepairedEqv pe (.snoc .nil X.ty) a a' Y.ty := Quotient.exact hf
          have right : RepairedEqv pe (.snoc .nil Y.ty) b b' Z.ty := Quotient.exact hg
          have combined : RepairedEqv pe (.snoc .nil X.ty)
              (.let₁ a b.underBinder) (.let₁ a' b'.underBinder) Z.ty :=
            Refinement.let₁ left (repaired_underBinder pe right)
          exact Quotient.sound combined

theorem pair_congr {X Y Z : SynCat modelSig}
    {f f' : X ⟶ Y} {g g' : X ⟶ Z}
    (hf : classOf (X, Y) f = classOf (X, Y) f')
    (hg : classOf (X, Z) g = classOf (X, Z) g') :
    classOf (X, productObj Y Z) (pairArrows f g) = classOf (X, productObj Y Z) (pairArrows f' g') := by
  induction f using ind with
  | H a ha =>
    induction f' using ind with
    | H a' ha' =>
      induction g using ind with
      | H b hb =>
        induction g' using ind with
        | H b' hb' =>
          have left : RepairedEqv pe (.snoc .nil X.ty) a a' Y.ty := Quotient.exact hf
          have right : RepairedEqv pe (.snoc .nil X.ty) b b' Z.ty := Quotient.exact hg
          have combined : RepairedEqv pe (.snoc .nil X.ty)
              (.pair a b) (.pair a' b') (product Y.ty Z.ty) :=
            Refinement.pair left right
          exact Quotient.sound combined

theorem syntaxDesc_congr {X Y Z : SynCat modelSig}
    {l l' : X ⟶ Z} {r r' : Y ⟶ Z}
    (hl : classOf (X, Z) l = classOf (X, Z) l')
    (hr : classOf (Y, Z) r = classOf (Y, Z) r') :
    classOf (cop X Y, Z) (desc l r) = classOf (cop X Y, Z) (desc l' r') := by
  induction l using ind with
  | H a ha =>
    induction l' using ind with
    | H a' ha' =>
      induction r using ind with
      | H b hb =>
        induction r' using ind with
        | H b' hb' =>
          have left : RepairedEqv pe (.snoc .nil X.ty) a a' Z.ty := Quotient.exact hl
          have right : RepairedEqv pe (.snoc .nil Y.ty) b b' Z.ty := Quotient.exact hr
          have combined : RepairedEqv pe (.snoc .nil (cop X Y).ty)
              (.case (.bv 0) a.underBinder b.underBinder)
              (.case (.bv 0) a'.underBinder b'.underBinder) Z.ty :=
            Refinement.case (Refinement.refl .bv) (repaired_underBinder pe left)
              (repaired_underBinder pe right)
          exact Quotient.sound combined

theorem desc_congr {X Y Z : SynCat modelSig}
    {l l' : X ⟶ Z} {r r' : Y ⟶ Z}
    (hl : classOf (X, Z) l = classOf (X, Z) l')
    (hr : classOf (Y, Z) r = classOf (Y, Z) r') :
    classOf (X ⨿ Y, Z) (coprod.desc l r) = classOf (X ⨿ Y, Z) (coprod.desc l' r') := by
  simp only [← copIso_inv_desc]
  exact comp_congr pe rfl (syntaxDesc_congr pe hl hr)

theorem syntaxIterate_congr {X Y : SynCat modelSig}
    {f f' : X ⟶ cop Y X}
    (hf : classOf (X, cop Y X) f = classOf (X, cop Y X) f') :
    classOf (X, Y) (Silmaril.Thesis.LambdaIter.Syn.SynCat.iterate (A := X) (B := Y) f) =
      classOf (X, Y) (Silmaril.Thesis.LambdaIter.Syn.SynCat.iterate (A := X) (B := Y) f') := by
  induction f using ind with
  | H a ha =>
    induction f' using ind with
    | H a' ha' =>
      have related : RepairedEqv pe (.snoc .nil X.ty) a a' (cop Y X).ty := Quotient.exact hf
      have combined : RepairedEqv pe (.snoc .nil X.ty)
          (.iter (.bv 0) a.underBinder) (.iter (.bv 0) a'.underBinder) Y.ty :=
        Refinement.iter (Refinement.refl .bv) (repaired_underBinder pe related)
      exact Quotient.sound combined

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem iterate_congr {X Y : SynCat modelSig}
    {f f' : X ⟶ Y ⨿ X}
    (hf : classOf (X, Y ⨿ X) f = classOf (X, Y ⨿ X) f') :
    classOf (X, Y) (CategoryTheory.iterate (X := X) (Y := Y) f) =
      classOf (X, Y) (CategoryTheory.iterate (X := X) (Y := Y) f') := by
  change classOf (X, Y) (iterate' (A := X) (B := Y) f) = classOf (X, Y) (iterate' (A := X) (B := Y) f')
  unfold iterate'
  exact syntaxIterate_congr pe (Y := Y) (comp_congr pe hf rfl)

theorem tensorLeft_congr {X Y : SynCat modelSig}
    (R : SynCat modelSig) {f f' : X ⟶ Y}
    (hf : classOf (X, Y) f = classOf (X, Y) f') :
    classOf (productObj R X, productObj R Y) (tensorLeft R f) =
      classOf (productObj R X, productObj R Y) (tensorLeft R f') := by
  induction f using ind with
  | H a ha =>
    induction f' using ind with
    | H a' ha' =>
      have related : RepairedEqv pe (.snoc .nil X.ty) a a' Y.ty := Quotient.exact hf
      have shifted : RepairedEqv pe (.snoc (.snoc (.snoc .nil (product R.ty X.ty)) R.ty) X.ty)
          (onNewest a) (onNewest a') Y.ty :=
        repaired_rename pe related ⟨fun _ => 0, Fin.cases rfl (fun i => i.elim0)⟩
      have combined : RepairedEqv pe (.snoc .nil (product R.ty X.ty))
          (tensorLeftTm a) (tensorLeftTm a') (product R.ty Y.ty) :=
        Refinement.let₂ (Refinement.refl .bv) (Refinement.let₁ shifted (Refinement.refl (.pair .bv .bv)))
      exact Quotient.sound combined

theorem tensorRight_congr {X Y : SynCat modelSig}
    (R : SynCat modelSig) {f f' : X ⟶ Y}
    (hf : classOf (X, Y) f = classOf (X, Y) f') :
    classOf (productObj X R, productObj Y R) (tensorRight R f) =
      classOf (productObj X R, productObj Y R) (tensorRight R f') := by
  unfold tensorRight
  exact comp_congr pe rfl (comp_congr pe (tensorLeft_congr pe R hf) rfl)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem retainLeft_congr {R A B : ValueCat modelSig}
    {f f' : A.obj ⟶ B.obj}
    (hf : classOf (A.obj, B.obj) f = classOf (A.obj, B.obj) f') :
    classOf ((R ⊗ A).obj, (R ⊗ B).obj) (retainLeft (values modelSig) (R := R) f) =
      classOf ((R ⊗ A).obj, (R ⊗ B).obj) (retainLeft (values modelSig) (R := R) f') := by
  have retained (g : A.obj ⟶ B.obj) :
      retainLeft (values modelSig) (R := R) g = tensorLeft R.obj g := by
    change 𝟙 _ ≫ leftTensor (𝟙 R.obj) g ≫ 𝟙 _ = _
    simp only [Category.id_comp, Category.comp_id, leftTensor, id_whiskerRight]
    rfl
  rw [retained, retained]
  exact tensorLeft_congr pe R.obj hf

theorem extend_congr {R A : ValueCat modelSig} {f f' : R.obj ⟶ A.obj}
    (hf : classOf (R.obj, A.obj) f = classOf (R.obj, A.obj) f') :
    classOf (R.obj, (R ⊗ A).obj) (extend (values modelSig) f) =
      classOf (R.obj, (R ⊗ A).obj) (extend (values modelSig) f') := by
  let J := values modelSig
  change classOf (R.obj, (R ⊗ A).obj) (J.map (duplicate R) ≫ retainLeft J (R := R) f) =
    classOf (R.obj, (R ⊗ A).obj) (J.map (duplicate R) ≫ retainLeft J (R := R) f')
  exact comp_congr pe rfl (retainLeft_congr pe (R := R) hf)

theorem bind_congr {R A B : ValueCat modelSig}
    {f f' : R.obj ⟶ A.obj} {g g' : (R ⊗ A).obj ⟶ B.obj}
    (hf : classOf (R.obj, A.obj) f = classOf (R.obj, A.obj) f')
    (hg : classOf ((R ⊗ A).obj, B.obj) g = classOf ((R ⊗ A).obj, B.obj) g') :
    classOf (R.obj, B.obj) (bindArrow (values modelSig) f g) =
      classOf (R.obj, B.obj) (bindArrow (values modelSig) f' g') :=
  comp_congr pe (extend_congr pe hf) hg

theorem caseWithContext_congr {R A B D : ValueCat modelSig}
    {f f' : R.obj ⟶ (A ⨿ B).obj}
    {l l' : (R ⊗ A).obj ⟶ D.obj} {r r' : (R ⊗ B).obj ⟶ D.obj}
    (hf : classOf (R.obj, (A ⨿ B).obj) f = classOf (R.obj, (A ⨿ B).obj) f')
    (hl : classOf ((R ⊗ A).obj, D.obj) l = classOf ((R ⊗ A).obj, D.obj) l')
    (hr : classOf ((R ⊗ B).obj, D.obj) r = classOf ((R ⊗ B).obj, D.obj) r') :
    classOf (R.obj, D.obj) (caseWithContext (values modelSig) f l r) =
      classOf (R.obj, D.obj) (caseWithContext (values modelSig) f' l' r') := by
  unfold caseWithContext
  apply bind_congr pe (R := R) (A := A ⨿ B) (B := D) hf
  exact comp_congr pe rfl (comp_congr pe rfl (desc_congr pe hl hr))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem contextualLoop_congr {R A B : ValueCat modelSig}
    {f f' : (R ⊗ A).obj ⟶ (B ⨿ A).obj}
    (hf : classOf ((R ⊗ A).obj, (B ⨿ A).obj) f = classOf ((R ⊗ A).obj, (B ⨿ A).obj) f') :
    classOf ((R ⊗ A).obj, B.obj) (contextualLoop (values modelSig) (R := R) f) =
      classOf ((R ⊗ A).obj, B.obj) (contextualLoop (values modelSig) (R := R) f') := by
  unfold contextualLoop
  apply comp_congr pe _ rfl
  apply iterate_congr pe (Y := (R ⊗ B).obj)
  exact comp_congr pe rfl (comp_congr pe (retainLeft_congr pe (R := R) hf) rfl)

end Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic.AbortSequenceProofs
