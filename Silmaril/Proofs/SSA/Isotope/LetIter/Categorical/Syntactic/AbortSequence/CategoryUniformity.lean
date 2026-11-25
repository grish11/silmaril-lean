module

public import Silmaril.SSA.Isotope.LetIter.Categorical.Syntactic.AbortSequence.Category.Thms
import Silmaril.SSA.Isotope.LetIter.AbortSequence.Normalization.Thms

/-! # Pure uniformity on projected exact representatives -/

public section

open CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope.LetIter.LocallyNameless.AbortNormalization
open Silmaril.Thesis.LambdaIter.Syn (SynCat Carrier mk)
open Silmaril.Thesis.LambdaIter.Syn.SynCat

universe u

namespace Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic.UniformityProofs

variable {τ Φ ε : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε]
local instance auditThesisTypeFormers : Thesis.LambdaIter.TypeFormers τ := Bridge.thesisTypeFormers τ
local instance auditThesisHasTy : Thesis.LambdaIter.HasTy Φ τ := Bridge.thesisHasTy Φ τ
local instance auditThesisHasEff : Thesis.LambdaIter.HasEff Φ ε := Bridge.thesisHasEff Φ ε

variable (pe : ε)
local notation "modelSig" => signature (τ := τ) (Φ := Φ) pe
local notation "TTm" => Thesis.LambdaIter.LocallyNameless.Tm
local notation "Typing" => Thesis.LambdaIter.LocallyNameless.HasType
local notation "ExactEqv" => Thesis.LambdaIter.LocallyNameless.Eqv
local notation "classOf" => repairedHomClass (τ := τ) (Φ := Φ) pe

private def sequenceThesis {n : Nat} (t : TTm Empty Φ n) : TTm Empty Φ n :=
  Bridge.toThesis (sequenceAborts (Bridge.ofThesis t))

private theorem sequenceThesis_rename {n m : Nat} (ρ : Fin n → Fin m) (t : TTm Empty Φ n) :
    sequenceThesis (Thesis.LambdaIter.LocallyNameless.Tm.rename ρ t) =
      Thesis.LambdaIter.LocallyNameless.Tm.rename ρ (sequenceThesis t) := by
  have translate : Bridge.ofThesis (Thesis.LambdaIter.LocallyNameless.Tm.rename ρ t) =
      LetIter.LocallyNameless.Tm.rename ρ (Bridge.ofThesis t) := by
    have h := Bridge.toThesis_rename ρ (Bridge.ofThesis t)
    simpa only [Bridge.toThesis_ofThesis, Bridge.ofThesis_toThesis] using
      (congrArg Bridge.ofThesis h).symm
  unfold sequenceThesis
  rw [translate, sequenceAborts_rename, Bridge.toThesis_rename]

private theorem sequenceThesis_underBinder {n : Nat} (t : TTm Empty Φ (n + 1)) :
    sequenceThesis t.underBinder = (sequenceThesis t).underBinder :=
  sequenceThesis_rename _ _

private theorem nativeTyping {n : Nat} {β : BoundCtx τ n} {t : TTm Empty Φ n} {A : τ}
    (ht : Typing Φ .nil (Bridge.BoundCtx.toThesis β) t A) :
    LetIter.LocallyNameless.HasType Φ (Ctx.nil : Ctx Empty τ) β (Bridge.ofThesis t) A := by
  apply (Bridge.hasType_iff (Bridge.TypeCompat.canonical τ) (Bridge.InstrCompat.canonical Φ τ)).mpr
  simpa only [Bridge.Ctx.toThesis, Bridge.toThesis_ofThesis] using Nonempty.intro ht

private theorem sequenceThesis_typing {n : Nat} {β : BoundCtx τ n} {t : TTm Empty Φ n} {A : τ}
    (ht : Typing Φ .nil (Bridge.BoundCtx.toThesis β) t A) :
    Nonempty (Typing Φ .nil (Bridge.BoundCtx.toThesis β) (sequenceThesis t) A) :=
  (Bridge.hasType_iff (Bridge.TypeCompat.canonical τ) (Bridge.InstrCompat.canonical Φ τ)).mp
    (sequenceAborts_typing (nativeTyping ht))

private theorem sequenceThesis_exact {X A : τ}
    {a b : TTm Empty Φ 1} (h : ExactEqv pe .nil (.snoc .nil X) a b A) :
    ExactEqv pe .nil (.snoc .nil X) (sequenceThesis a) (sequenceThesis b) A := by
  have hex := (Bridge.eqv_iff (Bridge.TypeCompat.canonical τ) (Bridge.InstrCompat.canonical Φ τ)
    (Bridge.EffCompat.canonical Φ ε) pe).mp h
  have hn := (Bridge.equiv_iff (Bridge.TypeCompat.canonical τ) (Bridge.InstrCompat.canonical Φ τ)
    (Bridge.EffCompat.canonical Φ ε) pe).mp (sequenceAborts_exact hex)
  exact hn

private def sequenceCarrier {X Y : SynCat modelSig}
    (a : Carrier modelSig (.snoc .nil X.ty) Y.ty) :
    Carrier modelSig (.snoc .nil X.ty) Y.ty :=
  ⟨sequenceThesis a.1, a.2.elim fun h => sequenceThesis_typing (β := .snoc .nil X.ty) h⟩

private def sequenceHom {X Y : SynCat modelSig} (f : X ⟶ Y) : X ⟶ Y :=
  Quotient.map (sequenceCarrier pe (X := X) (Y := Y)) (fun _ _ h => sequenceThesis_exact pe h) f

private noncomputable def sequenceTyping {X Y : SynCat modelSig} {a : TTm Empty Φ 1}
    (h : Typing Φ .nil (.snoc .nil X.ty) a Y.ty) :
    Typing Φ .nil (.snoc .nil X.ty) (sequenceThesis a) Y.ty :=
  Classical.choice (sequenceThesis_typing (β := .snoc .nil X.ty) h)

private theorem sequenceHom_mk {X Y : SynCat modelSig} {a : TTm Empty Φ 1}
    (h : Typing Φ .nil (.snoc .nil X.ty) a Y.ty) :
    sequenceHom pe (X := X) (Y := Y) (mk h) = mk (sequenceTyping pe (X := X) (Y := Y) h) := rfl

private theorem sequenceHom_of_class_eq {X Y : SynCat modelSig} {f g : X ⟶ Y}
    (h : classOf f = classOf g) : sequenceHom pe f = sequenceHom pe g := by
  induction f using Silmaril.Thesis.LambdaIter.Syn.ind with
  | H a ha =>
    induction g using Silmaril.Thesis.LambdaIter.Syn.ind with
    | H b hb =>
      have hr := (repairedHomClass_mk_eq_iff pe (X := X) (Y := Y) ha hb).mp h
      apply Quotient.sound
      exact (Bridge.equiv_iff (Bridge.TypeCompat.canonical τ) (Bridge.InstrCompat.canonical Φ τ)
        (Bridge.EffCompat.canonical Φ ε) pe).mp (sequenceAborts_repaired hr)

private theorem sequenceHom_class_eq {X Y : SynCat modelSig} (f : X ⟶ Y) :
    classOf (sequenceHom pe f) = classOf f := by
  induction f using Silmaril.Thesis.LambdaIter.Syn.ind with
  | H a ha =>
    rw [sequenceHom_mk]
    apply (repairedHomClass_mk_eq_iff pe (X := X) (Y := Y) (sequenceTyping pe (X := X) (Y := Y) ha) ha).mpr
    unfold RepairedEqv sequenceThesis
    rw [Bridge.ofThesis_toThesis]
    exact (repaired_sequenceAborts (pe := pe) (nativeTyping (β := .snoc .nil X.ty) ha)).symm

private theorem mk_eq_of_term_eq {X Y : SynCat modelSig} {a b : TTm Empty Φ 1}
    (h : a = b) (ha : Typing Φ .nil (.snoc .nil X.ty) a Y.ty)
    (hb : Typing Φ .nil (.snoc .nil X.ty) b Y.ty) :
    (mk (S := modelSig) ha : X ⟶ Y) = mk (S := modelSig) hb := by
  subst b
  rfl

private theorem sequenceHom_comp {X Y Z : SynCat modelSig} (f : X ⟶ Y) (g : Y ⟶ Z) :
    sequenceHom pe (f ≫ g) = sequenceHom pe f ≫ sequenceHom pe g := by
  induction f using Silmaril.Thesis.LambdaIter.Syn.ind with
  | H a ha =>
    induction g using Silmaril.Thesis.LambdaIter.Syn.ind with
    | H b hb =>
      change sequenceHom pe (X := X) (Y := Z) (mk (Thesis.LambdaIter.LocallyNameless.HasType.let₁ ha hb.underBinder)) = _
      simp only [sequenceHom_mk]
      change mk (sequenceTyping pe (X := X) (Y := Z) (Thesis.LambdaIter.LocallyNameless.HasType.let₁ ha hb.underBinder)) =
        mk (Thesis.LambdaIter.LocallyNameless.HasType.let₁ (sequenceTyping pe (X := X) (Y := Y) ha)
          (sequenceTyping pe (X := Y) (Y := Z) hb).underBinder)
      apply mk_eq_of_term_eq pe
      exact congrArg (Thesis.LambdaIter.LocallyNameless.Tm.let₁ (sequenceThesis a))
        (sequenceThesis_underBinder b)

private theorem sequenceHom_desc {X Y Z : SynCat modelSig} (f : X ⟶ Z) (g : Y ⟶ Z) :
    sequenceHom pe (desc f g) = desc (sequenceHom pe f) (sequenceHom pe g) := by
  induction f using Silmaril.Thesis.LambdaIter.Syn.ind with
  | H a ha =>
    induction g using Silmaril.Thesis.LambdaIter.Syn.ind with
    | H b hb =>
      simp only [desc_mk, sequenceHom_mk]
      apply mk_eq_of_term_eq pe
      exact congrArg₂ (Thesis.LambdaIter.LocallyNameless.Tm.case (.bv 0)) (sequenceThesis_underBinder a) (sequenceThesis_underBinder b)

private theorem sequenceHom_iterate {X Y : SynCat modelSig} (f : X ⟶ cop Y X) :
    sequenceHom pe (Silmaril.Thesis.LambdaIter.Syn.SynCat.iterate f) =
      Silmaril.Thesis.LambdaIter.Syn.SynCat.iterate (sequenceHom pe f) := by
  induction f using Silmaril.Thesis.LambdaIter.Syn.ind with
  | H a ha =>
    simp only [iterate_mk, sequenceHom_mk]
    apply mk_eq_of_term_eq pe
    exact congrArg (Thesis.LambdaIter.LocallyNameless.Tm.iter (.bv 0)) (sequenceThesis_underBinder a)

private theorem sequenceHom_pure {X Y : SynCat modelSig} {k : X ⟶ Y} (hk : IsPureMor k) :
    IsPureMor (sequenceHom pe k) := by
  obtain ⟨t, ht, hp, rfl⟩ := hk
  have h := Bridge.pure_iff (Bridge.EffCompat.canonical Φ ε) pe (t := Bridge.ofThesis t)
  have pn := sequenceAborts_pure (h.mpr (by simpa only [Bridge.toThesis_ofThesis] using hp))
  exact ⟨sequenceThesis t, sequenceTyping pe (X := X) (Y := Y) ht,
    (Bridge.pure_iff (Bridge.EffCompat.canonical Φ ε) pe).mp pn, (sequenceHom_mk pe ht).symm⟩

private theorem concrete_uniformity {X D B : SynCat modelSig}
    (f : X ⟶ cop B X) (g : D ⟶ cop B D) (k : X ⟶ D) (hk : IsPureMor k)
    (comm : classOf (f ≫ desc (injl B D) (k ≫ injr B D)) = classOf (k ≫ g)) :
    classOf (Silmaril.Thesis.LambdaIter.Syn.SynCat.iterate f) =
      classOf (k ≫ Silmaril.Thesis.LambdaIter.Syn.SynCat.iterate g) := by
  have square := sequenceHom_of_class_eq pe comm
  simp only [sequenceHom_comp, sequenceHom_desc] at square
  change sequenceHom pe f ≫ desc (injl B D) (sequenceHom pe k ≫ injr B D) =
    sequenceHom pe k ≫ sequenceHom pe g at square
  have uniform := Silmaril.Thesis.LambdaIter.Syn.SynCat.iterate_uniformity (sequenceHom pe f)
    (sequenceHom pe g) (sequenceHom pe k) (sequenceHom_pure pe hk) square
  rw [← sequenceHom_iterate, ← sequenceHom_iterate, ← sequenceHom_comp] at uniform
  exact (sequenceHom_class_eq pe _).symm.trans
    ((congrArg classOf uniform).trans (sequenceHom_class_eq pe _))

private theorem chosen_coprod_transport {X D B : SynCat modelSig} (k : X ⟶ D) :
    coprod.map (𝟙 B) k ≫ (copIso B D).inv =
      (copIso B X).inv ≫ desc (injl B D) (k ≫ injr B D) := by
  rw [copIso_inv_desc]
  apply coprod.hom_ext <;> simp

/-- The exact strong Elgot Freyd operations satisfy pure uniformity modulo
the abort-extended hom relation. -/
theorem repairedProjection_pure_uniformity {X D : ValueCat modelSig} {B : SynCat modelSig}
    (f : (values modelSig).obj X ⟶ B ⨿ (values modelSig).obj X)
    (g : (values modelSig).obj D ⟶ B ⨿ (values modelSig).obj D)
    (h : X ⟶ D)
    (comm : (repairedProjection pe).map (f ≫ coprod.map (𝟙 B) ((values modelSig).map h)) =
      (repairedProjection pe).map (((values modelSig).map h) ≫ g)) :
    (repairedProjection pe).map (CategoryTheory.iterate f) =
      (repairedProjection pe).map (((values modelSig).map h) ≫ CategoryTheory.iterate g) := by
  let k := (values modelSig).map h
  let T := (values modelSig).obj X
  let U := (values modelSig).obj D
  have square := (repairedProjection_map_eq_iff pe _ _).mp comm
  change classOf (f ≫ coprod.map (𝟙 B) k) = classOf (k ≫ g) at square
  have side := repairedHomClass_comp_congr pe square
    (g := (copIso B U).inv) (g' := (copIso B U).inv) rfl
  have sq : classOf ((f ≫ (copIso B T).inv) ≫ desc (injl B U) (k ≫ injr B U)) =
      classOf (k ≫ (g ≫ (copIso B U).inv)) := by
    simp only [Category.assoc] at side ⊢
    rw [chosen_coprod_transport pe k] at side
    simpa only [Category.assoc] using side
  exact (repairedProjection_map_eq_iff pe _ _).mpr
    (concrete_uniformity pe (f ≫ (copIso B T).inv) (g ≫ (copIso B U).inv) k h.property sq)

end Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic.UniformityProofs
