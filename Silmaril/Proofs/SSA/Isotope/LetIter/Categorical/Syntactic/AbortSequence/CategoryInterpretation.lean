module

public import Silmaril.SSA.Isotope.LetIter.Categorical.Syntactic.AbortSequence.Category.Interpretation.Defs
public import Silmaril.SSA.Isotope.LetIter.Categorical.Syntactic.AbortSequence.Category.Thms
public import Silmaril.SSA.Isotope.LetIter.Categorical.AbortSequence.Thms
public import Silmaril.SSA.Isotope.LetIter.Categorical.LetEta.Thms
public import Silmaril.SSA.Isotope.LetIter.Categorical.Substitution.Thms

/-! # Interpretation of repaired computation arrows -/

public section

universe u u₁ u₂ v₁ v₂

namespace Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic.InterpretationProofs

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open CartesianMonoidalCategory (snd leftUnitor_hom associator_hom_snd_snd whiskerRight_snd)
open Silmaril.Isotope.LetIter.LocallyNameless (Derivation Tm)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (boundLookup extend)
local notation "bindArrow" => Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind
open Silmaril.Thesis.LambdaIter.Syn (Carrier SynCat mk)
open Silmaril.Thesis.LambdaIter.LocallyNameless (HasType)

variable {τ Φ ε : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] (pe : ε)
  {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  [FreydCategory.CentralUnit J] (M : TypeModel τ V) [InstructionModel J M Φ]

local notation "modelSig" => signature (τ := τ) (Φ := Φ) pe
local notation "P" => repairedProjection (τ := τ) (Φ := Φ) pe
local notation "Q" => RepairedSynCat (τ := τ) (Φ := Φ) pe
local notation "Γ₀" => (Ctx.nil : Ctx Empty τ)

local instance : Thesis.LambdaIter.TypeFormers τ := Bridge.thesisTypeFormers τ
local instance : Thesis.LambdaIter.HasTy Φ τ := Bridge.thesisHasTy Φ τ

private theorem nativeTyping {X Y : SynCat modelSig} (a : Carrier modelSig (.snoc .nil X.ty) Y.ty) :
    Nonempty (Derivation Φ Γ₀ (.snoc .nil X.ty) (Bridge.ofThesis a.1) Y.ty) := by
  apply Derivation.ofHasType
  apply (Bridge.hasType_iff (Bridge.TypeCompat.canonical τ) (Bridge.InstrCompat.canonical Φ τ)).mpr
  simpa only [Bridge.Ctx.toThesis, Bridge.BoundCtx.toThesis, Bridge.toThesis_ofThesis] using a.2

variable
  (coherent : TypingCoherent (ν := Empty) J M Φ)
  (shared : ∀ R T : V, ∃ e : J.obj R ⊗ J.obj T = J.obj (R ⊗ T),
    Functor.StrongPremonoidal.tensorIso (J := J) R T = eqToIso e)
  (pureInstr : ∀ f : Φ, IsPure pe f → ∃ p : M.obj (instrSrc f) ⟶ M.obj (instrTrg f),
    InstructionModel.denote (J := J) (M := M) f = J.map p)

private noncomputable def denoteClass {X Y : SynCat modelSig} :
    Quotient (repairedHomSetoid pe X Y) → (J.obj (M.obj X.ty) ⟶ J.obj (M.obj Y.ty)) :=
  Quotient.lift
    (fun a => J.map (singletonEnvIso M X.ty).inv ≫ denote J M (nativeTyping pe a).some)
    (fun _ _ h => congrArg (J.map (singletonEnvIso M X.ty).inv ≫ ·)
      (denote_abortEquiv_of_coherent_shared_tensor J M coherent shared pureInstr h _ _))

noncomputable def repairedArrowDenote {X Y : Q} (f : X ⟶ Y) :
    J.obj (M.obj X.as.ty) ⟶ J.obj (M.obj Y.as.ty) :=
  Quot.liftOn f (fun g => denoteClass pe J M coherent shared pureInstr (repairedHomClass pe g))
    (fun g h e => congrArg (denoteClass pe J M coherent shared pureInstr)
      ((HomRel.compClosure_iff_self (repairedHomRel pe) g h).mp e))

theorem repairedArrowDenote_mk {X Y : SynCat modelSig}
    {t : Thesis.LambdaIter.LocallyNameless.Tm Empty Φ 1}
    (h : Thesis.LambdaIter.LocallyNameless.HasType Φ .nil (.snoc .nil X.ty) t Y.ty)
    (d : Derivation Φ Γ₀ (.snoc .nil X.ty) (Bridge.ofThesis t) Y.ty) :
    repairedArrowDenote pe J M coherent shared pureInstr
        ((P).map (mk (S := modelSig) h : X ⟶ Y)) =
      J.map (singletonEnvIso M X.ty).inv ≫ denote J M d := by
  change J.map (singletonEnvIso M X.ty).inv ≫ denote J M _ = _
  rw [coherent _ d]

omit [SymmetricCategory V] [DistributiveTensor V] in
private theorem singletonEnvIso_hom_eq_boundVar (A : τ) :
    (singletonEnvIso M A).hom = boundVar M (Γ := Γ₀) (β := .snoc .nil A) 0 := by
  change (λ_ ((𝟙_ V) ⊗ M.obj A)).hom ≫ (λ_ (M.obj A)).hom =
    snd (𝟙_ V) ((𝟙_ V) ⊗ M.obj A) ≫ snd (𝟙_ V) (M.obj A)
  simp only [leftUnitor_hom]

local notation "evalArrow" => repairedArrowDenote pe J M coherent shared pureInstr

theorem repairedArrowDenote_id (X : Q) :
    evalArrow (𝟙 X) = 𝟙 (J.obj (M.obj X.as.ty)) := by
  rcases X with ⟨X⟩
  change evalArrow (𝟙 ((P).obj X)) = 𝟙 (J.obj (M.obj X.ty))
  rw [← (P).map_id X]
  have h := repairedArrowDenote_mk pe J M coherent shared pureInstr (X := X) (Y := X)
    HasType.newest (.bv (ι := 0))
  change evalArrow ((P).map (𝟙 X)) = _ at h
  rw [h]
  change J.map (singletonEnvIso M X.ty).inv ≫
    J.map (boundVar M (Γ := Γ₀) (β := .snoc .nil X.ty) 0) = _
  rw [← singletonEnvIso_hom_eq_boundVar]
  change J.map (singletonEnvIso M X.ty).inv ≫ J.map (singletonEnvIso M X.ty).hom = _
  rw [← J.map_comp, Iso.inv_hom_id, J.map_id]

private theorem ofThesis_underBinder {n : Nat}
    (b : Thesis.LambdaIter.LocallyNameless.Tm Empty Φ (n + 1)) :
    Bridge.ofThesis b.underBinder = (Bridge.ofThesis b).underBinder := by
  unfold Thesis.LambdaIter.LocallyNameless.Tm.underBinder Tm.underBinder
  rw [← Bridge.ofThesis_toThesis (Tm.rename _ (Bridge.ofThesis b)), Bridge.toThesis_rename,
    Bridge.toThesis_ofThesis]

private theorem denote_singleton_comp {a b : Tm Empty Φ 1} {A B D : τ}
    (da : Derivation Φ Γ₀ (.snoc .nil A) a B)
    (db : Derivation Φ Γ₀ (.snoc .nil B) b D) :
    denote J M (.let₁ da (db.rename (BoundCtx.Renaming.underBinder .nil A B))) =
      denote J M da ≫ J.map (singletonEnvIso M B).inv ≫ denote J M db := by
  let E := envObj M Γ₀ (.snoc .nil A)
  have projectNewest :
      (envSnocIso M Γ₀ (.snoc .nil A) B).hom ≫
        boundVar M (Γ := Γ₀) (β := .snoc (.snoc .nil A) B) 0 = snd E (M.obj B) :=
    associator_hom_snd_snd (ctxObj M Γ₀) (boundObj M (.snoc .nil A)) (M.obj B)
  have letEta := denote_let_eta_of_centralUnit J M da
  change bindArrow J (denote J M da) (J.map (envSnocIso M Γ₀ (.snoc .nil A) B).hom ≫
    J.map (boundVar M (Γ := Γ₀) (β := .snoc (.snoc .nil A) B) 0)) = _ at letEta
  rw [← J.map_comp, projectNewest] at letEta
  have projectSlot :
      (dropSlot M (Γ := Γ₀) .nil A ▷ M.obj B) ≫ (envSnocIso M Γ₀ .nil B).hom =
        snd E (M.obj B) ≫ (singletonEnvIso M B).inv := by
    apply (cancel_mono (singletonEnvIso M B).hom).mp
    have newest : (envSnocIso M Γ₀ .nil B).hom ≫ (singletonEnvIso M B).hom =
        snd (envObj M Γ₀ .nil) (M.obj B) := by
      have unitProjection := congrArg
        (fun p : envObj M Γ₀ (.snoc .nil B) ⟶ M.obj B => (envSnocIso M Γ₀ .nil B).hom ≫ p)
        (singletonEnvIso_hom_eq_boundVar M B)
      exact unitProjection.trans
        (associator_hom_snd_snd (ctxObj M Γ₀) (boundObj M .nil) (M.obj B))
    simp only [Category.assoc, newest, Iso.inv_hom_id, Category.comp_id, whiskerRight_snd, E]
  change bindArrow J (denote J M da) (J.map (envSnocIso M Γ₀ (.snoc .nil A) B).hom ≫
    denote J M (db.rename (BoundCtx.Renaming.underBinder .nil A B))) = _
  rw [denote_underBinder J M db, ← J.map_comp_assoc, projectSlot, J.map_comp]
  let retained := extend J (denote J M da)
  change retained ≫ J.map (snd E (M.obj B)) = denote J M da at letEta
  change retained ≫ (J.map (snd E (M.obj B)) ≫ J.map (singletonEnvIso M B).inv) ≫
    denote J M db = _
  simp only [Category.assoc]
  rw [← Category.assoc retained, letEta]

include coherent shared pureInstr in
theorem repairedArrowDenote_mk_of {X Y : SynCat modelSig}
    {t : Thesis.LambdaIter.LocallyNameless.Tm Empty Φ 1}
    (h : HasType Φ .nil (.snoc .nil X.ty) t Y.ty)
    {s : Tm Empty Φ 1} (d : Derivation Φ Γ₀ (.snoc .nil X.ty) s Y.ty)
    (hs : s = Bridge.ofThesis t) :
    evalArrow ((P).map (mk (S := modelSig) h : X ⟶ Y)) =
      J.map (singletonEnvIso M X.ty).inv ≫ denote J M d := by
  subst s
  exact repairedArrowDenote_mk pe J M coherent shared pureInstr h d

theorem repairedArrowDenote_comp {X Y Z : Q} (f : X ⟶ Y) (g : Y ⟶ Z) :
    evalArrow (f ≫ g) = evalArrow f ≫ evalArrow g := by
  rcases X with ⟨X⟩
  rcases Y with ⟨Y⟩
  rcases Z with ⟨Z⟩
  obtain ⟨f, rfl⟩ := (P).map_surjective f
  obtain ⟨g, rfl⟩ := (P).map_surjective g
  rw [← (P).map_comp]
  induction f using Silmaril.Thesis.LambdaIter.Syn.ind with
  | H a ha =>
    induction g using Silmaril.Thesis.LambdaIter.Syn.ind with
    | H b hb =>
      obtain ⟨da⟩ := nativeTyping pe (X := X) (Y := Y) ⟨a, ⟨ha⟩⟩
      obtain ⟨db⟩ := nativeTyping pe (X := Y) (Y := Z) ⟨b, ⟨hb⟩⟩
      change evalArrow ((P).map (mk (S := modelSig) (HasType.let₁ ha hb.underBinder) : X ⟶ Z)) =
        evalArrow ((P).map (mk (S := modelSig) ha : X ⟶ Y)) ≫
          evalArrow ((P).map (mk (S := modelSig) hb : Y ⟶ Z))
      rw [repairedArrowDenote_mk pe J M coherent shared pureInstr ha da,
        repairedArrowDenote_mk pe J M coherent shared pureInstr hb db]
      have comp := repairedArrowDenote_mk_of pe J M coherent shared pureInstr (X := X) (Y := Z)
        (HasType.let₁ ha hb.underBinder) (.let₁ da (db.rename (BoundCtx.Renaming.underBinder .nil X.ty Y.ty)))
        (by change Tm.let₁ (Bridge.ofThesis a) (Bridge.ofThesis b).underBinder =
            Tm.let₁ (Bridge.ofThesis a) (Bridge.ofThesis b.underBinder)
            rw [ofThesis_underBinder])
      rw [comp, denote_singleton_comp, Category.assoc]

end Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic.InterpretationProofs
