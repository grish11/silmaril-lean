module

public import Silmaril.SSA.Isotope.LetIter.Categorical.Syntactic.AbortSequence.Category.Interpretation.Coproducts.Thms
public import Silmaril.SSA.Isotope.LetIter.Categorical.Syntactic.AbortSequence.Category.Iteration.Thms
public import Silmaril.SSA.Isotope.LetIter.Categorical.Context.Iteration.Thms
public import Silmaril.SSA.Isotope.LetIter.Categorical.Sequencing.Thms

/-! # Interpretation of the chosen LetIter iteration -/

public section

universe u u₁ u₂ v₁ v₂

namespace Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic.InterpretationIterationProofs

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open CartesianMonoidalCategory (snd leftUnitor_hom associator_hom_snd_snd)
open Silmaril.Isotope.LetIter.LocallyNameless (Derivation Tm)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (contextualLoop splitMapCoprod)
open Silmaril.Thesis.LambdaIter.Syn (SynCat mk)
open Silmaril.Thesis.LambdaIter.Syn.SynCat (cop copIso)
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
local notation "Γ₀" => (Ctx.nil : Ctx Empty τ)
local notation "P" => repairedProjection (τ := τ) (Φ := Φ) pe
local notation "Q" => RepairedSynCat (τ := τ) (Φ := Φ) pe

variable
  (coherent : TypingCoherent (ν := Empty) J M Φ)
  (shared : ∀ R T : V, ∃ e : J.obj R ⊗ J.obj T = J.obj (R ⊗ T),
    Functor.StrongPremonoidal.tensorIso (J := J) R T = eqToIso e)
  (pureInstr : ∀ f : Φ, IsPure pe f → ∃ p : M.obj (instrSrc f) ⟶ M.obj (instrTrg f),
    InstructionModel.denote (J := J) (M := M) f = J.map p)

local notation "F" => repairedComputationFunctor pe J M coherent shared pureInstr

local instance : Thesis.LambdaIter.TypeFormers τ := Bridge.thesisTypeFormers τ
local instance : Thesis.LambdaIter.HasTy Φ τ := Bridge.thesisHasTy Φ τ

include shared in
private theorem denote_singleton_iterate {a : Tm Empty Φ 1} {A B : τ}
    (d : Derivation Φ Γ₀ (.snoc .nil A) a (coprod B A)) :
    J.map (singletonEnvIso M A).inv ≫
      denote J M (.iter (.bv (ι := 0)) (d.rename (BoundCtx.Renaming.underBinder .nil A A))) =
      CategoryTheory.iterate (J.map (singletonEnvIso M A).inv ≫ denote J M d ≫
        J.map (M.coprodIso B A).hom ≫ splitMapCoprod J (M.obj B) (M.obj A)) := by
  let E := envObj M Γ₀ .nil
  let σ := envSnocIso M Γ₀ .nil A
  let κ := singletonEnvIso M A
  let f := J.map κ.inv ≫ denote J M d ≫ J.map (M.coprodIso B A).hom
  have entry : σ.hom ≫ κ.hom = snd E (M.obj A) := by
    change (α_ (𝟙_ V) (𝟙_ V) (M.obj A)).hom ≫
      ((λ_ ((𝟙_ V) ⊗ M.obj A)).hom ≫ (λ_ (M.obj A)).hom) =
        snd ((𝟙_ V) ⊗ (𝟙_ V)) (M.obj A)
    rw [leftUnitor_hom, leftUnitor_hom, associator_hom_snd_snd]
  have enterBody : J.map σ.hom ≫ denote J M d ≫ J.map (M.coprodIso B A).hom =
      J.map (snd E (M.obj A)) ≫ f := by
    rw [← entry, J.map_comp, Category.assoc]
    simp only [f, ← J.map_comp_assoc, Iso.hom_inv_id, J.map_id, Category.id_comp]
  have loop := denote_iter_newest J M d
  change J.map σ.hom ≫ _ =
    contextualLoop J (J.map σ.hom ≫ denote J M d ≫ J.map (M.coprodIso B A).hom) at loop
  rw [enterBody, contextualLoop_discard J (shared E (M.obj A)) f, ← entry, J.map_comp_assoc] at loop
  rw [(cancel_epi (J.map σ.hom)).mp loop, ← J.map_comp_assoc, Iso.inv_hom_id, J.map_id,
    Category.id_comp]
  simp only [f, κ, Category.assoc]

include coherent shared pureInstr in
private theorem mapSyntaxIterate {X Y : SynCat modelSig} (g : X ⟶ cop Y X) :
    (F).map ((P).map (Silmaril.Thesis.LambdaIter.Syn.SynCat.iterate g)) =
      CategoryTheory.iterate ((F).map ((P).map g) ≫ J.map (M.coprodIso Y.ty X.ty).hom ≫
        splitMapCoprod J (M.obj Y.ty) (M.obj X.ty)) := by
  induction g using Silmaril.Thesis.LambdaIter.Syn.ind with
  | H a ha =>
    have typed : Silmaril.Isotope.LetIter.LocallyNameless.HasType Φ Γ₀
        (.snoc .nil X.ty) (Bridge.ofThesis a) (coprod Y.ty X.ty) := by
      apply (Bridge.hasType_iff (Bridge.TypeCompat.canonical τ) (Bridge.InstrCompat.canonical Φ τ)).mpr
      exact ⟨(Bridge.toThesis_ofThesis a).symm ▸ ha⟩
    obtain ⟨d⟩ := Derivation.ofHasType typed
    have body := repairedArrowDenote_mk pe J M coherent shared pureInstr (X := X) (Y := cop Y X) ha d
    change (F).map ((P).map (mk (S := modelSig) ha : X ⟶ cop Y X)) = _ at body
    have underBinder : Bridge.ofThesis a.underBinder = (Bridge.ofThesis a).underBinder := by
      unfold Silmaril.Thesis.LambdaIter.LocallyNameless.Tm.underBinder Tm.underBinder
      rw [← Bridge.ofThesis_toThesis (Tm.rename _ (Bridge.ofThesis a)), Bridge.toThesis_rename,
        Bridge.toThesis_ofThesis]
    have h := repairedArrowDenote_mk_of pe J M coherent shared pureInstr (X := X) (Y := Y)
      (HasType.iter HasType.newest ha.underBinder)
      (.iter (.bv (ι := 0)) (d.rename (BoundCtx.Renaming.underBinder .nil X.ty X.ty)))
      (by change Tm.iter (.bv 0) (Bridge.ofThesis a).underBinder =
            Tm.iter (.bv 0) (Bridge.ofThesis a.underBinder)
          rw [underBinder])
    change (F).map ((P).map (Silmaril.Thesis.LambdaIter.Syn.SynCat.iterate (mk (S := modelSig) ha))) = _ at h
    rw [h, body]
    have assoc := Category.assoc (J.map (singletonEnvIso M X.ty).inv) (denote J M d)
      (J.map (M.coprodIso Y.ty X.ty).hom ≫ splitMapCoprod J (M.obj Y.ty) (M.obj X.ty))
    exact (denote_singleton_iterate J M shared d).trans
      (congrArg (fun f => CategoryTheory.iterate f) assoc.symm)

theorem repairedComputationFunctor_map_iterate {X Y : Q} (f : X ⟶ Y ⨿ X) :
    (F).map (CategoryTheory.iterate f) =
      CategoryTheory.iterate ((F).map f ≫
        (repairedComputationCoprodIso pe J M coherent shared pureInstr Y X).hom) := by
  rcases X with ⟨X⟩
  rcases Y with ⟨Y⟩
  let κ := repairedSyntaxCoprodIso pe ((P).obj Y) ((P).obj X)
  obtain ⟨g, hg⟩ := (P).map_surjective (f ≫ κ.inv)
  have repr : (P).map g ≫ κ.hom = f := by
    rw [hg, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  let exactBody := g ≫ (copIso Y X).hom
  have source : (P).map exactBody ≫ (repairedProjectionCoprodIso pe Y X).hom = f := by
    rw [← repr]
    change (P).map (g ≫ (copIso Y X).hom) ≫ (repairedProjectionCoprodIso pe Y X).hom =
      (P).map g ≫ (P).map (copIso Y X).hom ≫ (repairedProjectionCoprodIso pe Y X).hom
    rw [(P).map_comp, Category.assoc]
  have loop : CategoryTheory.iterate f =
      (P).map (Silmaril.Thesis.LambdaIter.Syn.SynCat.iterate g) := by
    rw [← source, repairedIteration_map]
    change (P).map (Silmaril.Thesis.LambdaIter.Syn.SynCat.iterate
      (exactBody ≫ (copIso Y X).inv)) = _
    rw [show exactBody ≫ (copIso Y X).inv = g by
      simp only [exactBody, Category.assoc, Iso.hom_inv_id, Category.comp_id]]
  rw [loop, mapSyntaxIterate]
  congr 1
  change _ = (F).map f ≫ (F).map κ.inv ≫ J.map (M.coprodIso Y.ty X.ty).hom ≫
    splitMapCoprod J (M.obj Y.ty) (M.obj X.ty)
  rw [← (F).map_comp_assoc, ← repr, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rfl

end Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic.InterpretationIterationProofs
