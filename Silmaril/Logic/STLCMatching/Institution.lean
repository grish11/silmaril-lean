module

public import Silmaril.Logic.STLCMatching.Sentences
public import Silmaril.Logic.Institution.Borrowing

@[expose] public section
noncomputable section
namespace Silmaril.Logic.STLCMatching
open CategoryTheory Silmaril.Logic.Institution
open Silmaril.Calculi.TypedLambda Silmaril.Calculi.LambdaCube
open Cslib.LambdaCalculus.LocallyNameless.Stlc
variable {B : Type} {S T U : FixedSignature B}

theorem Model.ext {S : Signature} {M N : Model S} (h : M.toSetModel = N.toSetModel) : M = N := by
  cases M
  cases N
  cases h
  rfl

namespace FixedHom

theorem pull_id (M : Model S.source) : pull (𝟙 S) M = M := by
  apply Model.ext
  cases M with
  | mk M hM => cases M; rfl

theorem pull_comp (f : S ⟶ T) (g : T ⟶ U) (M : Model U.source) :
    pull (f ≫ g) M = pull f (pull g M) := rfl

def pullFunctor (f : S ⟶ T) : Model T.source ⥤ Model S.source where
  obj := pull f
  map h := ⟨congrArg (pull f) h.down⟩

private theorem arrow_hext {M M' N N' : Model S.source} (hM : M = M') (hN : N = N')
    (f : M ⟶ N) (g : M' ⟶ N') : HEq f g := by
  cases hM
  cases hN
  cases f
  cases g
  rfl

theorem pullFunctor_id : pullFunctor (𝟙 S) = 𝟭 (Model S.source) := by
  apply Functor.hext pull_id
  intro M N h
  exact arrow_hext (pull_id M) (pull_id N) _ _

theorem pullFunctor_comp (f : S ⟶ T) (g : T ⟶ U) :
    pullFunctor (f ≫ g) = pullFunctor g ⋙ pullFunctor f := by
  apply Functor.hext (pull_comp f g)
  intro M N h
  exact arrow_hext (pull_comp f g M) (pull_comp f g N) _ _

theorem raw_id (t : Raw S.source) : raw (𝟙 S) t = t := by
  induction t with
  | var n => rfl
  | lam a t ih => simp only [raw, ih]
  | app t u iht ihu => simp only [raw, iht, ihu]
  | op o args ih => simp only [raw, ih]; rfl

theorem raw_comp (f : S ⟶ T) (g : T ⟶ U) (t : Raw S.source) :
    raw (f ≫ g) t = raw g (raw f t) := by
  induction t with
  | var n => rfl
  | lam a t ih => simp only [raw, ih]
  | app t u iht ihu => simp only [raw, iht, ihu]
  | op o args ih => simp only [raw, ih]; rfl

theorem term_id {Γ : Ctx S.source.Base} {τ : Ty S.source.Base} (t : Term S.source Γ τ) :
    t.mapOp (𝟙 S : S ⟶ S).operators = t := by
  induction t with
  | var v => rfl
  | lam t ih => exact congrArg Term.lam ih
  | app t u iht ihu => exact congrArg₂ Term.app iht ihu
  | op o args ih =>
      simp only [Term.mapOp]
      congr 1
      exact funext fun a => funext fun v => ih a v

theorem term_comp (f : S ⟶ T) (g : T ⟶ U)
    {Γ : Ctx S.source.Base} {τ : Ty S.source.Base} (t : Term S.source Γ τ) :
    t.mapOp (f ≫ g).operators = (t.mapOp f.operators).mapOp g.operators := by
  induction t with
  | var v => rfl
  | lam t ih => exact congrArg Term.lam ih
  | app t u iht ihu => exact congrArg₂ Term.app iht ihu
  | op o args ih =>
      simp only [Term.mapOp]
      congr 1
      exact funext fun a => funext fun v => ih a v

theorem sentence_id (p : STLC.Sentence S.source) : sentence (𝟙 S) p = p := by
  cases p <;> simp only [sentence, raw_id, term_id]

theorem sentence_comp (f : S ⟶ T) (g : T ⟶ U) (p : STLC.Sentence S.source) :
    sentence (f ≫ g) p = sentence g (sentence f p) := by
  cases p <;> simp only [sentence, raw_comp, term_comp]

end FixedHom

def sourceRoom (S : FixedSignature B) : Room.{0,0,1} :=
  ⟨STLC.Sentence S.source, Cat.of (Model S.source), fun M => STLC.Sat M.toSetModel⟩

/-- Actual inhabited STLC, with operator changes over fixed base types. -/
def sourceInstitution (B : Type) : FixedSignature B ⥤ Room.{0,0,1} where
  obj := sourceRoom
  map f := ⟨FixedHom.sentence f, FixedHom.pullFunctor f, FixedHom.satisfaction f⟩
  map_id _ := Room.hom_ext (funext FixedHom.sentence_id) FixedHom.pullFunctor_id
  map_comp f g := Room.hom_ext (funext (FixedHom.sentence_comp f g)) (FixedHom.pullFunctor_comp f g)

/-- All native sentences, independently evaluated in canonical full-function models. -/
def targetRoom (S : FixedSignature B) : Room.{0,0,1} :=
  ⟨Matching.FirstOrder.Sentence (nativeSignature S.source).symbols, Cat.of (Model S.source),
    fun M => Matching.FirstOrder.Sentence.Satisfies (nativeModel M)⟩

theorem target_satisfaction (f : S ⟶ T) (M : Model T.source)
    (p : Matching.FirstOrder.Sentence (nativeSignature S.source).symbols) :
    Matching.FirstOrder.Sentence.Satisfies (nativeModel M)
      (Matching.FirstOrder.Sentence.map (FixedHom.native (S := S) (T := T) f) p) ↔
    Matching.FirstOrder.Sentence.Satisfies (nativeModel (FixedHom.pull f M)) p := by
  rw [Matching.FirstOrder.Sentence.satisfaction, FixedHom.native_pull]

def targetInstitution (B : Type) : FixedSignature B ⥤ Room.{0,0,1} where
  obj := targetRoom
  map {S T} f := ⟨Matching.FirstOrder.Sentence.map (FixedHom.native (S := S) (T := T) f),
    FixedHom.pullFunctor f, target_satisfaction f⟩
  map_id S := Room.hom_ext (by
    funext p
    change Matching.FirstOrder.Sentence.map (FixedHom.native (𝟙 S)) p = p
    rw [FixedHom.native_id]
    exact Matching.FirstOrder.Sentence.map_id p) FixedHom.pullFunctor_id
  map_comp {S T U} f g := Room.hom_ext (by
    funext p
    change Matching.FirstOrder.Sentence.map (FixedHom.native (S := S) (T := U) (f ≫ g)) p =
      Matching.FirstOrder.Sentence.map (FixedHom.native (S := T) (T := U) g)
        (Matching.FirstOrder.Sentence.map (FixedHom.native (S := S) (T := T) f) p)
    rw [FixedHom.native_comp]
    exact Matching.FirstOrder.Sentence.map_comp _ _ p) (FixedHom.pullFunctor_comp f g)

def sourceInst (B : Type) : Inst := ⟨FixedSignature B, sourceInstitution B⟩
def targetInst (B : Type) : Inst := ⟨FixedSignature B, targetInstitution B⟩

def toMatchingNatural (B : Type) : sourceInstitution B ⟶ (𝟭 _) ⋙ targetInstitution B where
  app S := ⟨translate, 𝟭 _, fun M p => translate_satisfaction (S := S.source) M p⟩
  naturality := by
    intro S T f
    apply Room.hom_ext
    · funext p
      exact (translate_naturality f p).symm
    · rfl

/-- A qualified types→matching edge: inhabited fixed-base STLC to canonical native matching. -/
def toMatching (B : Type) : Inst.CoHom (sourceInst B) (targetInst B) :=
  ⟨𝟭 _, toMatchingNatural B⟩

theorem toMatching_modelExpansive (B : Type) : (toMatching B).ModelExpansive :=
  fun _ M => ⟨M, rfl⟩

end Silmaril.Logic.STLCMatching
