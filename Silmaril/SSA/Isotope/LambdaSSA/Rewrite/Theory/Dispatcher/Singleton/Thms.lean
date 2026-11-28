module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Continuations.Direct.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Categorical.Defs
public import Silmaril.SSA.Isotope.LetIter.Categorical.Context.Iteration.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.SingletonDispatcher

/-! # One-block CFG label and dispatcher equations -/

public section

universe v₁ v₂ u₁ u₂ u₃ u₄

namespace Silmaril.Isotope.LambdaSSA.Semantics.Categorical.SingletonDispatcher

open Silmaril Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open CartesianMonoidalCategory (fst snd lift)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical
  (extend duplicate caseWithContext contextualLoop splitMapCoprod)
open Silmaril.Isotope.LetIter.Semantics.Categorical
  (TypeModel InstructionModel
    routeEnvironment)

variable {V : Type u₁} [Category.{v₁} V] [CartesianMonoidalCategory V] [HasFiniteCoproducts V]
  {τ : Type u₃} [TypeFormers τ] (M : TypeModel τ V)
  {Φ : Type u₄} [HasTy Φ τ]

theorem labelHom_ext {L : LCtx τ} {Y : V} {f g : labelObj M L ⟶ Y}
    (h : ∀ (i : Nat) (A : τ) (hi : At L i A), labelInject M i hi ≫ f = labelInject M i hi ≫ g) :
    f = g :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.SingletonDispatcher.labelHom_ext M h

theorem labelInject_payload (A : τ) :
    labelInject M 0 (L := [A]) (A := A) rfl ≫ singletonLabelPayload M A = 𝟙 _ :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.SingletonDispatcher.labelInject_payload M A

theorem payload_labelInject (A : τ) :
    singletonLabelPayload M A ≫ labelInject M 0 (L := [A]) (A := A) rfl = 𝟙 _ :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.SingletonDispatcher.payload_labelInject M A

@[reassoc] theorem labelAppendSplit_zero (A : τ) (L : LCtx τ) :
    labelInject M 0 (L := A :: L) (A := A) rfl ≫ labelAppendSplit M [A] L =
      labelInject M 0 (L := [A]) (A := A) rfl ≫ coprod.inr :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.SingletonDispatcher.labelAppendSplit_zero M A L

@[reassoc] theorem labelAppendSplit_succ (A : τ) {L : LCtx τ} {i : Nat} {D : τ} (hi : At L i D) :
    labelInject M (i + 1) (L := A :: L) hi ≫ labelAppendSplit M [A] L = labelInject M i hi ≫ coprod.inl :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.SingletonDispatcher.labelAppendSplit_succ M A hi

section CollectiveOne

variable {C : Type u₂} [Category.{v₂} C] (J : V ⥤ C)

/-- In a one-block dispatcher, decode the local payload and run block zero. -/
theorem collectiveOne {Γ : VCtx τ} {L : LCtx τ} {A : τ}
    {fb : Fin 1 → (J.obj (ctxObj M (A :: Γ)) ⟶ J.obj (labelObj M (A :: L)))}
    {c : J.obj (ctxObj M Γ ⊗ finiteLabelObj M (fun _ : Fin 1 => A)) ⟶ J.obj (labelObj M (A :: L))}
    (dc : CollectiveDenotes J M Γ (fun _ : Fin 1 => A) L fb c) :
    J.map (ctxObj M Γ ◁ labelObjToFinite M (fun _ : Fin 1 => A)) ≫ c =
      J.map (ctxObj M Γ ◁ singletonLabelPayload M A) ≫ fb 0 :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.SingletonDispatcher.collectiveOne M J dc

end CollectiveOne

variable {C : Type u₂} [Category.{v₂} C] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  (J : V ⥤ C)

section Denotation

variable [Iteration C] [ElgotCategory C] [StrongElgotFreydCategory J]
  [InstructionModel J M Φ] [RegionTypingCoherent (Φ := Φ) J M]

omit [RegionTypingCoherent (Φ := Φ) J M] in
/-- Assemble the actual one-block CFG arrow from supplied graph witnesses at
the indicated local label type. No global coherence premise is needed. -/
theorem cfgOne {Γ : VCtx τ} {L : LCtx τ} {A : τ} {e p : Region Φ}
    {he : Region.HasType Γ e (A :: L)} {hp : Region.HasType (A :: Γ) p (A :: L)}
    {fe : J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M (A :: L))}
    {fp : J.obj (ctxObj M (A :: Γ)) ⟶ J.obj (labelObj M (A :: L))}
    (de : RegionDenotes J M he fe) (dp : RegionDenotes J M hp fp) :
    RegionDenotes J M (.cfg (fun _ : Fin 1 => A) he (fun _ => hp))
      (caseWithContext J (fe ≫ J.map (labelAppendSplit M [A] L))
        (J.map (snd (ctxObj M Γ) (labelObj M L)))
        (contextualLoop J (J.map (ctxObj M Γ ◁ singletonLabelPayload M A) ≫
          fp ≫ J.map (labelAppendSplit M [A] L)))) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.SingletonDispatcher.cfgOne M J de dp

theorem denoteSingleCfg {Γ : VCtx τ} {L : LCtx τ} {A : τ} {e p : Region Φ}
    (he : Region.HasType Γ e (A :: L)) (hp : Region.HasType (A :: Γ) p (A :: L)) :
    denoteRegion J M (.cfg (fun _ : Fin 1 => A) he (fun _ => hp)) =
      caseWithContext J (denoteRegion J M he ≫ J.map (labelAppendSplit M [A] L))
        (J.map (snd (ctxObj M Γ) (labelObj M L)))
        (contextualLoop J (J.map (ctxObj M Γ ◁ singletonLabelPayload M A) ≫
          denoteRegion J M hp ≫ J.map (labelAppendSplit M [A] L))) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.SingletonDispatcher.denoteSingleCfg M J he hp

theorem caseWithContext_inr {E A B D : V} (f : J.obj E ⟶ J.obj B)
    (l : J.obj (E ⊗ A) ⟶ J.obj D) (r : J.obj (E ⊗ B) ⟶ J.obj D) :
    caseWithContext J (f ≫ J.map (coprod.inr : B ⟶ A ⨿ B)) l r = Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.extend J f ≫ r :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.SingletonDispatcher.caseWithContext_inr J f l r

theorem denote_weakenCapture {Γ : VCtx τ} {L : LCtx τ} {A B : τ} {p : Region Φ}
    (hp : Region.HasType (A :: Γ) p L) :
    denoteRegion J M (hp.renameVars ((Ren.wk Γ B).lift A)) =
      J.map (fst (ctxObj M Γ) (M.obj B) ▷ M.obj A) ≫ denoteRegion J M hp :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.SingletonDispatcher.denote_weakenCapture M J hp

end Denotation

variable [DistributiveFreydCategory J]

theorem route_inr {E A B : V} :
    J.map (E ◁ (coprod.inr : B ⟶ A ⨿ B)) ≫
        routeEnvironment J E A B = coprod.inr :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.SingletonDispatcher.route_inr J

theorem route_inl {E A B : V} :
    J.map (E ◁ (coprod.inl : A ⟶ A ⨿ B)) ≫
        routeEnvironment J E A B = coprod.inl :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.SingletonDispatcher.route_inl J

end Silmaril.Isotope.LambdaSSA.Semantics.Categorical.SingletonDispatcher
