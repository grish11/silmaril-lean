module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Continuations.Direct.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Categorical.Defs
public import Silmaril.SSA.Isotope.LetIter.Categorical.Context.Iteration.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Labels.Thms

/-! # Categorical normalization of the one-block CFG dispatcher -/

public section

universe v₁ v₂ u₁ u₂ u₃ u₄

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.SingletonDispatcher

open Silmaril Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open CartesianMonoidalCategory (fst snd lift)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical
  (extend duplicate caseWithContext contextualLoop splitMapCoprod)
open Silmaril.Isotope.LetIter.Semantics.Categorical
  (TypeModel InstructionModel extend_map extend_postmap duplicate_central_of_tensor_eqToIso
    contextualLoop_pre_map contextualLoop_uniformity_of_diagonal routeEnvironment)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.dsimp.instances true

variable {V : Type u₁} [Category.{v₁} V] [CartesianMonoidalCategory V] [HasFiniteCoproducts V]
  {τ : Type u₃} [TypeFormers τ] (M : TypeModel τ V)
  {Φ : Type u₄} [HasTy Φ τ]

local notation "inj" => labelInject
local notation "payload" => singletonLabelPayload
local notation "cut" => labelAppendSplit

theorem labelHom_ext {L : LCtx τ} {Y : V} {f g : labelObj M L ⟶ Y}
    (h : ∀ (i : Nat) (A : τ) (hi : At L i A), inj M i hi ≫ f = inj M i hi ≫ g) :
    f = g := by
  apply Sigma.hom_ext
  intro i
  have hi : At L i (L.get i) := by simp [At, i.isLt]
  have hi' : inj M i hi = Sigma.ι (fun j : Fin L.length => M.obj (L.get j)) i := by
    unfold labelInject
    simp
  rw [← hi']
  exact h i (L.get i) hi

theorem labelInject_payload (A : τ) :
    inj M 0 (L := [A]) (A := A) rfl ≫ payload M A = 𝟙 _ := by
  unfold labelInject singletonLabelPayload
  simp

theorem payload_labelInject (A : τ) :
    payload M A ≫ inj M 0 (L := [A]) (A := A) rfl = 𝟙 _ := by
  apply labelHom_ext M
  intro i B hi
  cases i with
  | zero =>
    cases Option.some.inj hi
    rw [← Category.assoc, labelInject_payload, Category.id_comp, Category.comp_id]
  | succ i => simp [At] at hi

private theorem finite_one (A : τ) :
    labelObjToFinite M (fun _ : Fin 1 => A) =
      payload M A ≫ finiteLabelInject M (fun _ : Fin 1 => A) 0 := by
  apply labelHom_ext M
  intro i B hi
  cases i with
  | zero =>
    cases Option.some.inj hi
    rw [← Category.assoc, labelInject_payload, Category.id_comp]
    exact labelObjToFinite_local M (fun _ : Fin 1 => A) 0 rfl
  | succ i => simp [At] at hi

@[reassoc] theorem labelAppendSplit_zero (A : τ) (L : LCtx τ) :
    inj M 0 (L := A :: L) (A := A) rfl ≫ cut M [A] L =
      inj M 0 (L := [A]) (A := A) rfl ≫ coprod.inr :=
  labelAppendSplit_local M (fun _ : Fin 1 => A) L 0 rfl rfl

@[reassoc] theorem labelAppendSplit_succ (A : τ) {L : LCtx τ} {i : Nat} {D : τ} (hi : At L i D) :
    inj M (i + 1) (L := A :: L) hi ≫ cut M [A] L = inj M i hi ≫ coprod.inl := by
  have h : At (A :: L) (1 + i) D := by rw [Nat.add_comm]; exact hi
  have eq := labelAppendSplit_exit M (fun _ : Fin 1 => A) L hi h
  change inj M (1 + i) (L := A :: L) h ≫ cut M [A] L = _ at eq
  have same {j k : Nat} (hjk : j = k) (hj : At (A :: L) j D) (hk : At (A :: L) k D) :
      inj M j hj = inj M k hk := by subst k; rfl
  rw [same (Nat.add_comm i 1) hi h]
  exact eq

section CollectiveOne

variable {C : Type u₂} [Category.{v₂} C] (J : V ⥤ C)

theorem collectiveOne {Γ : VCtx τ} {L : LCtx τ} {A : τ}
    {fb : Fin 1 → (J.obj (ctxObj M (A :: Γ)) ⟶ J.obj (labelObj M (A :: L)))}
    {c : J.obj (ctxObj M Γ ⊗ finiteLabelObj M (fun _ : Fin 1 => A)) ⟶ J.obj (labelObj M (A :: L))}
    (dc : CollectiveDenotes J M Γ (fun _ : Fin 1 => A) L fb c) :
    J.map (ctxObj M Γ ◁ labelObjToFinite M (fun _ : Fin 1 => A)) ≫ c =
      J.map (ctxObj M Γ ◁ payload M A) ≫ fb 0 := by
  have hd := dc.restrict 0
  simp only [MonoidalCategory.id_tensorHom] at hd
  rw [finite_one M A, MonoidalCategory.whiskerLeft_comp, J.map_comp, Category.assoc, hd]

end CollectiveOne

variable {C : Type u₂} [Category.{v₂} C] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  (J : V ⥤ C)

section Denotation

variable [Iteration C] [ElgotCategory C] [StrongElgotFreydCategory J]
  [InstructionModel J M Φ] [RegionTypingCoherent (Φ := Φ) J M]

omit [RegionTypingCoherent (Φ := Φ) J M] in
theorem cfgOne {Γ : VCtx τ} {L : LCtx τ} {A : τ} {e p : Region Φ}
    {he : Region.HasType Γ e (A :: L)} {hp : Region.HasType (A :: Γ) p (A :: L)}
    {fe : J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M (A :: L))}
    {fp : J.obj (ctxObj M (A :: Γ)) ⟶ J.obj (labelObj M (A :: L))}
    (de : RegionDenotes J M he fe) (dp : RegionDenotes J M hp fp) :
    RegionDenotes J M (.cfg (fun _ : Fin 1 => A) he (fun _ => hp))
      (caseWithContext J (fe ≫ J.map (cut M [A] L))
        (J.map (snd (ctxObj M Γ) (labelObj M L)))
        (contextualLoop J (J.map (ctxObj M Γ ◁ payload M A) ≫ fp ≫ J.map (cut M [A] L)))) := by
  let R : Fin 1 → τ := fun _ => A
  obtain ⟨c, dc⟩ := collectiveDenotes_exists_succ J M 0 Γ R L (fun _ => fp)
  have den := RegionDenotes.cfg (R := R) he (fun _ => hp) de (fun _ => dp) dc
  have norm := collectiveOne M J dc
  have normDispatch :
      J.map (ctxObj M Γ ◁ labelObjToFinite M R) ≫ c ≫ J.map (cut M [A] L) =
        J.map (ctxObj M Γ ◁ payload M A) ≫ fp ≫ J.map (cut M [A] L) := by
    rw [← Category.assoc, norm, Category.assoc]
  have normTensor :
      J.map ((𝟙 (ctxObj M Γ)) ⊗ₘ labelObjToFinite M R) ≫ c ≫ J.map (cut M [A] L) =
        J.map (ctxObj M Γ ◁ payload M A) ≫ fp ≫ J.map (cut M [A] L) := by
    rw [MonoidalCategory.id_tensorHom, normDispatch]
  exact normTensor ▸ den

theorem denoteSingleCfg {Γ : VCtx τ} {L : LCtx τ} {A : τ} {e p : Region Φ}
    (he : Region.HasType Γ e (A :: L)) (hp : Region.HasType (A :: Γ) p (A :: L)) :
    denoteRegion J M (.cfg (fun _ : Fin 1 => A) he (fun _ => hp)) =
      caseWithContext J (denoteRegion J M he ≫ J.map (cut M [A] L))
        (J.map (snd (ctxObj M Γ) (labelObj M L)))
        (contextualLoop J (J.map (ctxObj M Γ ◁ payload M A) ≫
          denoteRegion J M hp ≫ J.map (cut M [A] L))) :=
  (cfgOne M J (denoteRegion_spec J M he) (denoteRegion_spec J M hp)).eq_denote J M |>.symm

theorem caseWithContext_inr {E A B D : V} (f : J.obj E ⟶ J.obj B)
    (l : J.obj (E ⊗ A) ⟶ J.obj D) (r : J.obj (E ⊗ B) ⟶ J.obj D) :
    caseWithContext J (f ≫ J.map (coprod.inr : B ⟶ A ⨿ B)) l r = extend J f ≫ r := by
  have h : (E ◁ (coprod.inr : B ⟶ A ⨿ B)) ≫ (DistributiveTensor.leftIso E A B).inv =
      coprod.inr := by
    apply (cancel_mono (DistributiveTensor.leftIso E A B).hom).1
    simp [DistributiveTensor.leftIso]
  simp only [caseWithContext, Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind,
    extend_postmap, Category.assoc]
  rw [← J.map_comp_assoc, h]
  simp only [splitMapCoprod, map_inr_inv_coprodComparison_assoc, coprod.inr_desc]

theorem denote_weakenCapture {Γ : VCtx τ} {L : LCtx τ} {A B : τ} {p : Region Φ}
    (hp : Region.HasType (A :: Γ) p L) :
    denoteRegion J M (hp.renameVars ((Ren.wk Γ B).lift A)) =
      J.map (fst (ctxObj M Γ) (M.obj B) ▷ M.obj A) ≫ denoteRegion J M hp := by
  let E := ctxObj M Γ
  let a := inj M 0 (L := [A]) (A := A) rfl
  let k := J.map (E ◁ payload M A) ≫ denoteRegion J M hp
  have h : ContinuationDenotes J M (Γ := Γ) (L := [A]) (K := L) (fun _ => p) k := by
    intro i D hi
    cases i with
    | zero =>
      cases Option.some.inj hi
      refine ⟨hp, ?_⟩
      change RegionDenotes J M hp (J.map ((𝟙 E) ⊗ₘ a) ≫ k)
      have ha : a ≫ payload M A = 𝟙 _ := labelInject_payload M A
      dsimp only [k]
      rw [MonoidalCategory.id_tensorHom, ← Category.assoc, ← J.map_comp,
        ← MonoidalCategory.whiskerLeft_comp, ha, MonoidalCategory.whiskerLeft_id]
      change RegionDenotes J M hp (J.map (𝟙 (ctxObj M (A :: Γ))) ≫ denoteRegion J M hp)
      rw [J.map_id, Category.id_comp]
      exact denoteRegion_spec J M hp
    | succ i => simp [At] at hi
  obtain ⟨_, d⟩ := (h.weakenCapture J M B) (i := 0) (A := A) rfl
  have dd := d.eq_denote J M
  simp only [MonoidalCategory.id_tensorHom] at dd
  change J.map ((E ⊗ M.obj B) ◁ a) ≫
    J.map (fst E (M.obj B) ▷ labelObj M [A]) ≫ k = _ at dd
  rw [← dd]
  simp only [k, ← Category.assoc, ← J.map_comp]
  congr 2
  have ha : a ≫ payload M A = 𝟙 _ := labelInject_payload M A
  rw [MonoidalCategory.whisker_exchange, Category.assoc,
    ← MonoidalCategory.whiskerLeft_comp, ha, MonoidalCategory.whiskerLeft_id,
    Category.comp_id]

end Denotation

variable [DistributiveFreydCategory J]

theorem route_inr {E A B : V} :
    J.map (E ◁ (coprod.inr : B ⟶ A ⨿ B)) ≫
        routeEnvironment J E A B = coprod.inr := by
  have h : (E ◁ (coprod.inr : B ⟶ A ⨿ B)) ≫ (DistributiveTensor.leftIso E A B).inv =
      coprod.inr := by
    apply (cancel_mono (DistributiveTensor.leftIso E A B).hom).1
    simp [DistributiveTensor.leftIso]
  simp only [routeEnvironment, ← J.map_comp_assoc, h,
    splitMapCoprod, map_inr_inv_coprodComparison]

theorem route_inl {E A B : V} :
    J.map (E ◁ (coprod.inl : A ⟶ A ⨿ B)) ≫
        routeEnvironment J E A B = coprod.inl := by
  have h : (E ◁ (coprod.inl : A ⟶ A ⨿ B)) ≫ (DistributiveTensor.leftIso E A B).inv =
      coprod.inl := by
    apply (cancel_mono (DistributiveTensor.leftIso E A B).hom).1
    simp [DistributiveTensor.leftIso]
  simp only [routeEnvironment, ← J.map_comp_assoc, h,
    splitMapCoprod, map_inl_inv_coprodComparison]

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.SingletonDispatcher
