module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.LabelRenaming.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Typing.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Labels
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Combinators

public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.dsimp.instances true

universe v₁ v₂ u₁ u₂ w q

namespace Silmaril.Isotope.LambdaSSA.Semantics.Categorical

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.DeBruijn
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical
  (caseWithContext contextualLoop retainLeft splitMapCoprod)
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite

local notation "extendArrow" => Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.extend

section Labels

variable {V : Type u₁} [Category.{v₁} V] [CartesianMonoidalCategory V]
  [HasFiniteCoproducts V] {τ : Type w} [TypeFormers τ] (M : TypeModel τ V)

private theorem labelInject_get (L : LCtx τ) (i : Fin L.length) :
    labelInject M i (labelAt_get L i) =
      Sigma.ι (fun j : Fin L.length => M.obj (L.get j)) i := by
  unfold labelInject
  simp

theorem labelInject_labelMap_proof {L K : LCtx τ} {ρ : Nat → Nat} (hρ : Ren L K ρ)
    {i : Nat} {A : τ} (hi : At L i A) :
    labelInject M i hi ≫ labelMap M hρ = labelInject M (ρ i) (hρ hi) := by
  obtain ⟨hlt, hh⟩ := List.getElem?_eq_some_iff.mp hi
  let j : Fin L.length := ⟨i, hlt⟩
  change L.get j = A at hh
  subst A
  change labelInject M j (labelAt_get L j) ≫ _ = _
  rw [labelInject_get, labelMap, Sigma.ι_comp_desc]

private theorem labelHom_ext {L : LCtx τ} {Y : V} {f g : labelObj M L ⟶ Y}
    (h : ∀ (i : Nat) (A : τ) (hi : At L i A), labelInject M i hi ≫ f = labelInject M i hi ≫ g) :
    f = g := by
  apply Sigma.hom_ext
  intro i
  exact (labelInject_get M L i) ▸ h i (L.get i) (labelAt_get L i)

theorem labelMap_id_proof (L : LCtx τ) :
    labelMap M (SSA.Ren.id L) = 𝟙 (labelObj M L) := by
  apply labelHom_ext M
  intro i A hi
  rw [labelInject_labelMap_proof, Category.comp_id]
  rfl

theorem labelMap_comp_proof {L K H : LCtx τ} {ρ σ : Nat → Nat}
    (hρ : Ren L K ρ) (hσ : Ren K H σ) :
    labelMap M (SSA.Ren.comp hρ hσ) = labelMap M hρ ≫ labelMap M hσ := by
  apply labelHom_ext M
  intro i A hi
  rw [labelInject_labelMap_proof, ← Category.assoc, labelInject_labelMap_proof,
    labelInject_labelMap_proof]
  rfl

omit [TypeFormers τ] in
private theorem appendRen {L K : LCtx τ} {ρ : Nat → Nat} (hρ : Ren L K ρ)
    {n : Nat} (R : Fin n → τ) : Ren (List.ofFn R ++ L) (List.ofFn R ++ K) (liftN n ρ) := by
  simpa only [List.length_ofFn] using SSA.Ren.append hρ (List.ofFn R)

private theorem labelAppendSplit_labelMap {L K : LCtx τ} {ρ : Nat → Nat}
    (hρ : Ren L K ρ) {n : Nat} (R : Fin n → τ) :
    labelMap M (appendRen hρ R) ≫ labelAppendSplit M (List.ofFn R) K =
      labelAppendSplit M (List.ofFn R) L ≫ coprod.map (labelMap M hρ) (𝟙 _) := by
  apply labelHom_ext M
  intro i A hi
  by_cases hlocal : i < n
  · let j : Fin n := ⟨i, hlocal⟩
    have htype : A = R j := Option.some.inj (hi.symm.trans (localAt R j L))
    subst A
    have hmap : labelInject M i hi ≫ labelMap M (appendRen hρ R) =
        labelInject M i (localAt R j K) := by
      simpa only [liftN_lt ρ hlocal] using labelInject_labelMap_proof M (appendRen hρ R) hi
    have hL := labelAppendSplit_local M R j L
    have hK := labelAppendSplit_local M R j K
    rw [← Category.assoc, hmap, hK, ← Category.assoc, hL,
      Category.assoc, coprod.inr_map, Category.id_comp]
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt hlocal)
    have hL : At L j A := by simpa [At, List.getElem?_append_right] using hi
    have hmap : labelInject M (n + j) hi ≫ labelMap M (appendRen hρ R) =
        labelInject M (n + ρ j) (exitAt R (hρ hL)) := by
      simpa only [liftN_add_index] using labelInject_labelMap_proof M (appendRen hρ R) hi
    rw [← Category.assoc, hmap, labelAppendSplit_exit, ← Category.assoc,
      labelAppendSplit_exit M R hL, Category.assoc, coprod.inl_map, ← Category.assoc,
      labelInject_labelMap_proof]

end Labels

section Control

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  (J : Functor V C) [DistributiveFreydCategory J]

private noncomputable def distribute (E A B : V) :
    J.obj (E ⊗ (A ⨿ B)) ⟶ J.obj (E ⊗ A) ⨿ J.obj (E ⊗ B) :=
  J.map (DistributiveTensor.leftIso E A B).inv ≫ splitMapCoprod J (E ⊗ A) (E ⊗ B)

@[reassoc] private theorem distribute_naturality (E : V) {A B A' B' : V}
    (f : A ⟶ A') (g : B ⟶ B') :
    J.map (E ◁ coprod.map f g) ≫ distribute J E A' B' =
      distribute J E A B ≫ coprod.map (J.map (E ◁ f)) (J.map (E ◁ g)) := by
  let d := distribute J E A B
  have : IsIso d := by
    dsimp only [d, distribute, splitMapCoprod]
    infer_instance
  have h₁ : J.map (E ◁ (coprod.inl : A ⟶ A ⨿ B)) ≫ d = coprod.inl :=
    distributeMap_inl J E A B
  have h₂ : J.map (E ◁ (coprod.inr : B ⟶ A ⨿ B)) ≫ d = coprod.inr :=
    distributeMap_inr J E A B
  apply (cancel_epi (inv d)).mp
  apply coprod.hom_ext
  · have hinv : coprod.inl ≫ inv d = J.map (E ◁ (coprod.inl : A ⟶ A ⨿ B)) := by
      rw [← h₁, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    simp only [← Category.assoc, hinv]
    simp only [Category.assoc]
    rw [← J.map_comp_assoc, ← MonoidalCategory.whiskerLeft_comp, coprod.inl_map,
      MonoidalCategory.whiskerLeft_comp, J.map_comp]
    simp only [distribute, Category.assoc, distributeMap_inl_assoc, distributeMap_inl, coprod.inl_map]
  · have hinv : coprod.inr ≫ inv d = J.map (E ◁ (coprod.inr : B ⟶ A ⨿ B)) := by
      rw [← h₂, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    simp only [← Category.assoc, hinv]
    simp only [Category.assoc]
    rw [← J.map_comp_assoc, ← MonoidalCategory.whiskerLeft_comp, coprod.inr_map,
      MonoidalCategory.whiskerLeft_comp, J.map_comp]
    simp only [distribute, Category.assoc, distributeMap_inr_assoc, distributeMap_inr, coprod.inr_map]

private theorem caseWithContext_post {E A B D D' : V}
    (f : J.obj E ⟶ J.obj (A ⨿ B)) (g : J.obj (E ⊗ A) ⟶ J.obj D)
    (h : J.obj (E ⊗ B) ⟶ J.obj D) (k : J.obj D ⟶ J.obj D') :
    caseWithContext J f g h ≫ k = caseWithContext J f (g ≫ k) (h ≫ k) := by
  simp only [caseWithContext, Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind,
    Category.assoc, coprod.desc_comp]

private theorem caseWithContext_map {E A B A' B' D : V}
    (f : J.obj E ⟶ J.obj (A ⨿ B)) (a : A ⟶ A') (b : B ⟶ B')
    (left : J.obj (E ⊗ A') ⟶ J.obj D) (right : J.obj (E ⊗ B') ⟶ J.obj D) :
    caseWithContext J (f ≫ J.map (coprod.map a b)) left right =
      caseWithContext J f (J.map (E ◁ a) ≫ left) (J.map (E ◁ b) ≫ right) := by
  have route := distribute_naturality_assoc J E a b (coprod.desc left right)
  simp only [distribute, Category.assoc] at route
  simp only [caseWithContext, Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind,
    extend_post_map, Category.assoc, route, coprod.map_desc]

end Control

section Loop

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C]
  (J : Functor V C) [StrongElgotFreydCategory J]

private theorem contextualLoop_map {E A B B' : V}
    (f : J.obj (E ⊗ A) ⟶ J.obj (B ⨿ A)) (b : B ⟶ B') :
    contextualLoop J f ≫ J.map b =
      contextualLoop J (f ≫ J.map (coprod.map b (𝟙 A))) := by
  let copy := J.map (CartesianMonoidalCategory.lift
    (CartesianMonoidalCategory.fst E A) (𝟙 (E ⊗ A)))
  let body := copy ≫ retainLeft J f ≫ distribute J E B A
  change (iterate body ≫ J.map (CartesianMonoidalCategory.snd E B)) ≫ J.map b =
    iterate (copy ≫ retainLeft J (f ≫ J.map (coprod.map b (𝟙 A))) ≫
      distribute J E B' A) ≫ J.map (CartesianMonoidalCategory.snd E B')
  have hproj : CartesianMonoidalCategory.snd E B ≫ b =
      (E ◁ b) ≫ CartesianMonoidalCategory.snd E B' := by simp
  rw [Category.assoc, ← J.map_comp, hproj, J.map_comp, ← Category.assoc,
    ElgotCategory.naturality]
  have route := distribute_naturality J E b (𝟙 A)
  rw [MonoidalCategory.whiskerLeft_id, J.map_id] at route
  simp only [retainLeft_comp, retainLeft_map, body, Category.assoc, route]

end Loop

section Region

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C]
  (J : Functor V C) [StrongElgotFreydCategory J]
  {τ : Type w} [TypeFormers τ] (M : TypeModel τ V)
  {Φ : Type q} [HasTy Φ τ] [InstructionModel J M Φ]

private theorem cfgLabelRenaming {n : Nat} (R : Fin n → τ) (Γ : VCtx τ)
    {L K : LCtx τ} {ρ : Nat → Nat} (hρ : Ren L K ρ)
    (entry : J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M (List.ofFn R ++ L)))
    (blocks : J.obj (ctxObj M Γ ⊗ finiteLabelObj M R) ⟶
      J.obj (labelObj M (List.ofFn R ++ L))) :
    let E := ctxObj M Γ
    let labelRenaming := J.map (labelMap M (appendRen hρ R))
    let out := labelMap M hρ
    let routeL := J.map (labelAppendSplit M (List.ofFn R) L)
    let routeK := J.map (labelAppendSplit M (List.ofFn R) K)
    let localState := J.map ((𝟙 E) ⊗ₘ labelObjToFinite M R)
    caseWithContext J (entry ≫ labelRenaming ≫ routeK)
      (J.map (CartesianMonoidalCategory.snd E (labelObj M K)))
      (contextualLoop J (localState ≫ blocks ≫ labelRenaming ≫ routeK)) =
    caseWithContext J (entry ≫ routeL)
      (J.map (CartesianMonoidalCategory.snd E (labelObj M L)))
      (contextualLoop J (localState ≫ blocks ≫ routeL)) ≫ J.map out := by
  dsimp only
  have split := congrArg J.map (labelAppendSplit_labelMap M hρ R)
  simp only [Functor.map_comp] at split
  rw [split]
  simp only [← Category.assoc]
  rw [caseWithContext_map]
  simp only [Category.assoc, MonoidalCategory.whiskerLeft_id]
  rw [J.map_id, Category.id_comp]
  let body := J.map ((𝟙 (ctxObj M Γ)) ⊗ₘ labelObjToFinite M R) ≫
    blocks ≫ J.map (labelAppendSplit M (List.ofFn R) L)
  have mapLoop := contextualLoop_map J body (labelMap M hρ)
  simp only [body, Category.assoc] at mapLoop
  rw [← mapLoop]
  have projection : J.map ((ctxObj M Γ) ◁ labelMap M hρ) ≫
      J.map (CartesianMonoidalCategory.snd (ctxObj M Γ) (labelObj M K)) =
    J.map (CartesianMonoidalCategory.snd (ctxObj M Γ) (labelObj M L)) ≫
      J.map (labelMap M hρ) := by
    simp only [← Functor.map_comp]
    congr 1
    simp
  rw [projection, caseWithContext_post]

theorem RegionDenotes.renameLabels_proof {Γ : VCtx τ} {L K : LCtx τ} {ρ : Nat → Nat}
    {r : Region Φ} {hr : Region.HasType Γ r L}
    {f : J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M L)}
    (d : RegionDenotes J M hr f) (hρ : Ren L K ρ) :
    RegionDenotes J M (hr.renameLabels hρ) (f ≫ J.map (labelMap M hρ)) := by
  induction d generalizing K ρ with
  | br dt =>
      rw [Category.assoc, ← J.map_comp, labelInject_labelMap_proof]
      exact RegionDenotes.br dt
  | case de dl dr ihl ihr =>
      rw [caseWithContext_post]
      exact RegionDenotes.case de (ihl hρ) (ihr hρ)
  | let₁ da db ih =>
      simpa only [Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind, Category.assoc]
        using RegionDenotes.let₁ da (ih hρ)
  | let₂ da db ih =>
      simpa only [Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind, Category.assoc]
        using RegionDenotes.let₂ da (ih hρ)
  | @cfgZero Γ L entry R blocks he hb fe de ih =>
      exact RegionDenotes.cfgZero (R := R) (he.renameLabels hρ)
        (fun i => (hb i).renameLabels hρ) (ih hρ)
  | @cfg n R Γ L entry blocks he hb fe fb collective de db dc ihe ihb =>
      let hlabels := appendRen hρ R
      have dc' : CollectiveDenotes J M Γ R K
          (fun i => fb i ≫ J.map (labelMap M hlabels))
          (collective ≫ J.map (labelMap M hlabels)) := by
        constructor
        intro i
        rw [← Category.assoc, dc.restrict]
      have renamed := RegionDenotes.cfg (he.renameLabels hlabels)
        (fun i => (hb i).renameLabels hlabels) (ihe hlabels) (fun i => ihb i hlabels) dc'
      rw [← cfgLabelRenaming J M R Γ hρ fe collective]
      simpa only [Category.assoc] using renamed

end Region

end Silmaril.Isotope.LambdaSSA.Semantics.Categorical
