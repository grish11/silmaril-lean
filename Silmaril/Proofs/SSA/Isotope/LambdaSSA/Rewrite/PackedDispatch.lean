module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Categorical.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Continuations.Categorical.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.PackedLabels
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.CategoricalLink
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.CaseCfg
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.OutwardEffect
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.LabelRenaming.Thms

/-! # Categorical denotation of the typed packed-exit decoder -/

public section

universe v₁ v₂ u₁ u₂ u₃ u₄

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Region (packedExitType packedExitArg unpackExits)
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open CategoryTheory.CartesianMonoidalCategory (snd)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (extend)

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  [FreydCategory.CentralUnit J]
  {τ : Type u₃} [TypeFormers τ] (M : TypeModel τ V)
  {Φ : Type u₄} [HasTy Φ τ] [InstructionModel J M Φ]

set_option backward.isDefEq.respectTransparency false in
theorem unpackExits_denotes (Γ : VCtx τ) (L : LCtx τ) :
    ∃ h : Region.HasType (packedExitType L :: Γ) (unpackExits L : Region Φ) L,
      RegionDenotes J M h (J.map (snd (ctxObj M Γ) _ ≫ unpackLabel M L)) := by
  induction L generalizing Γ with
  | nil =>
    let h := Region.unpackExits_hasType (Φ := Φ) Γ ([] : LCtx τ)
    obtain ⟨f, df⟩ := regionDenotes_exists J M h
    have hZ : (coprod.inl : M.obj (Silmaril.empty : τ) ⟶ _ ⨿ _) = coprod.inr :=
      M.emptyIsInitial.hom_ext _ _
    have hf : f = J.map (snd (ctxObj M Γ) _ ≫ unpackLabel M []) :=
      context_of_empty_hom_ext J hZ
    exact ⟨h, hf ▸ df⟩
  | cons A L ih =>
    let P := packedExitType (A :: L)
    let E := ctxObj M (P :: Γ)
    let Q := packedExitType L
    obtain ⟨_, dTail⟩ := ih (P :: Γ)
    let ρ := Silmaril.Isotope.SSA.Ren.wk L A
    have dRight := dTail.renameLabels J M ρ
    rw [← J.map_comp, Category.assoc] at dRight
    let right : M.obj Q ⟶ labelObj M (A :: L) := unpackLabel M L ≫ labelMap M ρ
    let left := labelInject M (L := A :: L) 0 (A := A) rfl
    have dLeft : RegionDenotes J M (.br (rfl : At (A :: L) 0 A)
        (Tm.HasType.var (Φ := Φ) (i := 0) (Γ := A :: P :: Γ) (A := A) rfl))
        (J.map (snd E _ ≫ left)) := by
      rw [J.map_comp]
      exact .br (.var (i := 0) rfl)
    have dTest : Denotes J M (Tm.HasType.var
        (Φ := Φ) (i := 0) (Γ := P :: Γ) (A := P) rfl)
        (J.map (snd (ctxObj M Γ) (M.obj P))) := by
      exact .var (i := 0) rfl
    have d := RegionDenotes.case dTest dLeft dRight
    change RegionDenotes J M _ (Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.caseWithContext J
      (J.map (snd (ctxObj M Γ) (M.obj P)) ≫ J.map (M.coprodIso A Q).hom)
      (J.map (snd E (M.obj A) ≫ left))
      (J.map (snd (ctxObj M (P :: Γ)) (M.obj (packedExitType L)) ≫ right))) at d
    rw [case_snd_desc J (FreydCategory.CentralUnit.unit_central (J := J)),
      ← J.map_comp, ← J.map_comp, Category.assoc] at d
    exact ⟨_, d⟩

omit [FreydCategory.CentralUnit J] in
set_option backward.isDefEq.respectTransparency false in
theorem packedExitArg_denotes {Γ : VCtx τ} {L : LCtx τ} {i : Nat} {A : τ} {a : Tm Φ}
    (hi : At L i A) {ha : Tm.HasType Γ a A} {f : J.obj (ctxObj M Γ) ⟶ J.obj (M.obj A)}
    (da : Denotes J M ha f) :
    ∃ h : Tm.HasType Γ (packedExitArg i a) (packedExitType L),
      Denotes J M h (f ≫ J.map (packedLabelInject M i hi)) := by
  induction L generalizing i with
  | nil => simp [At] at hi
  | cons B L ih =>
    cases i with
    | zero =>
      cases Option.some.inj hi
      exact ⟨_, by simpa [packedLabelInject] using Denotes.inl (B := packedExitType L) da⟩
    | succ i =>
      obtain ⟨_, d⟩ := ih (show At L i A from hi)
      exact ⟨_, by
        simpa only [packedLabelInject, J.map_comp, Category.assoc] using Denotes.inr (A := B) d⟩

omit [FreydCategory.CentralUnit J] in
set_option backward.isDefEq.respectTransparency false in
theorem packContinuation_denotes (Γ : VCtx τ) (L : LCtx τ) :
    ContinuationDenotes J M (fun i => Region.br 0 (packedExitArg i (.var 0 : Tm Φ)))
      (J.map (snd (ctxObj M Γ) (labelObj M L) ≫ packLabelExit M L)) := by
  intro i A hi
  obtain ⟨ht, d⟩ := packedExitArg_denotes J M hi
    (Denotes.var (J := J) (M := M) (Φ := Φ) (i := 0) (Γ := A :: Γ) (A := A) rfl)
  rw [packLabelExit, MonoidalCategory.id_tensorHom, ← J.map_comp,
    CartesianMonoidalCategory.whiskerLeft_snd_assoc, labelInject_packLabel_assoc]
  have dr := RegionDenotes.br (h := (rfl : At [packedExitType L] 0 (packedExitType L))) d
  refine ⟨.br (rfl : At [packedExitType L] 0 (packedExitType L)) ht, ?_⟩
  simpa [lookup, J.map_comp, Category.assoc] using dr

set_option backward.isDefEq.respectTransparency false in
theorem unpackContinuation_denotes (Γ : VCtx τ) (L : LCtx τ) :
    ContinuationDenotes J M (fun _ => unpackExits L : Nat → Region Φ)
      (J.map (snd (ctxObj M Γ) (labelObj M [packedExitType L]) ≫ unpackLabelExit M L)) := by
  intro i A hi
  cases i with
  | zero =>
    cases Option.some.inj hi
    rw [unpackLabelExit, MonoidalCategory.id_tensorHom, ← J.map_comp,
      CartesianMonoidalCategory.whiskerLeft_snd_assoc, labelInject_singletonLabelPayload_assoc]
    exact unpackExits_denotes J M Γ L
  | succ i => simp [At] at hi

theorem denoteRegion_link_payload [RegionTypingCoherent (Φ := Φ) J M]
    {Γ : VCtx τ} {L K : LCtx τ} {r : Region Φ} {σ : Nat → Region Φ}
    (hr : Region.HasType Γ r L) (hs : Region.HasType Γ (r.linkExits L σ) K)
    (k : labelObj M L ⟶ labelObj M K)
    (hk : ContinuationDenotes J M σ (J.map (snd (ctxObj M Γ) (labelObj M L) ≫ k))) :
    denoteRegion J M hs = denoteRegion J M hr ≫ J.map k := by
  rw [denoteRegion_linkExits J M hr hs hk]
  simp only [Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind,
    J.map_comp, ← Category.assoc, extend_snd J (FreydCategory.CentralUnit.unit_central (J := J))]

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite
