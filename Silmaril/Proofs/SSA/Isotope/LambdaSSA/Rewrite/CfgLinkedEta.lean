module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Dispatcher.Eta.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Continuations.Categorical.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.EnvironmentNaturality
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Combinators
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.ValueSubstitution
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.OutwardEffect

/-! # Categorical CFG η for linked continuations -/

public section

universe v₁ v₂ u₁ u₂ u₃ u₄

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.DeBruijn (lift)
open Silmaril.Isotope.LambdaSSA.Region (cfgEntryContinuations liftLSubstVars renameVars_comp)
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (caseWithContext contextualLoop extend)
open CategoryTheory.CartesianMonoidalCategory (fst snd)

theorem lift_cfgEntryContinuations {Φ : Type u₄} {n : Nat} (blocks : Fin n → Region Φ) :
    liftLSubstVars (cfgEntryContinuations blocks) =
      cfgEntryContinuations (fun i => (blocks i).renameVars (lift Nat.succ)) := by
  funext i
  simp only [liftLSubstVars, cfgEntryContinuations, Region.renameVars, Tm.rename]
  congr 1
  funext j
  rw [renameVars_comp, renameVars_comp]
  congr 1
  funext i
  cases i with
  | zero => rfl
  | succ i => cases i <;> rfl

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

omit [FreydCategory.CentralUnit J] in
set_option backward.isDefEq.respectTransparency false in
private theorem dispatcherFamily_denotes {n : Nat} {Γ : VCtx τ} {L : LCtx τ}
    (R : Fin (n + 1) → τ) {blocks : Fin (n + 1) → Region Φ}
    (hb : ∀ i, Region.HasType (R i :: Γ) (blocks i) (List.ofFn R ++ L))
    {fb : ∀ i, J.obj (ctxObj M (R i :: Γ)) ⟶ J.obj (labelObj M (List.ofFn R ++ L))}
    (db : ∀ i, RegionDenotes J M (hb i) (fb i))
    {c : J.obj (ctxObj M Γ ⊗ finiteLabelObj M R) ⟶ J.obj (labelObj M (List.ofFn R ++ L))}
    (dc : CollectiveDenotes J M Γ R L fb c) :
    let E := ctxObj M Γ
    let B := labelObj M L
    let S := labelObj M (List.ofFn R)
    let split := labelAppendSplit M (List.ofFn R) L
    let body := J.map (E ◁ labelObjToFinite M R) ≫ c ≫ J.map split
    ContinuationDenotes J M (Region.cfgEntryContinuations blocks)
      (J.map (E ◁ split) ≫ distributeEnv J E B S ≫
        coprod.desc (J.map (snd E B)) (contextualLoop J body)) := by
  dsimp only
  intro i A hi
  let E := ctxObj M Γ
  let D := ctxObj M (A :: Γ)
  let B := labelObj M L
  let S := labelObj M (List.ofFn R)
  let split := labelAppendSplit M (List.ofFn R) L
  let projection : D ⟶ E := fst E (M.obj A)
  let j := labelInject M i hi
  let wk := (Silmaril.Isotope.SSA.Ren.wk Γ A)
  let c' := J.map (projection ▷ finiteLabelObj M R) ≫ c
  let body := J.map (E ◁ labelObjToFinite M R) ≫ c ≫ J.map split
  let body' := J.map (D ◁ labelObjToFinite M R) ≫ c' ≫ J.map split
  have dcoll : CollectiveDenotes J M (A :: Γ) R L
      (fun k => J.map (projection ▷ M.obj (R k)) ≫ fb k) c' := by
    constructor
    intro k
    simp only [c', MonoidalCategory.id_tensorHom, ← J.map_comp_assoc]
    rw [MonoidalCategory.whisker_exchange, J.map_comp_assoc]
    have h := dc.restrict k
    simp only [MonoidalCategory.id_tensorHom] at h
    exact congrArg (J.map (projection ▷ M.obj (R k)) ≫ ·) h
  have hb' (k : Fin (n + 1)) := (hb k).renameVars (wk.lift (R k))
  have db' (k : Fin (n + 1)) : RegionDenotes J M (hb' k)
      (J.map (projection ▷ M.obj (R k)) ≫ fb k) :=
    regionDenotes_weakenCapture_proof J M A (db k)
  have he : Region.HasType (A :: Γ) (.br i (.var 0) : Region Φ) (List.ofFn R ++ L) :=
    .br hi (.var rfl)
  have dEntry : RegionDenotes J M he (J.map (snd E (M.obj A)) ≫ J.map j) :=
    RegionDenotes.br (h := hi) (.var (i := 0) rfl)
  have d := RegionDenotes.cfg he hb' dEntry db' dcoll
  simp only [MonoidalCategory.id_tensorHom] at d
  change RegionDenotes J M (.cfg R he hb')
    (caseWithContext J ((J.map (snd E (M.obj A)) ≫ J.map j) ≫ J.map split)
      (J.map (snd D B)) (contextualLoop J body')) at d
  have hbody : body' = J.map (projection ▷ S) ≫ body := by
    simp only [body', body, c', Category.assoc]
    rw [← J.map_comp_assoc, MonoidalCategory.whisker_exchange, J.map_comp_assoc]
  have hleft : J.map (snd D B) = J.map (projection ▷ B) ≫ J.map (snd E B) := by
    rw [← J.map_comp, CartesianMonoidalCategory.whiskerRight_snd]
  rw [hleft, hbody, contextualLoop_pre_map J, Category.assoc, ← J.map_comp,
    ← J.map_comp, caseWithContext_payload J (j ≫ split)] at d
  refine ⟨.cfg R he hb', ?_⟩
  simpa only [MonoidalCategory.id_tensorHom, ← J.map_comp_assoc, ← MonoidalCategory.whiskerLeft_comp] using d

set_option backward.isDefEq.respectTransparency false in
theorem cfg_linked_eta_common {n : Nat} {Γ : VCtx τ} {L : LCtx τ} {entry : Region Φ}
    (R : Fin n → τ) {blocks : Fin n → Region Φ}
    (he : Region.HasType Γ entry (List.ofFn R ++ L))
    (hb : ∀ i, Region.HasType (R i :: Γ) (blocks i) (List.ofFn R ++ L)) :
    ∃ ht : Region.HasType Γ (entry.linkExits (List.ofFn R ++ L) (Region.cfgEntryContinuations blocks)) L,
      ∃ f, ∃ k : J.obj (ctxObj M Γ ⊗ labelObj M (List.ofFn R ++ L)) ⟶ J.obj (labelObj M L),
        RegionDenotes J M (.cfg R he hb) f ∧ RegionDenotes J M ht f ∧
          ContinuationDenotes J M (Region.cfgEntryContinuations blocks) k := by
  let E := ctxObj M Γ
  let B := labelObj M L
  cases n with
  | zero =>
    have he' : Region.HasType Γ entry L := he
    obtain ⟨f, df⟩ := regionDenotes_exists J M he'
    have hk : ContinuationDenotes J M (Γ := Γ) (L := L) (K := L)
        (Region.cfgEntryContinuations blocks) (J.map (snd E B)) := by
      intro i A hi
      have proj : (E ◁ labelInject M i hi) ≫ snd E B =
          snd E (M.obj A) ≫ labelInject M i hi := by
        exact CartesianMonoidalCategory.whiskerLeft_snd E (labelInject M i hi)
      simp only [MonoidalCategory.id_tensorHom, ← J.map_comp]
      have d : RegionDenotes J M (.br hi (.var (Φ := Φ) (Γ := A :: Γ) rfl))
          (J.map (snd E (M.obj A)) ≫ J.map (labelInject M i hi)) :=
        RegionDenotes.br (h := hi) (Denotes.var (i := 0) rfl)
      rw [← J.map_comp, ← proj] at d
      exact ⟨.cfg R (.br hi (.var rfl)) (fun j => j.elim0), .cfgZero (R := R) _ (fun j => j.elim0) d⟩
    obtain ⟨_, d⟩ := df.linkExits J M hk
    rw [Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind,
      extend_snd J (FreydCategory.CentralUnit.unit_central (J := J))] at d
    exact ⟨_, f, _, .cfgZero he hb df, d, hk⟩
  | succ n =>
    obtain ⟨f, df⟩ := regionDenotes_exists J M he
    let fb (i : Fin (n + 1)) := denoteRegion J M (hb i)
    obtain ⟨c, dc⟩ := collectiveDenotes_exists_succ J M n Γ R L fb
    have db (i : Fin (n + 1)) := denoteRegion_spec J M (hb i)
    have hk := dispatcherFamily_denotes J M R hb db dc
    obtain ⟨_, d⟩ := df.linkExits J M hk
    have h := RegionDenotes.cfg he hb df db dc
    simp only [Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind, distributeEnv] at d
    change RegionDenotes J M _ (caseWithContext J
      (f ≫ J.map (labelAppendSplit M (List.ofFn R) L)) (J.map (snd E B)) _) at h
    simp only [caseWithContext, Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind,
      extend_post_map, MonoidalCategory.id_tensorHom, Category.assoc] at h
    exact ⟨_, _, _, h, by simpa only [Category.assoc] using d, hk⟩

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite
