module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Typing.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.EnvironmentNaturality
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Combinators

/-! # Categorical transport along a pure variable substitution -/

public section

universe v₁ v₂ u₁ u₂ u₃ u₄

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.DeBruijn (lift)
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)

local notation "fst" => CartesianMonoidalCategory.fst
local notation "snd" => CartesianMonoidalCategory.snd
local notation "liftPair" => CartesianMonoidalCategory.lift

set_option backward.isDefEq.respectTransparency false

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  (J : V ⥤ C) {τ : Type u₃} [TypeFormers τ] (M : TypeModel τ V)

section Terms

variable [DistributiveFreydCategory J] {Φ : Type u₄} [HasTy Φ τ] [InstructionModel J M Φ]

omit [DistributiveFreydCategory J] [SymmetricCategory V] [DistributiveTensor V] in
private theorem lookup_zero {Γ : VCtx τ} {A : τ} :
    lookup M (Γ := A :: Γ) 0 (rfl : At (A :: Γ) 0 A) = snd (ctxObj M Γ) (M.obj A) := by
  simp [lookup]

omit [DistributiveFreydCategory J] [SymmetricCategory V] [DistributiveTensor V] in
private theorem lookup_succ {Γ : VCtx τ} {A B : τ} {i : Nat} (h : At Γ i A) :
    lookup M (Γ := B :: Γ) (i + 1) h = fst (ctxObj M Γ) (M.obj B) ≫ lookup M i h := rfl

omit [DistributiveFreydCategory J] [SymmetricCategory V] [DistributiveTensor V] in
theorem renameLookup_lift {Γ Δ : VCtx τ} {ρ : Nat → Nat} (hρ : Ren Γ Δ ρ)
    {k : ctxObj M Δ ⟶ ctxObj M Γ}
    (hk : ∀ ⦃i A⦄ (h : At Γ i A), k ≫ lookup M i h = lookup M (ρ i) (hρ h)) (B : τ) :
    ∀ ⦃i A⦄ (h : At (B :: Γ) i A),
      (k ▷ M.obj B) ≫ lookup M i h = lookup M (lift ρ i) ((hρ.lift B) h) := by
  intro i A hi
  cases i with
  | zero =>
    have h : B = A := Option.some.inj hi
    subst A
    simp [lookup_zero, lift]
  | succ i =>
    change (k ▷ M.obj B) ≫ lookup M (i + 1) hi = lookup M (ρ i + 1) ((hρ.lift B) hi)
    rw [lookup_succ, lookup_succ, CartesianMonoidalCategory.whiskerRight_fst_assoc, hk]

theorem denotes_rename {Γ : VCtx τ} {a : Tm Φ} {A : τ} {ha : Tm.HasType Γ a A}
    {f : J.obj (ctxObj M Γ) ⟶ J.obj (M.obj A)} (d : Denotes J M ha f)
    {Δ : VCtx τ} {ρ : Nat → Nat} (hρ : Ren Γ Δ ρ) {k : ctxObj M Δ ⟶ ctxObj M Γ}
    (hk : ∀ ⦃i B⦄ (h : At Γ i B), k ≫ lookup M i h = lookup M (ρ i) (hρ h)) :
    Denotes J M (ha.rename hρ) (J.map k ≫ f) := by
  induction d generalizing Δ ρ with
  | var h =>
    rw [← J.map_comp, hk]
    exact .var (hρ h)
  | op _ ih => simpa only [Category.assoc] using Denotes.op (ih hρ hk)
  | let₁ _ _ iha ihb =>
    rw [← bind_pre_map]
    exact .let₁ (iha hρ hk) (ihb (hρ.lift _) (renameLookup_lift M hρ hk _))
  | let₂ _ _ iha ihb =>
    simp only [MonoidalCategory.id_tensorHom, ctxPairIso, Iso.symm_hom]
    rw [← bindPair_pre_map]
    simpa only [MonoidalCategory.id_tensorHom, ctxPairIso, Iso.symm_hom] using
      Denotes.let₂ (iha hρ hk) (ihb ((hρ.lift _).lift _)
        (renameLookup_lift M _ (renameLookup_lift M hρ hk _) _))
  | pair _ _ iha ihb =>
    simp only [← Category.assoc, ← pair_pre_map]
    exact .pair (iha hρ hk) (ihb hρ hk)
  | unit =>
    rw [← J.map_comp]
    rw [← Category.assoc, CartesianMonoidalCategory.isTerminalTensorUnit.hom_ext
      (k ≫ CartesianMonoidalCategory.toUnit _) (CartesianMonoidalCategory.toUnit _)]
    exact .unit
  | inl _ ih => simpa only [Category.assoc] using Denotes.inl (ih hρ hk)
  | inr _ ih => simpa only [Category.assoc] using Denotes.inr (ih hρ hk)
  | abort _ ih => simpa only [Category.assoc] using Denotes.abort (ih hρ hk)
  | case _ _ _ ihe ihl ihr =>
    rw [← case_pre_map, ← Category.assoc (J.map k)]
    exact .case (ihe hρ hk) (ihl (hρ.lift _) (renameLookup_lift M hρ hk _))
      (ihr (hρ.lift _) (renameLookup_lift M hρ hk _))

@[expose] def SubstDenotes {Γ Δ : VCtx τ} (σ : Nat → Tm Φ) (k : ctxObj M Δ ⟶ ctxObj M Γ) : Prop :=
  ∀ ⦃i A⦄ (hi : At Γ i A), ∃ h : Tm.HasType Δ (σ i) A,
    Denotes J M h (J.map (k ≫ lookup M i hi))

private theorem substDenotes_lift {Γ Δ : VCtx τ} {σ : Nat → Tm Φ}
    {k : ctxObj M Δ ⟶ ctxObj M Γ} (hσ : SubstDenotes J M σ k) (B : τ) :
    SubstDenotes J M (Γ := B :: Γ) (Δ := B :: Δ) (Tm.liftSubst σ) (k ▷ M.obj B) := by
  intro i A hi
  cases i with
  | zero =>
    have h : B = A := Option.some.inj hi
    subst A
    refine ⟨.var rfl, ?_⟩
    simp only [lookup_zero, CartesianMonoidalCategory.whiskerRight_snd]
    exact .var (i := 0) rfl
  | succ i =>
    obtain ⟨ha, da⟩ := hσ (show At Γ i A from hi)
    let π := fst (ctxObj M Δ) (M.obj B)
    have dr := denotes_rename J M da (Ren.wk Δ B) (k := π)
      (fun _ _ hz => (lookup_succ M (B := B) hz).symm)
    refine ⟨ha.weaken B, ?_⟩
    rw [lookup_succ, CartesianMonoidalCategory.whiskerRight_fst_assoc]
    simpa only [π, ← J.map_comp] using dr

private theorem denotes_subst {Γ : VCtx τ} {a : Tm Φ} {A : τ} {ha : Tm.HasType Γ a A}
    {f : J.obj (ctxObj M Γ) ⟶ J.obj (M.obj A)} (d : Denotes J M ha f)
    {Δ : VCtx τ} {σ : Nat → Tm Φ} {k : ctxObj M Δ ⟶ ctxObj M Γ}
    (hσ : SubstDenotes J M σ k) :
    ∃ ht : Tm.HasType Δ (a.subst σ) A, Denotes J M ht (J.map k ≫ f) := by
  induction d generalizing Δ σ with
  | var h =>
    rw [← J.map_comp]
    exact hσ h
  | op _ ih =>
    obtain ⟨_, da⟩ := ih hσ
    exact ⟨_, by simpa only [Category.assoc] using Denotes.op da⟩
  | let₁ _ _ iha ihb =>
    obtain ⟨_, da⟩ := iha hσ
    obtain ⟨_, db⟩ := ihb (substDenotes_lift J M hσ _)
    rw [← bind_pre_map]
    exact ⟨_, .let₁ da db⟩
  | let₂ _ _ iha ihb =>
    obtain ⟨ha, da⟩ := iha hσ
    obtain ⟨hb, db⟩ := ihb (substDenotes_lift J M (substDenotes_lift J M hσ _) _)
    simp only [MonoidalCategory.id_tensorHom, ctxPairIso, Iso.symm_hom]
    rw [← bindPair_pre_map]
    refine ⟨.let₂ ha hb, ?_⟩
    simpa only [MonoidalCategory.id_tensorHom, ctxPairIso, Iso.symm_hom] using Denotes.let₂ da db
  | pair _ _ iha ihb =>
    obtain ⟨ha, da⟩ := iha hσ
    obtain ⟨hb, db⟩ := ihb hσ
    simp only [← Category.assoc, ← pair_pre_map]
    exact ⟨.pair ha hb, .pair da db⟩
  | unit =>
    rw [← J.map_comp, ← Category.assoc, CartesianMonoidalCategory.isTerminalTensorUnit.hom_ext
      (k ≫ CartesianMonoidalCategory.toUnit _) (CartesianMonoidalCategory.toUnit _)]
    exact ⟨_, .unit⟩
  | inl _ ih =>
    obtain ⟨_, da⟩ := ih hσ
    exact ⟨_, by simpa only [Category.assoc] using Denotes.inl da⟩
  | inr _ ih =>
    obtain ⟨_, da⟩ := ih hσ
    exact ⟨_, by simpa only [Category.assoc] using Denotes.inr da⟩
  | abort _ ih =>
    obtain ⟨_, da⟩ := ih hσ
    exact ⟨_, by simpa only [Category.assoc] using Denotes.abort da⟩
  | case _ _ _ ihe ihl ihr =>
    obtain ⟨_, de⟩ := ihe hσ
    obtain ⟨_, dl⟩ := ihl (substDenotes_lift J M hσ _)
    obtain ⟨_, dr⟩ := ihr (substDenotes_lift J M hσ _)
    rw [← case_pre_map, ← Category.assoc (J.map k)]
    exact ⟨_, .case de dl dr⟩

end Terms

section Regions

variable [Iteration C] [ElgotCategory C] [StrongElgotFreydCategory J]
  {Φ : Type u₄} [HasTy Φ τ] [InstructionModel J M Φ]

open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (caseWithContext contextualLoop)

theorem regionDenotes_subst {Γ : VCtx τ} {L : LCtx τ} {r : Region Φ}
    {hr : Region.HasType Γ r L} {f : J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M L)}
    (d : RegionDenotes J M hr f) {Δ : VCtx τ} {σ : Nat → Tm Φ}
    {k : ctxObj M Δ ⟶ ctxObj M Γ} (hσ : SubstDenotes J M σ k) :
    ∃ ht : Region.HasType Δ (r.substVars σ) L, RegionDenotes J M ht (J.map k ≫ f) := by
  induction d generalizing Δ σ with
  | br da =>
    obtain ⟨_, db⟩ := denotes_subst J M da hσ
    exact ⟨_, by simpa only [Category.assoc] using RegionDenotes.br db⟩
  | let₁ da _ ih =>
    obtain ⟨_, da'⟩ := denotes_subst J M da hσ
    obtain ⟨_, db'⟩ := ih (substDenotes_lift J M hσ _)
    rw [← bind_pre_map]
    exact ⟨_, .let₁ da' db'⟩
  | let₂ da _ ih =>
    obtain ⟨ha, da'⟩ := denotes_subst J M da hσ
    obtain ⟨hb, db'⟩ := ih (substDenotes_lift J M (substDenotes_lift J M hσ _) _)
    simp only [MonoidalCategory.id_tensorHom, ctxPairIso, Iso.symm_hom]
    rw [← bindPair_pre_map]
    refine ⟨.let₂ ha hb, ?_⟩
    simpa only [MonoidalCategory.id_tensorHom, ctxPairIso, Iso.symm_hom] using RegionDenotes.let₂ da' db'
  | case de _ _ ihl ihr =>
    obtain ⟨_, de'⟩ := denotes_subst J M de hσ
    obtain ⟨_, dl'⟩ := ihl (substDenotes_lift J M hσ _)
    obtain ⟨_, dr'⟩ := ihr (substDenotes_lift J M hσ _)
    rw [← case_pre_map, ← Category.assoc (J.map k)]
    exact ⟨_, .case de' dl' dr'⟩
  | @cfgZero Γ L entry R blocks he hb fe de ihe =>
    obtain ⟨he', de'⟩ := ihe hσ
    exact ⟨_, RegionDenotes.cfgZero he' (fun i => Fin.elim0 i) de'⟩
  | @cfg n R Γ L entry blocks he hb fe fb collective de db dc ihe ihb =>
    obtain ⟨he', de'⟩ := ihe hσ
    choose hb' db' using fun i => ihb i (substDenotes_lift J M hσ (R i))
    let D := ctxObj M Δ
    let E := ctxObj M Γ
    let X := finiteLabelObj M R
    let Y := labelObj M (List.ofFn R)
    let B := labelObj M L
    let split := J.map (labelAppendSplit M (List.ofFn R) L)
    let collective' : J.obj (D ⊗ X) ⟶ J.obj (labelObj M (List.ofFn R ++ L)) :=
      J.map (k ▷ X) ≫ collective
    have dc' : CollectiveDenotes J M Δ R L (fun i => J.map (k ▷ M.obj (R i)) ≫ fb i) collective' := by
      constructor
      intro i
      simp only [collective', MonoidalCategory.id_tensorHom, ← J.map_comp_assoc]
      rw [MonoidalCategory.whisker_exchange, J.map_comp_assoc]
      have eq := dc.restrict i
      simp only [MonoidalCategory.id_tensorHom] at eq
      exact congrArg (J.map (k ▷ M.obj (R i)) ≫ ·) eq
    let body := J.map (E ◁ labelObjToFinite M R) ≫ collective ≫ split
    let body' := J.map (D ◁ labelObjToFinite M R) ≫ collective' ≫ split
    have hbody : body' = J.map (k ▷ Y) ≫ body := by
      simp only [body', body, collective', Category.assoc]
      rw [← J.map_comp_assoc, MonoidalCategory.whisker_exchange, J.map_comp_assoc]
    have proj : J.map (k ▷ B) ≫ J.map (snd E B) = J.map (snd D B) := by
      rw [← J.map_comp, CartesianMonoidalCategory.whiskerRight_snd]
    simp only [MonoidalCategory.id_tensorHom]
    change ∃ ht : Region.HasType Δ ((Region.cfg entry (n + 1) blocks).substVars σ) L,
      RegionDenotes J M ht
      (J.map k ≫ caseWithContext J (fe ≫ split) (J.map (snd E B)) (contextualLoop J body))
    rw [← case_pre_map, ← Category.assoc (J.map k) fe, proj, ← contextualLoop_pre_map, ← hbody]
    refine ⟨.cfg R he' hb', ?_⟩
    simpa only [body', split, MonoidalCategory.id_tensorHom] using RegionDenotes.cfg he' hb' de' db' dc'

theorem regionDenotes_replaceNewest {Γ : VCtx τ} {L : LCtx τ} {r : Region Φ} {a : Tm Φ}
    {A B : τ} {hr : Region.HasType (A :: Γ) r L}
    {f : J.obj (ctxObj M (A :: Γ)) ⟶ J.obj (labelObj M L)}
    (d : RegionDenotes J M hr f) {p : M.obj B ⟶ M.obj A} {ha : Tm.HasType (B :: Γ) a A}
    (da : Denotes J M ha (J.map (snd (ctxObj M Γ) (M.obj B) ≫ p))) :
    ∃ ht : Region.HasType (B :: Γ) (r.substVars (Tm.replaceNewest a)) L,
      RegionDenotes J M ht (J.map (ctxObj M Γ ◁ p) ≫ f) := by
  apply regionDenotes_subst J M d
  intro i D hi
  cases i with
  | zero =>
    cases Option.some.inj hi
    rw [lookup_zero, CartesianMonoidalCategory.whiskerLeft_snd]
    exact ⟨ha, da⟩
  | succ i =>
    rw [lookup_succ, CartesianMonoidalCategory.whiskerLeft_fst_assoc]
    refine ⟨.var (i := i + 1) hi, ?_⟩
    simpa only [lookup_succ] using Denotes.var (J := J) (M := M) (Φ := Φ)
      (Γ := B :: Γ) (i := i + 1) hi

theorem regionDenotes_weakenCapture_proof {Γ : VCtx τ} {L : LCtx τ} {r : Region Φ}
    {A : τ} (B : τ) {hr : Region.HasType (A :: Γ) r L}
    {f : J.obj (ctxObj M (A :: Γ)) ⟶ J.obj (labelObj M L)}
    (d : RegionDenotes J M hr f) :
    RegionDenotes J M (hr.renameVars ((Ren.wk Γ B).lift A))
      (J.map (fst (ctxObj M Γ) (M.obj B) ▷ M.obj A) ≫ f) := by
  let ρ := (Ren.wk Γ B).lift A
  let k := fst (ctxObj M Γ) (M.obj B)
  have hk : ∀ ⦃i T⦄ (h : At Γ i T),
      k ≫ lookup M i h = lookup M (i + 1) ((Ren.wk Γ B) h) :=
    fun _ _ h => (lookup_succ M (B := B) h).symm
  have hσ : SubstDenotes J M (Φ := Φ) (Γ := A :: Γ) (Δ := A :: B :: Γ)
      (Tm.var ∘ lift Nat.succ) (k ▷ M.obj A) := by
    intro i T h
    refine ⟨.var (ρ h), ?_⟩
    rw [renameLookup_lift M (Ren.wk Γ B) hk A h]
    exact .var (ρ h)
  obtain ⟨ht, dt⟩ := regionDenotes_subst J M d hσ
  simpa only [← Region.renameVars_eq_substVars] using dt

theorem regionDenotes_substValue_proof {Γ : VCtx τ} {L : LCtx τ} {r : Region Φ}
    {a : Tm Φ} {A : τ} {hr : Region.HasType (A :: Γ) r L}
    {f : J.obj (ctxObj M (A :: Γ)) ⟶ J.obj (labelObj M L)}
    (d : RegionDenotes J M hr f) {p : ctxObj M Γ ⟶ M.obj A} {ha : Tm.HasType Γ a A}
    (da : Denotes J M ha (J.map p)) :
    ∃ ht : Region.HasType Γ (r.substVars (Tm.singleSubst a)) L,
      RegionDenotes J M ht (J.map (liftPair (𝟙 _) p) ≫ f) := by
  apply regionDenotes_subst J M d
  intro i B hi
  cases i with
  | zero =>
    have h : A = B := Option.some.inj hi
    subst B
    simp only [lookup_zero, CartesianMonoidalCategory.lift_snd]
    exact ⟨ha, da⟩
  | succ i =>
    simp only [lookup_succ, CartesianMonoidalCategory.lift_fst_assoc, Category.id_comp]
    exact ⟨.var (i := i) (show At Γ i B from hi), .var (i := i) hi⟩

theorem letValue_common {Γ : VCtx τ} {L : LCtx τ} {r : Region Φ} {a : Tm Φ} {A : τ}
    (ha : Tm.BranchValue Γ a A) (hr : Region.HasType (A :: Γ) r L) :
    ∃ (ht : Region.HasType Γ (r.substVars (Tm.singleSubst a)) L), ∃ f,
      RegionDenotes J M (.let₁ ha.hasType hr) f ∧ RegionDenotes J M ht f := by
  obtain ⟨p, da⟩ := ha.denotes_map J M
  obtain ⟨f, dr⟩ := regionDenotes_exists J M hr
  obtain ⟨ht, dt⟩ := regionDenotes_substValue_proof J M dr da
  have dlet := RegionDenotes.let₁ da dr
  simp only [Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind, extend_map] at dlet
  exact ⟨ht, _, dlet, dt⟩

end Regions

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite
