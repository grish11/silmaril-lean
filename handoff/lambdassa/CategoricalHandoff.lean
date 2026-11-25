module

import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Outward.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Combinators

open CategoryTheory CategoryTheory.Limits
open Silmaril Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)

universe v₁ v₂ u₁ u₂ u₃ u₄

section

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C]
  (J : V ⥤ C) [StrongElgotFreydCategory J]
  {τ : Type u₃} [TypeFormers τ] (M : TypeModel τ V)
  {Φ : Type u₄} [HasTy Φ τ] [InstructionModel J M Φ]

/-- The structural denotation transport to supply from the semantic task. -/
private def RegionValueTransport : Prop :=
  ∀ {Γ Δ : VCtx τ} {L : LCtx τ} {r : Region Φ} {σ : Nat → Tm Φ}
    (hr : Region.HasType Γ r L) (hσ : Tm.Subst.HasType Γ Δ σ)
    (k : ctxObj M Δ ⟶ ctxObj M Γ)
    (_hs : ∀ ⦃i A⦄, (hi : At Γ i A) → Denotes J M (hσ hi) (J.map (k ≫ lookup M i hi)))
    {f : J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M L)},
    RegionDenotes J M hr f → RegionDenotes J M (hr.substVars hσ) (J.map k ≫ f)

set_option backward.isDefEq.respectTransparency false in
private theorem letValue_common (transport : RegionValueTransport (Φ := Φ) J M)
    {Γ : VCtx τ} {L : LCtx τ} {A : τ} {a : Tm Φ} {r : Region Φ}
    (ha : Tm.BranchValue Γ a A) (hr : Region.HasType (A :: Γ) r L) :
    ∃ f, RegionDenotes J M (.let₁ ha.hasType hr) f ∧
      RegionDenotes J M (hr.substVars (Tm.Subst.HasType.single ha.hasType)) f := by
  obtain ⟨p, dp⟩ := ha.denotes_map J M
  let k : ctxObj M Γ ⟶ ctxObj M (A :: Γ) := CartesianMonoidalCategory.lift (𝟙 _) p
  let hσ := Tm.Subst.HasType.single ha.hasType
  have hm : ∀ ⦃i D⦄, (hi : At (A :: Γ) i D) →
      Denotes J M (hσ hi) (J.map (k ≫ lookup M i hi)) := by
    intro i D hi
    cases i with
    | zero =>
        cases Option.some.inj hi
        change Denotes J M ha.hasType
          (J.map (k ≫ CartesianMonoidalCategory.snd (ctxObj M Γ) (M.obj A)))
        rw [show k ≫ CartesianMonoidalCategory.snd (ctxObj M Γ) (M.obj A) = p from
          CartesianMonoidalCategory.lift_snd _ _]
        exact dp
    | succ i =>
        have h : At Γ i D := hi
        change Denotes J M (.var h)
          (J.map (k ≫ CartesianMonoidalCategory.fst (ctxObj M Γ) (M.obj A) ≫ lookup M i h))
        rw [← Category.assoc, show k ≫ CartesianMonoidalCategory.fst (ctxObj M Γ) (M.obj A) = 𝟙 _ from
          CartesianMonoidalCategory.lift_fst _ _, Category.id_comp]
        exact .var h
  have de := denoteRegion_spec J M hr
  have d := RegionDenotes.let₁ dp de
  simp only [Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind,
    Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.extend_map] at d
  exact ⟨_, d, transport hr hσ k hm de⟩

variable [RegionTypingCoherent (Φ := Φ) J M]

private theorem common_of_value_transport (transport : RegionValueTransport (Φ := Φ) J M)
    (hu : PremonoidalCategory.IsCentral (Functor.StrongPremonoidal.unitIso (J := J)).hom)
    {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}
    (h : Region.SubstitutionEquiv Γ r s L) :
    ∃ (hr : Region.HasType Γ r L) (hs : Region.HasType Γ s L),
      ∃ f, RegionDenotes J M hr f ∧ RegionDenotes J M hs f := by
  induction h with
  | base h =>
      obtain ⟨hr, hs⟩ := h.typed
      exact ⟨hr, hs, _, denoteRegion_spec J M hr,
        (h.sound J M hr hs).symm ▸ denoteRegion_spec J M hs⟩
  | symm _ ih =>
      obtain ⟨hr, hs, f, dr, ds⟩ := ih
      exact ⟨hs, hr, f, ds, dr⟩
  | trans _ _ ihr ihs =>
      obtain ⟨hr, hs, f, dr, ds⟩ := ihr
      obtain ⟨_, ht, g, ds', dt⟩ := ihs
      have hfg : f = g := RegionTypingCoherent.denotes_eq (h := hs) ds ds'
      exact ⟨hr, ht, g, hfg ▸ dr, dt⟩
  | let₁ ha _ ih =>
      obtain ⟨hr, hs, f, dr, ds⟩ := ih
      have da := denote_spec J M ha
      exact ⟨.let₁ ha hr, .let₁ ha hs, _, .let₁ da dr, .let₁ da ds⟩
  | let₂ ha _ ih =>
      obtain ⟨hr, hs, f, dr, ds⟩ := ih
      have da := denote_spec J M ha
      exact ⟨.let₂ ha hr, .let₂ ha hs, _, .let₂ da dr, .let₂ da ds⟩
  | case ha _ _ ihl ihr =>
      obtain ⟨hl, hl', fl, dl, dl'⟩ := ihl
      obtain ⟨hr, hr', fr, dr, dr'⟩ := ihr
      have da := denote_spec J M ha
      exact ⟨.case ha hl hr, .case ha hl' hr', _, .case da dl dr, .case da dl' dr'⟩
  | @cfg n _ _ _ _ _ _ R _ _ ihe ihb =>
      obtain ⟨he, he', fe, de, de'⟩ := ihe
      choose hb hb' fb db using ihb
      cases n with
      | zero => exact ⟨.cfg R he hb, .cfg R he' hb', fe, .cfgZero he hb de, .cfgZero he' hb' de'⟩
      | succ n =>
          obtain ⟨_, dc⟩ := collectiveDenotes_exists_succ J M n _ R _ fb
          exact ⟨.cfg R he hb, .cfg R he' hb', _,
            .cfg he hb de (fun i => (db i).1) dc, .cfg he' hb' de' (fun i => (db i).2) dc⟩
  | letValue ha hr => exact ⟨_, _, letValue_common J M transport ha hr⟩
  | cfgOutward R hr hb =>
      have ht := (Region.SubstitutionEquiv.cfgOutward R hr hb).typed.1
      have e := denoteRegion_cfgOutward J M hu R hr hb ht
      exact ⟨ht, hr, _, e ▸ denoteRegion_spec J M ht, denoteRegion_spec J M hr⟩

/-- Assembling categorical invariance uses a structural value-substitution lemma. -/
theorem substitutionEquiv_sound_of_value_transport (transport : RegionValueTransport (Φ := Φ) J M)
    (hu : PremonoidalCategory.IsCentral (Functor.StrongPremonoidal.unitIso (J := J)).hom)
    {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}
    (h : Region.SubstitutionEquiv Γ r s L) (hr : Region.HasType Γ r L) (hs : Region.HasType Γ s L) :
    denoteRegion J M hr = denoteRegion J M hs := by
  obtain ⟨_, _, _, dr, ds⟩ := common_of_value_transport J M transport hu h
  exact (RegionDenotes.eq_denote (h := hr) J M dr).symm.trans
    (RegionDenotes.eq_denote (h := hs) J M ds)

#print axioms substitutionEquiv_sound_of_value_transport

end
