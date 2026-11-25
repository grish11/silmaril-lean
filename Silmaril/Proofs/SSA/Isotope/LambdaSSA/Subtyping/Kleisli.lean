module

public import Silmaril.SSA.Isotope.LambdaSSA.Subtyping.Kleisli.Defs

@[expose] public section

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.dsimp.instances true

namespace Silmaril.Isotope.LambdaSSA.Subtyping.Semantics

open CategoryTheory CategoryTheory.Limits Silmaril.Elgot
open scoped MonoidalCategory
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical
  (typeJ ofTypeModel ofInstructionModel bind_of pair_of caseWithContext_of)

universe u v q r

namespace Agreement

open LambdaSSA.Semantics.Agreement
  (envToCategorical lookup_agrees coprod_hom_agrees collectiveArrow
    collective_toCategorical cfgDenotation_agrees)

variable {τ : Type u} [TypeFormers τ] [Subtyping τ] [TypeModel.{u, v} τ]
variable {Φ : Type q} [HasTy Φ τ]
variable {ε : Type r} [HasEff Φ ε] [Bot ε]
variable {m : Type v → Type v} [Monad m] [LawfulMonad m]
variable [InstructionModel Φ τ ε m]

/-- Every witness of the direct monadic graph induces a witness of the
categorical graph specialized to the Kleisli/Freyd model, with pointwise equal
underlying functions.  No proof-irrelevance or typing-coherence assumption is
used. -/
private theorem denotes_toCategorical {Γ : VCtx τ} {t : Tm Φ} {A : τ}
    {h : Tm.HasType Γ t A} {f : Monadic.Env Γ → m (TyDen A)}
    (d : Monadic.Denotes (m := m) ε h f) :
    let _ := ofInstructionModel
      (τ := τ) (Φ := Φ) (ε := ε) (m := m)
    ∃ F, Categorical.Denotes (typeJ (m := m)) (ofTypeModel (τ := τ)) h F ∧
      (fun ρ => F.of (envToCategorical ρ)) = f := by
  dsimp
  let _ := ofInstructionModel
    (τ := τ) (Φ := Φ) (ε := ε) (m := m)
  induction d with
  | var h =>
      exact ⟨_, .var h, funext (lookup_agrees _ h)⟩
  | op d ih =>
      rcases ih with ⟨F, dF, eF⟩
      refine ⟨_, .op dF, ?_⟩
      funext ρ
      have hF := congrFun eF ρ
      simp [ofInstructionModel, joinM, bind_map_left, hF]
  | let₁ da db iha ihb =>
      rcases iha with ⟨F, dF, eF⟩
      rcases ihb with ⟨G, dG, eG⟩
      refine ⟨_, .let₁ dF dG, ?_⟩
      funext ρ
      have hF := congrFun eF ρ
      have hG (a) := congrFun eG (ρ, a)
      erw [bind_of]
      simp only [Bind.kleisliRight]
      exact congrArg₂ (fun (x : m _) (k : _ → m _) => x >>= k) hF (funext hG)
  | pair da db iha ihb =>
      rcases iha with ⟨F, dF, eF⟩
      rcases ihb with ⟨G, dG, eG⟩
      refine ⟨_, .pair dF dG, ?_⟩
      funext ρ
      have hF := congrFun eF ρ
      have hG := congrFun eG ρ
      erw [Kleisli.Type.comp_of_eq_kleisliRight]
      simp only [Bind.kleisliRight]
      have hp := pair_of (m := m) F G (envToCategorical ρ)
      rw [hp]
      simp [Bind.kleisliRight, hF, hG, bind_assoc]
      rfl
  | unit =>
      refine ⟨_, .unit, ?_⟩
      funext ρ
      rfl
  | let₂ da db iha ihb =>
      rcases iha with ⟨F, dF, eF⟩
      rcases ihb with ⟨G, dG, eG⟩
      refine ⟨_, .let₂ dF dG, ?_⟩
      funext ρ
      have hF := congrFun eF ρ
      have hG (a) (b) := congrFun eG ((ρ, a), b)
      erw [bind_of]
      simp [Bind.kleisliRight, hF]
      exact bind_congr (m := m) (fun ab => hG _ _)
  | inl d ih =>
      rcases ih with ⟨F, dF, eF⟩
      refine ⟨_, .inl dF, ?_⟩
      funext ρ
      have hF := congrFun eF ρ
      simpa [ofTypeModel,
        joinM, bind_map_left] using hF
  | inr d ih =>
      rcases ih with ⟨F, dF, eF⟩
      refine ⟨_, .inr dF, ?_⟩
      funext ρ
      have hF := congrFun eF ρ
      simpa [ofTypeModel,
        joinM, bind_map_left] using hF
  | case de dl dr ihe ihl ihr =>
      rcases ihe with ⟨E, dE, eE⟩
      rcases ihl with ⟨L, dL, eL⟩
      rcases ihr with ⟨R, dR, eR⟩
      refine ⟨_, .case dE dL dR, ?_⟩
      funext ρ
      have hE := congrFun eE ρ
      have hL (a) := congrFun eL (ρ, a)
      have hR (b) := congrFun eR (ρ, b)
      erw [caseWithContext_of]
      simp [Bind.kleisliRight, joinM, bind_map_left, hE]
      apply bind_congr (m := m)
      intro e
      cases hcase : TypeModel.coprodEquiv _ _ e with
      | inl a =>
          generalize hs : (Types.binaryCoproductIso _ _).hom
            (((ofTypeModel (τ := τ)).coprodIso _ _).hom e) = s
          cases s with
          | inl x =>
              have hx : x = a := Sum.inl.inj
                (hs.symm.trans ((coprod_hom_agrees _ _ e).trans hcase))
              subst x
              exact hL a
          | inr y =>
              have contra := hs.symm.trans ((coprod_hom_agrees _ _ e).trans hcase)
              cases contra
      | inr b =>
          generalize hs : (Types.binaryCoproductIso _ _).hom
            (((ofTypeModel (τ := τ)).coprodIso _ _).hom e) = s
          cases s with
          | inl x =>
              have contra := hs.symm.trans ((coprod_hom_agrees _ _ e).trans hcase)
              cases contra
          | inr y =>
              have hy : y = b := Sum.inr.inj
                (hs.symm.trans ((coprod_hom_agrees _ _ e).trans hcase))
              subst y
              exact hR b
  | abort d ih =>
      rcases ih with ⟨F, dF, eF⟩
      refine ⟨_, .abort dF, ?_⟩
      funext ρ
      have hF := congrFun eF ρ
      unfold Categorical.abort
      erw [Kleisli.Type.comp_of_eq_kleisliRight]
      simp only [Bind.kleisliRight]
      refine congrArg₂ (fun (x : m _) (k : _ → m _) => x >>= k) hF ?_
      funext z
      exact Empty.elim (TypeModel.emptyEquiv z)

  | sub d coercion ih =>
      rcases ih with ⟨F, dF, eF⟩
      refine ⟨_, .sub dF coercion, ?_⟩
      funext ρ
      have hF := congrFun eF ρ
      simp [ofTypeModel, coeSub, joinM, bind_map_left]
      exact congrArg (fun x => TypeModel.coe coercion <$> x) hF

theorem denote_agrees_proof {Γ : VCtx τ} {t : Tm Φ} {A : τ}
    (h : Tm.HasType Γ t A) :
    (fun ρ => (categoricalTermDenote (ε := ε) (m := m) h).of (envToCategorical ρ)) =
      Monadic.denote (ε := ε) (m := m) h := by
  let := ofInstructionModel (τ := τ) (Φ := Φ) (ε := ε) (m := m)
  rcases denotes_toCategorical (Monadic.denote_spec (ε := ε) (m := m) h) with ⟨F, dF, hF⟩
  have hchosen := Categorical.Denotes.eq_denote (typeJ (m := m)) (ofTypeModel (τ := τ)) dF
  simpa only [categoricalTermDenote, hchosen] using hF

variable [Iterate m] [LawfulElgotMonad m]

/-- A direct monadic region witness induces a categorical witness in the
Kleisli/Freyd model with the same result on corresponding environments. -/
private theorem regionDenotes_toCategorical {Γ : VCtx τ} {region : Region Φ} {L : LCtx τ}
    {h : Region.HasType Γ region L}
    {f : Monadic.Env Γ → m (Monadic.LabelDen L)}
    (d : Monadic.RegionDenotes (m := m) ε h f) :
    let _ := ofInstructionModel
      (τ := τ) (Φ := Φ) (ε := ε) (m := m)
    ∃ F, Categorical.RegionDenotes (typeJ (m := m)) (ofTypeModel (τ := τ)) h F ∧
      (fun ρ => F.of (envToCategorical ρ)) =
        (fun ρ => f ρ >>= fun x => pure (LambdaSSA.Semantics.Monadic.LabelValue.categoricalEquiv L x)) := by
  dsimp
  let _ := ofInstructionModel
    (τ := τ) (Φ := Φ) (ε := ε) (m := m)
  induction d with
  | br dt =>
      rename_i Γ t A ht fa L i hi
      rcases denotes_toCategorical dt with ⟨F, dF, eF⟩
      refine ⟨_, Categorical.RegionDenotes.br (h := by assumption) dF, ?_⟩
      funext ρ
      erw [Kleisli.Type.comp_of_eq_kleisliRight]
      have hF := congrFun eF ρ
      simp only [Bind.kleisliRight, LambdaSSA.Semantics.Monadic.labelInject, bind_pure_comp, Functor.map_map]
      refine (congrArg (fun (x : m _) => x >>= _) hF).trans ?_
      let inject : TyDen A → LambdaSSA.Semantics.Monadic.CategoricalLabelDen L := fun a =>
        LambdaSSA.Semantics.Categorical.labelInject (LambdaSSA.Semantics.Categorical.ofMonadicTypeModel (τ := τ)) i hi a
      let equiv := LambdaSSA.Semantics.Monadic.LabelValue.categoricalEquiv L
      change (fa ρ >>= fun a => pure (inject a)) =
        (fun a => equiv (equiv.symm (inject a))) <$> fa ρ
      exact (bind_pure_comp (m := m) inject (fa ρ)).trans
        (congrArg (fun g : TyDen A → LambdaSSA.Semantics.Monadic.CategoricalLabelDen L => g <$> fa ρ)
          (funext fun a => (equiv.apply_symm_apply (inject a)).symm))
  | case de dl dr ihl ihr =>
      rcases denotes_toCategorical de with ⟨E, dE, eE⟩
      rcases ihl with ⟨FL, dFL, eFL⟩
      rcases ihr with ⟨FR, dFR, eFR⟩
      refine ⟨_, .case dE dFL dFR, ?_⟩
      funext ρ
      erw [caseWithContext_of]
      simp [Bind.kleisliRight, joinM, bind_map_left]
      refine congrArg₂ (fun (x : m _) (k : _ → m _) => x >>= k) (congrFun eE ρ) ?_
      funext e
      erw [coprod_hom_agrees]
      cases TypeModel.coprodEquiv _ _ e with
      | inl a =>
          have agreed := congrFun eFL (ρ, a)
          change (_ : m _) = _ at agreed
          rwa [bind_pure_comp] at agreed
      | inr b =>
          have agreed := congrFun eFR (ρ, b)
          change (_ : m _) = _ at agreed
          rwa [bind_pure_comp] at agreed
  | let₁ da db ihb =>
      rcases denotes_toCategorical da with ⟨F, dF, eF⟩
      rcases ihb with ⟨G, dG, eG⟩
      refine ⟨_, .let₁ dF dG, ?_⟩
      funext ρ
      erw [bind_of]
      simp only [Bind.kleisliRight, bind_assoc]
      exact congrArg₂ (fun (x : m _) (k : _ → m _) => x >>= k)
        (congrFun eF ρ) (funext fun a => congrFun eG (ρ, a))
  | let₂ da db ihb =>
      rename_i Γ t A B ha fa r L hb fb
      rcases denotes_toCategorical da with ⟨F, dF, eF⟩
      rcases ihb with ⟨G, dG, eG⟩
      refine ⟨_, .let₂ dF dG, ?_⟩
      funext ρ
      erw [bind_of]
      simp [Bind.kleisliRight]
      refine congrArg₂ (fun (x : m _) (k : _ → m _) => x >>= k) (congrFun eF ρ) ?_
      funext ab
      let values := TypeModel.productEquiv A B ab
      have agreed := congrFun eG ((ρ, values.1), values.2)
      change (_ : m _) = _ at agreed
      rwa [bind_pure_comp] at agreed
  | cfgZero he hb de ih =>
      rcases ih with ⟨F, dF, eF⟩
      exact ⟨F, .cfgZero dF, eF⟩
  | cfg he hb de db dc ihe ihb =>
      rcases ihe with ⟨FE, dFE, eFE⟩
      choose FB dFB eFB using ihb
      rename_i n R Γ L entry blocks fe fb collective
      let FC := collectiveArrow collective
      have dFC : LambdaSSA.Semantics.Categorical.CollectiveDenotes (typeJ (m := m)) (LambdaSSA.Semantics.Categorical.ofMonadicTypeModel (τ := τ))
          Γ R L FB FC := collective_toCategorical dc (fun i ρ => congrFun (eFB i) ρ)
      refine ⟨_, .cfg dFE dFB dFC, ?_⟩
      exact cfgDenotation_agrees (Γ := Γ) (R := R) (L := L) (fe := fe) (FE := FE) eFE collective

theorem denoteRegion_agrees_proof
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := m))
    {Γ : VCtx τ} {region : Region Φ} {L : LCtx τ}
    (h : Region.HasType Γ region L) (ρ : Monadic.Env Γ) :
    (categoricalRegionDenote (ε := ε) (m := m) h).of (envToCategorical ρ) =
      (Monadic.denoteRegion (ε := ε) (m := m) h ρ >>= fun x =>
        pure (LambdaSSA.Semantics.Monadic.LabelValue.categoricalEquiv L x)) := by
  let := ofInstructionModel (τ := τ) (Φ := Φ) (ε := ε) (m := m)
  let _ : Categorical.RegionTypingCoherent (Φ := Φ) (typeJ (m := m)) (ofTypeModel (τ := τ)) :=
    coherent
  rcases regionDenotes_toCategorical (Monadic.denoteRegion_spec (ε := ε) (m := m) h) with
    ⟨F, dF, hF⟩
  have hchosen := Categorical.RegionDenotes.eq_denote (typeJ (m := m)) (ofTypeModel (τ := τ)) dF
  simpa only [categoricalRegionDenote, hchosen] using congrFun hF ρ

end Agreement
end Silmaril.Isotope.LambdaSSA.Subtyping.Semantics
