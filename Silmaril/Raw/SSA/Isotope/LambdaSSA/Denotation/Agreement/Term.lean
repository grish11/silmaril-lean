module

public import Silmaril.Raw.SSA.Isotope.LambdaSSA.Denotation.Monadic.Term
public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Thms

@[expose] public section

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.dsimp.instances true

namespace Silmaril.Isotope.LambdaSSA.Semantics

open CategoryTheory CategoryTheory.Limits Silmaril.Elgot
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical
  (typeJ bind_of pair_of caseWithContext_of comp_map_of contextualLoop_of)

universe u v q r

namespace Agreement

variable {τ : Type u} [TypeFormers τ] [Subtyping τ] [TypeModel.{u, v} τ]
variable {Φ : Type q} [HasTy Φ τ]
variable {ε : Type r} [HasEff Φ ε] [Bot ε]
variable {m : Type v → Type v} [Monad m] [LawfulMonad m]
variable [InstructionModel Φ τ ε m]

private theorem tensor_inv_agrees (A B : τ) (p : TyDen A × TyDen B) :
    ((Categorical.ofMonadicTypeModel (τ := τ)).productIso A B).inv p =
      (TypeModel.productEquiv A B).symm p := rfl

private theorem coprod_inv_inl_agrees (A B : τ) (a : TyDen A) :
    ((Categorical.ofMonadicTypeModel (τ := τ)).coprodIso A B).inv
      ((Types.binaryCoproductIso (TyDen A) (TyDen B)).inv (.inl a)) =
      (TypeModel.coprodEquiv A B).symm (.inl a) := by
  change (((Equiv.toIso (TypeModel.coprodEquiv A B)).trans
    (Types.binaryCoproductIso _ _).symm).inv
      ((Types.binaryCoproductIso _ _).inv (.inl a))) = _
  simp

private theorem coprod_inv_inr_agrees (A B : τ) (b : TyDen B) :
    ((Categorical.ofMonadicTypeModel (τ := τ)).coprodIso A B).inv
      ((Types.binaryCoproductIso (TyDen A) (TyDen B)).inv (.inr b)) =
      (TypeModel.coprodEquiv A B).symm (.inr b) := by
  change (((Equiv.toIso (TypeModel.coprodEquiv A B)).trans
    (Types.binaryCoproductIso _ _).symm).inv
      ((Types.binaryCoproductIso _ _).inv (.inr b))) = _
  simp

theorem coprod_hom_agrees (A B : τ) (e : TyDen (Silmaril.coprod A B)) :
    (Types.binaryCoproductIso ((Categorical.ofMonadicTypeModel (τ := τ)).obj A) ((Categorical.ofMonadicTypeModel (τ := τ)).obj B)).hom
      (((Categorical.ofMonadicTypeModel (τ := τ)).coprodIso A B).hom e) =
        TypeModel.coprodEquiv A B e := by
  change (Types.binaryCoproductIso _ _).hom
    (((Equiv.toIso (TypeModel.coprodEquiv A B)).trans
      (Types.binaryCoproductIso _ _).symm).hom e) = _
  simp

/-- The explicit identification between direct monadic environments and the
newest-first categorical interpretation of SSA contexts. -/
def envToCategorical : {Γ : VCtx τ} →
    Monadic.Env Γ → Categorical.ctxObj (Categorical.ofMonadicTypeModel (τ := τ)) Γ
  | [], ρ => ρ
  | _ :: _, ρ => (envToCategorical ρ.1, ρ.2)

private theorem envPair_agrees {Γ : VCtx τ} {A B : τ} (ρ : Monadic.Env Γ)
    (ab : TyDen (Silmaril.product A B)) :
    (Categorical.ctxPairIso (Categorical.ofMonadicTypeModel (τ := τ)) Γ A B).hom
      (envToCategorical ρ, ((Categorical.ofMonadicTypeModel (τ := τ)).productIso A B).hom ab) =
    let p := TypeModel.productEquiv A B ab
    envToCategorical (Γ := B :: A :: Γ) ((ρ, p.1), p.2) := by rfl

theorem lookup_agrees {Γ : VCtx τ} {A : τ} (i : Nat) (h : At Γ i A)
    (ρ : Monadic.Env Γ) :
    ((typeJ (m := m)).map (Categorical.lookup (Categorical.ofMonadicTypeModel (τ := τ)) i h)).of
        (envToCategorical ρ) = (pure (Monadic.Env.get ρ i h) : m _) := by
  induction Γ generalizing i with
  | nil => simp [At] at h
  | cons B Γ ih =>
      cases i with
      | zero =>
          simp [At] at h
          subst A
          rfl
      | succ i =>
          exact ih i h ρ.1

/-- Every witness of the direct monadic graph induces a witness of the
categorical graph specialized to the Kleisli/Freyd model, with pointwise equal
underlying functions.  No proof-irrelevance or typing-coherence assumption is
used. -/
theorem denotes_toCategorical {Γ : VCtx τ} {t : Tm Φ} {A : τ}
    {h : Tm.HasType Γ t A} {f : Monadic.Env Γ → m (TyDen A)}
    (d : Monadic.Denotes (m := m) ε h f) :
    let _ := Categorical.ofMonadicInstructionModel
      (τ := τ) (Φ := Φ) (ε := ε) (m := m)
    ∃ F, Categorical.Denotes (typeJ (m := m)) (Categorical.ofMonadicTypeModel (τ := τ)) h F ∧
      (fun ρ => F.of (envToCategorical ρ)) = f := by
  dsimp
  let _ := Categorical.ofMonadicInstructionModel
    (τ := τ) (Φ := Φ) (ε := ε) (m := m)
  induction d with
  | var h =>
      exact ⟨_, .var h, funext (lookup_agrees _ h)⟩
  | op d ih =>
      rcases ih with ⟨F, dF, eF⟩
      refine ⟨_, .op dF, ?_⟩
      funext ρ
      have hF := congrFun eF ρ
      simp [Categorical.ofMonadicInstructionModel, joinM, bind_map_left, hF]
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
      simp [Categorical.ofMonadicTypeModel, joinM, bind_map_left, hF]
      apply congrArg (fun k => k <$> _)
      funext a
      change ((Categorical.ofMonadicTypeModel (τ := τ)).coprodIso _ _).inv
        ((Types.binaryCoproductIso _ _).inv (.inl a)) = _
      exact coprod_inv_inl_agrees _ _ a
  | inr d ih =>
      rcases ih with ⟨F, dF, eF⟩
      refine ⟨_, .inr dF, ?_⟩
      funext ρ
      have hF := congrFun eF ρ
      simp [Categorical.ofMonadicTypeModel, joinM, bind_map_left, hF]
      apply congrArg (fun k => k <$> _)
      funext b
      change ((Categorical.ofMonadicTypeModel (τ := τ)).coprodIso _ _).inv
        ((Types.binaryCoproductIso _ _).inv (.inr b)) = _
      exact coprod_inv_inr_agrees _ _ b
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
            (((Categorical.ofMonadicTypeModel (τ := τ)).coprodIso _ _).hom e) = s
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
            (((Categorical.ofMonadicTypeModel (τ := τ)).coprodIso _ _).hom e) = s
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
      simp [Categorical.ofMonadicTypeModel, joinM, bind_map_left, hF]
      apply bind_congr
      intro z
      exact Empty.elim (TypeModel.emptyEquiv z)

end Agreement
end Silmaril.Isotope.LambdaSSA.Semantics
