module

public import Silmaril.SSA.Isotope.LetParIter.Interpretation.Defs
public import Silmaril.SSA.Isotope.LetParIter.Semantics.Thms
public import Silmaril.Semantics.Elgot.Parallel.Thms

public section

namespace Silmaril.Isotope.LetParIter.Proofs

open Parallel LetIter.ProofRelevant.Semantics

universe u v w q r

variable {τ : Type u} [TypeFormers τ] [Subtyping τ] [TypeModel.{u, v} τ]
variable {ν : Type w} [DecidableEq ν] {Φ : Type q} [HasTy Φ τ]
variable {ε : Type r} [HasEff Φ ε] [Bot ε]
variable {m : Type v → Type v} [Monad m] [Elgot.Iterate m] [InstructionModel Φ τ ε m]
variable (P : Elgot.ParallelPairing m)
variable {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n} {a : Tm ν Φ n} {A : τ}

set_option backward.isDefEq.respectTransparency false in
theorem denote_embed {t : LetIter.LocallyNameless.Tm ν Φ n}
    (d : LetIter.LocallyNameless.Derivation Φ Γ β t A) (γ : CtxDen Γ) (ρ : BoundDen β) :
    LetParIter.denote (ε := ε) P (derivation d) γ ρ =
      LetIter.ProofRelevant.Semantics.denote (ε := ε) (nativeTyping d) γ ρ := by
  induction d with
  | fv | bv | unit =>
      simp only [derivation, nativeTyping, LetParIter.denote, LetIter.ProofRelevant.Semantics.denote]
  | op _ ih | inl _ ih | inr _ ih =>
      simp only [derivation, nativeTyping, LetParIter.denote,
        LetIter.ProofRelevant.Semantics.denote, denoteInstr, ih]
  | abort _ ih =>
      simp only [derivation, nativeTyping, LetParIter.denote,
        LetIter.ProofRelevant.Semantics.denote, ih]
      rfl
  | let₁ _ _ iha ihb | pair _ _ iha ihb | let₂ _ _ iha ihb =>
      simp only [derivation, nativeTyping, LetParIter.denote,
        LetIter.ProofRelevant.Semantics.denote, iha, ihb]
  | case _ _ _ ihe ihl ihr =>
      simp only [derivation, nativeTyping, LetParIter.denote,
        LetIter.ProofRelevant.Semantics.denote, ihe, ihl, ihr]
      rfl
  | iter ha hb iha ihb =>
      rw [derivation, nativeTyping, denote_letIter_iter]
      simp only [LetParIter.denote, iha, ihb]

variable [LawfulMonad m]

theorem denote_pure (d : Derivation Φ Γ β a A) (hp : Pure (⊥ : ε) a)
    (γ : CtxDen Γ) (ρ : BoundDen β) :
    ∃ x : TyDen A, LetParIter.denote (ε := ε) P d γ ρ = pure x := by
  induction d with
  | fv h => exact ⟨CtxDen.lookup γ _ h, by rw [LetParIter.denote]⟩
  | bv => exact ⟨BoundDen.get ρ _, by rw [LetParIter.denote]⟩
  | unit => exact ⟨TypeModel.unitEquiv.symm (), by rw [LetParIter.denote]⟩
  | op da ih =>
      cases hp with
      | op hf hpa =>
          obtain ⟨a, ha⟩ := ih hpa ρ
          refine ⟨denotePureInstr (m := m) _ hf a, ?_⟩
          rw [LetParIter.denote, ha, pure_bind]
          exact InstructionModel.denote_pure _ _ _
  | let₁ da db iha ihb =>
      cases hp with
      | let₁ hpa hpb =>
          obtain ⟨a, ha⟩ := iha hpa ρ
          obtain ⟨b, hb⟩ := ihb hpb (ρ, a)
          exact ⟨b, by simp only [LetParIter.denote, ha, hb, pure_bind]⟩
  | pair da db iha ihb =>
      cases hp with
      | pair hpa hpb =>
          obtain ⟨a, ha⟩ := iha hpa ρ
          obtain ⟨b, hb⟩ := ihb hpb ρ
          exact ⟨(TypeModel.productEquiv _ _).symm (a, b),
            by simp only [LetParIter.denote, ha, hb, pure_bind]⟩
  | let₂ da db iha ihb =>
      cases hp with
      | let₂ hpa hpb =>
          obtain ⟨a, ha⟩ := iha hpa ρ
          let p := TypeModel.productEquiv _ _ a
          obtain ⟨b, hb⟩ := ihb hpb ((ρ, p.1), p.2)
          refine ⟨b, ?_⟩
          rw [LetParIter.denote, ha, pure_bind]
          exact hb
  | inl da ih =>
      cases hp with
      | inl hpa =>
          obtain ⟨a, ha⟩ := ih hpa ρ
          exact ⟨(TypeModel.coprodEquiv _ _).symm (.inl a),
            by simp only [LetParIter.denote, ha, pure_bind]⟩
  | inr db ih =>
      cases hp with
      | inr hpb =>
          obtain ⟨b, hb⟩ := ih hpb ρ
          exact ⟨(TypeModel.coprodEquiv _ _).symm (.inr b),
            by simp only [LetParIter.denote, hb, pure_bind]⟩
  | case de dl dr ihe ihl ihr =>
      cases hp with
      | case hpe hpl hpr =>
          obtain ⟨e, he⟩ := ihe hpe ρ
          rw [LetParIter.denote, he, pure_bind]
          cases h : TypeModel.coprodEquiv _ _ e with
          | inl a => simpa only [h] using ihl hpl (ρ, a)
          | inr b => simpa only [h] using ihr hpr (ρ, b)
  | abort da ih =>
      cases hp with
      | abort hpa =>
          obtain ⟨z, _⟩ := ih hpa ρ
          exact Empty.elim (TypeModel.emptyEquiv z)
  | iter => cases hp
  | par da db iha ihb =>
      cases hp with
      | par hpa hpb =>
          obtain ⟨a, ha⟩ := iha hpa ρ
          obtain ⟨b, hb⟩ := ihb hpb ρ
          exact ⟨(TypeModel.productEquiv _ _).symm (a, b),
            by simp only [LetParIter.denote, evalPar, ha, hb, P.pure_pair, map_pure]⟩

end Silmaril.Isotope.LetParIter.Proofs
