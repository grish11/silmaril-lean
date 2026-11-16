module

public import Silmaril.Logic.TypeTheory.LambdaPi.Eta.Defs

@[expose] public section

namespace Silmaril.Proofs.Logic.TypeTheory.LambdaPi

open Silmaril.Logic.TypeTheory.LambdaPi Silmaril.Calculi.LambdaCube

theorem eta_rule_left (σ : ℕ → Term) :
    etaRule.lhs.subst σ = .lam (σ 0) (.app ((σ 1).rename Nat.succ) (.var 0)) := rfl

theorem eta_rule_right (σ : ℕ → Term) : etaRule.rhs.subst σ = σ 1 := rfl

theorem eta_step (C : Calculus) (A f : Term) :
    C.withEta.Conversion (.lam A (.app (f.rename Nat.succ) (.var 0))) f := by
  let σ : ℕ → Term := fun | 0 => A | _ + 1 => f
  have hr : etaRule ∈ C.withEta.rules := Set.mem_union_right C.rules (Set.mem_singleton _)
  exact Calculus.Conversion.rewrite etaRule hr σ

theorem beta_eta_of_profile (declared : String → Term → Prop) {t u : Term}
    (h : (Calculus.lfBetaEta declared).Conversion t u) : BetaEtaConversion t u := by
  induction h with
  | refl _ => exact .refl _
  | symm _ ih => exact .symm ih
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  | beta _ _ _ => exact .beta _ _ _
  | rewrite r hr σ =>
    have he : r = etaRule := by
      rcases hr with h | h
      · exact (Set.notMem_empty r h).elim
      · exact Set.mem_singleton_iff.mp h
    subst r
    exact .eta (σ 0) (σ 1)
  | app _ _ ihf iha => exact .app ihf iha
  | lam _ _ ihA ihb => exact .lam ihA ihb
  | pi _ _ ihA ihB => exact .pi ihA ihB

theorem profile_of_beta_eta (declared : String → Term → Prop) {t u : Term}
    (h : BetaEtaConversion t u) : (Calculus.lfBetaEta declared).Conversion t u := by
  induction h with
  | refl _ => exact .refl _
  | symm _ ih => exact .symm ih
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  | beta _ _ _ => exact .beta _ _ _
  | eta A f => exact eta_step _ A f
  | app _ _ ihf iha => exact .app ihf iha
  | lam _ _ ihA ihb => exact .lam ihA ihb
  | pi _ _ ihA ihB => exact .pi ihA ihB

theorem eta_map_rule (f : String → String) : etaRule.mapConstants f = etaRule := rfl

theorem eta_assignment_rule (F : ConstantAssignment) :
    F.term etaRule.lhs = etaRule.lhs ∧ F.term etaRule.rhs = etaRule.rhs := ⟨rfl, rfl⟩

end Silmaril.Proofs.Logic.TypeTheory.LambdaPi
