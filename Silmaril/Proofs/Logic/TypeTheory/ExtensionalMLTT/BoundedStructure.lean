module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Finite.Derivation.Thms
public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.DerivationStructure

public section

namespace Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.BoundedStructure

open Silmaril.Logic.TypeTheory.ExtensionalMLTT

theorem context {levels : ℕ} {Γ : ECtx} {A a b : ETm 0}
    (h : ECtx.JEqB levels ∅ Γ A a b) : ECtx.JEqB levels ∅ Γ .unit .star .star := by
  induction h
  case hyp Γ A a b hj => cases hj
  case nil_ok => exact .nil_ok
  case cons_ok Γ x A n hn hΓ hx hA ihΓ ihA => exact .cons_ok hn hΓ hx hA
  all_goals assumption

private theorem family {levels n : ℕ} {Γ Δ : ECtx} {A : ETm 0} {L : Finset String}
    {B a b : String → ETm 0} (hn : n < levels) (e : Γ.Embeds Δ)
    (hΔ : ECtx.JEqB levels ∅ Δ .unit .star .star) (hA : ECtx.JEqB levels ∅ Δ (.univ n) A A)
    (ih : ∀ x ∉ L, ∀ {Ξ}, ECtx.JEqB levels ∅ Ξ .unit .star .star → (Γ.cons x A).Embeds Ξ →
      ECtx.JEqB levels ∅ Ξ (B x) (a x) (b x)) :
    ∀ x ∉ L ∪ Δ.dv, ECtx.JEqB levels ∅ (Δ.cons x A) (B x) (a x) (b x) := by
  intro x hx
  have hs : x ∉ L ∧ x ∉ Δ.dv := Finset.notMem_union.mp hx
  exact ih x hs.1 (.cons_ok hn hΔ hs.2 hA) (ECtx.Embeds.cons e x A)

theorem weaken {levels : ℕ} {Γ : ECtx} {A a b : ETm 0} (h : ECtx.JEqB levels ∅ Γ A a b)
    {Δ : ECtx} (hΔ : ECtx.JEqB levels ∅ Δ .unit .star .star) (hΓΔ : Γ.Embeds Δ) :
    ECtx.JEqB levels ∅ Δ A a b := by
  induction h generalizing Δ with
  | hyp h => exact False.elim h
  | nil_ok => exact hΔ
  | cons_ok _ _ _ _ _ _ => exact hΔ
  | var _ hx _ => exact .var hΔ (hΓΔ hx)
  | univ hn _ _ => exact .univ hn hΔ
  | empty hn _ _ => exact .empty hn hΔ
  | unit hn _ _ => exact .unit hn hΔ
  | nats hn _ _ => exact .nats hn hΔ
  | zero _ _ => exact .zero hΔ
  | succ _ ih => exact .succ (ih hΔ hΓΔ)
  | @pi Γ n hn A A' B B' L hA hB ihA ihB =>
    have hA' : ECtx.JEqB levels ∅ Δ (.univ n) A A' := ihA hΔ hΓΔ
    exact .pi hn hA' (family hn hΓΔ hΔ (.trans hA' (.symm hA')) ihB)
  | @sigma Γ n hn A A' B B' L hA hB ihA ihB =>
    have hA' : ECtx.JEqB levels ∅ Δ (.univ n) A A' := ihA hΔ hΓΔ
    exact .sigma hn hA' (family hn hΓΔ hΔ (.trans hA' (.symm hA')) ihB)
  | id hn _ _ _ ihA iha ihb => exact .id hn (ihA hΔ hΓΔ) (iha hΔ hΓΔ) (ihb hΔ hΓΔ)
  | @abs Γ n hn A A' B b b' L hA hB hb ihA ihB ihb =>
    have hA' : ECtx.JEqB levels ∅ Δ (.univ n) A A' := ihA hΔ hΓΔ
    exact .abs hn hA' (family hn hΓΔ hΔ (.trans hA' (.symm hA')) ihB)
      (family hn hΓΔ hΔ (.trans hA' (.symm hA')) ihb)
  | @app Γ n hn A f f' a a' B L hA hB hf ha ihA ihB ihf iha =>
    have hA' : ECtx.JEqB levels ∅ Δ (.univ n) A A := ihA hΔ hΓΔ
    exact .app hn hA' (family hn hΓΔ hΔ hA' ihB) (ihf hΔ hΓΔ) (iha hΔ hΓΔ)
  | @pair Γ n hn A a a' b b' B L hA hB ha hb ihA ihB iha ihb =>
    have hA' : ECtx.JEqB levels ∅ Δ (.univ n) A A := ihA hΔ hΓΔ
    exact .pair hn hA' (family hn hΓΔ hΔ hA' ihB) (iha hΔ hΓΔ) (ihb hΔ hΓΔ)
  | @fst Γ n hn A p p' B L hA hB hp ihA ihB ihp =>
    have hA' : ECtx.JEqB levels ∅ Δ (.univ n) A A := ihA hΔ hΓΔ
    exact .fst hn hA' (family hn hΓΔ hΔ hA' ihB) (ihp hΔ hΓΔ)
  | @snd Γ n hn A p p' B L hA hB hp ihA ihB ihp =>
    have hA' : ECtx.JEqB levels ∅ Δ (.univ n) A A := ihA hΔ hΓΔ
    exact .snd hn hA' (family hn hΓΔ hΔ hA' ihB) (ihp hΔ hΓΔ)
  | @natrec Γ n hn C C' s s' z z' m m' L hC hz hs hm ihC ihz ihs ihm =>
    exact .natrec (n := n) hn (family (by omega) hΓΔ hΔ (.nats (n := 0) (by omega) hΔ) ihC) (ihz hΔ hΓΔ)
      (family (by omega) hΓΔ hΔ (.nats (n := 0) (by omega) hΔ) ihs) (ihm hΔ hΓΔ)
  | refl _ iha => exact .refl (iha hΔ hΓΔ)
  | absurd hn _ _ ihA ihe => exact .absurd hn (ihA hΔ hΓΔ) (ihe hΔ hΓΔ)
  | @beta_app Γ n hn A a B b L hA hB hb ha ihA ihB ihb iha =>
    have hA' : ECtx.JEqB levels ∅ Δ (.univ n) A A := ihA hΔ hΓΔ
    exact .beta_app hn hA' (family hn hΓΔ hΔ hA' ihB) (family hn hΓΔ hΔ hA' ihb) (iha hΔ hΓΔ)
  | @beta_fst Γ n hn A a b B L hA hB ha hb ihA ihB iha ihb =>
    have hA' : ECtx.JEqB levels ∅ Δ (.univ n) A A := ihA hΔ hΓΔ
    exact .beta_fst hn hA' (family hn hΓΔ hΔ hA' ihB) (iha hΔ hΓΔ) (ihb hΔ hΓΔ)
  | @beta_snd Γ n hn A a b B L hA hB ha hb ihA ihB iha ihb =>
    have hA' : ECtx.JEqB levels ∅ Δ (.univ n) A A := ihA hΔ hΓΔ
    exact .beta_snd hn hA' (family hn hΓΔ hΔ hA' ihB) (iha hΔ hΓΔ) (ihb hΔ hΓΔ)
  | @beta_natrec_zero Γ n hn C s z L hC hz hs ihC ihz ihs =>
    exact .beta_natrec_zero (n := n) hn (family (by omega) hΓΔ hΔ (.nats (n := 0) (by omega) hΔ) ihC) (ihz hΔ hΓΔ)
      (family (by omega) hΓΔ hΔ (.nats (n := 0) (by omega) hΔ) ihs)
  | @beta_natrec_succ Γ n hn C s z m L hC hz hs hm ihC ihz ihs ihm =>
    exact .beta_natrec_succ (n := n) hn (family (by omega) hΓΔ hΔ (.nats (n := 0) (by omega) hΔ) ihC) (ihz hΔ hΓΔ)
      (family (by omega) hΓΔ hΔ (.nats (n := 0) (by omega) hΔ) ihs) (ihm hΔ hΓΔ)
  | reflect _ _ _ iha ihb ihp => exact .reflect (iha hΔ hΓΔ) (ihb hΔ hΓΔ) (ihp hΔ hΓΔ)
  | id_uip _ _ _ iha ihb ihp => exact .id_uip (iha hΔ hΓΔ) (ihb hΔ hΓΔ) (ihp hΔ hΓΔ)
  | unit_ext _ iha => exact .unit_ext (iha hΔ hΓΔ)
  | @pi_ext Γ n hn A f g B L hA hB hf hg hfg ihA ihB ihf ihg ihfg =>
    have hA' : ECtx.JEqB levels ∅ Δ (.univ n) A A := ihA hΔ hΓΔ
    exact .pi_ext hn hA' (family hn hΓΔ hΔ hA' ihB) (ihf hΔ hΓΔ) (ihg hΔ hΓΔ)
      (family hn hΓΔ hΔ hA' ihfg)
  | @sigma_ext Γ n hn A p q B L hA hB hp hq h1 h2 ihA ihB ihp ihq ih1 ih2 =>
    have hA' : ECtx.JEqB levels ∅ Δ (.univ n) A A := ihA hΔ hΓΔ
    exact .sigma_ext hn hA' (family hn hΓΔ hΔ hA' ihB) (ihp hΔ hΓΔ) (ihq hΔ hΓΔ)
      (ih1 hΔ hΓΔ) (ih2 hΔ hΓΔ)
  | symm _ ih => exact .symm (ih hΔ hΓΔ)
  | trans _ _ ih ik => exact .trans (ih hΔ hΓΔ) (ik hΔ hΓΔ)
  | conv hn _ _ ihA iha => exact .conv hn (ihA hΔ hΓΔ) (iha hΔ hΓΔ)
  | cumul hn hmn _ ihA => exact .cumul hn hmn (ihA hΔ hΓΔ)

end Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.BoundedStructure
