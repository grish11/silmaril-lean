module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.TheoryStructure.Defs

public section

namespace Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.DerivationStructure

open Silmaril.Logic.TypeTheory.ExtensionalMLTT

theorem embedding_cons {Γ Δ : ECtx} (h : Γ.Embeds Δ) (x : String) (A : ETm 0) :
    (Γ.cons x A).Embeds (Δ.cons x A) := by
  intro y B hy
  cases hy with
  | here => exact .here _ _ _
  | there _ _ _ _ _ hy hne => exact .there _ _ _ _ _ (h hy) hne

theorem lookup_mem_dv {Γ : ECtx} {x : String} {A : ETm 0} (h : Γ.Lookup x A) : x ∈ Γ.dv := by
  induction h with
  | here => exact Finset.mem_insert_self _ _
  | there _ _ _ _ _ _ _ ih => exact Finset.mem_insert_of_mem ih

theorem embedding_fresh {Γ : ECtx} {x : String} (hx : x ∉ Γ.dv) (A : ETm 0) :
    Γ.Embeds (Γ.cons x A) := by
  intro y B hy
  apply ECtx.Lookup.there _ _ _ _ _ hy
  intro heq
  subst y
  exact hx (lookup_mem_dv hy)

theorem context {Γ : ECtx} {A a b : ETm 0} (h : ECtx.JEqH ∅ Γ A a b) :
    ECtx.JEqH ∅ Γ .unit .star .star := by
  induction h with
  | hyp h => exact False.elim h
  | nil_ok => exact .nil_ok
  | cons_ok hΓ hx hA _ _ => exact .cons_ok hΓ hx hA
  | var hΓ _ _ => exact hΓ
  | univ hΓ _ => exact hΓ
  | empty hΓ _ => exact hΓ
  | unit hΓ _ => exact hΓ
  | nats hΓ _ => exact hΓ
  | zero hΓ _ => exact hΓ
  | succ _ ih => exact ih
  | pi _ _ ihA _ => exact ihA
  | sigma _ _ ihA _ => exact ihA
  | id _ _ _ ihA _ _ => exact ihA
  | abs _ _ _ ihA _ _ => exact ihA
  | app _ _ _ _ ihA _ _ _ => exact ihA
  | pair _ _ _ _ ihA _ _ _ => exact ihA
  | fst _ _ _ ihA _ _ => exact ihA
  | snd _ _ _ ihA _ _ => exact ihA
  | natrec _ _ _ _ _ ihz _ _ => exact ihz
  | refl _ ih => exact ih
  | absurd _ _ ihA _ => exact ihA
  | beta_app _ _ _ _ ihA _ _ _ => exact ihA
  | beta_fst _ _ _ _ ihA _ _ _ => exact ihA
  | beta_snd _ _ _ _ ihA _ _ _ => exact ihA
  | beta_natrec_zero _ _ _ _ ihz _ => exact ihz
  | beta_natrec_succ _ _ _ _ _ ihz _ _ => exact ihz
  | reflect _ _ _ iha _ _ => exact iha
  | id_uip _ _ _ iha _ _ => exact iha
  | unit_ext _ ih => exact ih
  | pi_ext _ _ _ _ _ ihA _ _ _ _ => exact ihA
  | sigma_ext _ _ _ _ _ _ ihA _ _ _ _ _ => exact ihA
  | symm _ ih => exact ih
  | trans _ _ ih _ => exact ih
  | conv _ _ ihA _ => exact ihA
  | cumul _ _ ih => exact ih

private theorem family {K : Set EJdg} {n : ℕ} {Γ Δ : ECtx} {A : ETm 0} {L : Finset String}
    {B a b : String → ETm 0} (e : Γ.Embeds Δ)
    (hΔ : ECtx.JEqH K Δ .unit .star .star) (hA : ECtx.JEqH K Δ (.univ n) A A)
    (ih : ∀ x ∉ L, ∀ {Ξ}, ECtx.JEqH K Ξ .unit .star .star → (Γ.cons x A).Embeds Ξ →
      ECtx.JEqH K Ξ (B x) (a x) (b x)) :
    ∀ x ∉ L ∪ Δ.dv, ECtx.JEqH K (Δ.cons x A) (B x) (a x) (b x) := by
  intro x hx
  have hs : x ∉ L ∧ x ∉ Δ.dv := Finset.notMem_union.mp hx
  exact ih x hs.1 (.cons_ok hΔ hs.2 hA) (embedding_cons e x A)

theorem weaken_of_hypotheses {H K : Set EJdg} {Γ : ECtx} {A a b : ETm 0}
    (h : ECtx.JEqH H Γ A a b) (hh : HypothesisTransport H K)
    {Δ : ECtx} (hΔ : ECtx.JEqH K Δ .unit .star .star) (hΓΔ : Γ.Embeds Δ) :
    ECtx.JEqH K Δ A a b := by
  induction h generalizing Δ with
  | hyp h => exact hh h hΓΔ hΔ
  | nil_ok => exact hΔ
  | cons_ok _ _ _ _ _ => exact hΔ
  | var _ hx _ => exact .var hΔ (hΓΔ hx)
  | univ _ _ => exact .univ hΔ
  | empty _ _ => exact .empty hΔ
  | unit _ _ => exact .unit hΔ
  | nats _ _ => exact .nats hΔ
  | zero _ _ => exact .zero hΔ
  | succ _ ih => exact .succ (ih hΔ hΓΔ)
  | @pi Γ n A A' B B' L hA hB ihA ihB =>
    have hA' : ECtx.JEqH K Δ (.univ n) A A' := ihA hΔ hΓΔ
    exact .pi hA' (family hΓΔ hΔ (.trans hA' (.symm hA')) ihB)
  | @sigma Γ n A A' B B' L hA hB ihA ihB =>
    have hA' : ECtx.JEqH K Δ (.univ n) A A' := ihA hΔ hΓΔ
    exact .sigma hA' (family hΓΔ hΔ (.trans hA' (.symm hA')) ihB)
  | id _ _ _ ihA iha ihb => exact .id (ihA hΔ hΓΔ) (iha hΔ hΓΔ) (ihb hΔ hΓΔ)
  | @abs Γ n A A' B b b' L hA hB hb ihA ihB ihb =>
    have hA' : ECtx.JEqH K Δ (.univ n) A A' := ihA hΔ hΓΔ
    exact .abs hA' (family hΓΔ hΔ (.trans hA' (.symm hA')) ihB)
      (family hΓΔ hΔ (.trans hA' (.symm hA')) ihb)
  | @app Γ n A f f' a a' B L hA hB hf ha ihA ihB ihf iha =>
    have hA' : ECtx.JEqH K Δ (.univ n) A A := ihA hΔ hΓΔ
    exact .app hA' (family hΓΔ hΔ hA' ihB) (ihf hΔ hΓΔ) (iha hΔ hΓΔ)
  | @pair Γ n A a a' b b' B L hA hB ha hb ihA ihB iha ihb =>
    have hA' : ECtx.JEqH K Δ (.univ n) A A := ihA hΔ hΓΔ
    exact .pair hA' (family hΓΔ hΔ hA' ihB) (iha hΔ hΓΔ) (ihb hΔ hΓΔ)
  | @fst Γ n A p p' B L hA hB hp ihA ihB ihp =>
    have hA' : ECtx.JEqH K Δ (.univ n) A A := ihA hΔ hΓΔ
    exact .fst hA' (family hΓΔ hΔ hA' ihB) (ihp hΔ hΓΔ)
  | @snd Γ n A p p' B L hA hB hp ihA ihB ihp =>
    have hA' : ECtx.JEqH K Δ (.univ n) A A := ihA hΔ hΓΔ
    exact .snd hA' (family hΓΔ hΔ hA' ihB) (ihp hΔ hΓΔ)
  | @natrec Γ n C C' s s' z z' m m' L hC hz hs hm ihC ihz ihs ihm =>
    exact .natrec (n := n) (family hΓΔ hΔ (.nats (n := 0) hΔ) ihC) (ihz hΔ hΓΔ)
      (family hΓΔ hΔ (.nats (n := 0) hΔ) ihs) (ihm hΔ hΓΔ)
  | refl _ iha => exact .refl (iha hΔ hΓΔ)
  | absurd _ _ ihA ihe => exact .absurd (ihA hΔ hΓΔ) (ihe hΔ hΓΔ)
  | @beta_app Γ n A a B b L hA hB hb ha ihA ihB ihb iha =>
    have hA' : ECtx.JEqH K Δ (.univ n) A A := ihA hΔ hΓΔ
    exact .beta_app hA' (family hΓΔ hΔ hA' ihB) (family hΓΔ hΔ hA' ihb) (iha hΔ hΓΔ)
  | @beta_fst Γ n A a b B L hA hB ha hb ihA ihB iha ihb =>
    have hA' : ECtx.JEqH K Δ (.univ n) A A := ihA hΔ hΓΔ
    exact .beta_fst hA' (family hΓΔ hΔ hA' ihB) (iha hΔ hΓΔ) (ihb hΔ hΓΔ)
  | @beta_snd Γ n A a b B L hA hB ha hb ihA ihB iha ihb =>
    have hA' : ECtx.JEqH K Δ (.univ n) A A := ihA hΔ hΓΔ
    exact .beta_snd hA' (family hΓΔ hΔ hA' ihB) (iha hΔ hΓΔ) (ihb hΔ hΓΔ)
  | @beta_natrec_zero Γ n C s z L hC hz hs ihC ihz ihs =>
    exact .beta_natrec_zero (n := n) (family hΓΔ hΔ (.nats (n := 0) hΔ) ihC) (ihz hΔ hΓΔ)
      (family hΓΔ hΔ (.nats (n := 0) hΔ) ihs)
  | @beta_natrec_succ Γ n C s z m L hC hz hs hm ihC ihz ihs ihm =>
    exact .beta_natrec_succ (n := n) (family hΓΔ hΔ (.nats (n := 0) hΔ) ihC) (ihz hΔ hΓΔ)
      (family hΓΔ hΔ (.nats (n := 0) hΔ) ihs) (ihm hΔ hΓΔ)
  | reflect _ _ _ iha ihb ihp => exact .reflect (iha hΔ hΓΔ) (ihb hΔ hΓΔ) (ihp hΔ hΓΔ)
  | id_uip _ _ _ iha ihb ihp => exact .id_uip (iha hΔ hΓΔ) (ihb hΔ hΓΔ) (ihp hΔ hΓΔ)
  | unit_ext _ iha => exact .unit_ext (iha hΔ hΓΔ)
  | @pi_ext Γ n A f g B L hA hB hf hg hfg ihA ihB ihf ihg ihfg =>
    have hA' : ECtx.JEqH K Δ (.univ n) A A := ihA hΔ hΓΔ
    exact .pi_ext hA' (family hΓΔ hΔ hA' ihB) (ihf hΔ hΓΔ) (ihg hΔ hΓΔ)
      (family hΓΔ hΔ hA' ihfg)
  | @sigma_ext Γ n A p q B L hA hB hp hq h1 h2 ihA ihB ihp ihq ih1 ih2 =>
    have hA' : ECtx.JEqH K Δ (.univ n) A A := ihA hΔ hΓΔ
    exact .sigma_ext hA' (family hΓΔ hΔ hA' ihB) (ihp hΔ hΓΔ) (ihq hΔ hΓΔ)
      (ih1 hΔ hΓΔ) (ih2 hΔ hΓΔ)
  | symm _ ih => exact .symm (ih hΔ hΓΔ)
  | trans _ _ ih ik => exact .trans (ih hΔ hΓΔ) (ik hΔ hΓΔ)
  | conv _ _ ihA iha => exact .conv (ihA hΔ hΓΔ) (iha hΔ hΓΔ)
  | cumul hmn _ ihA => exact .cumul hmn (ihA hΔ hΓΔ)

/-- The existing closed interface specializes the general leaf-transport proof. -/
theorem weaken {Γ : ECtx} {A a b : ETm 0} (h : ECtx.JEqH ∅ Γ A a b)
    {Δ : ECtx} (hΔ : ECtx.JEqH ∅ Δ .unit .star .star) (hΓΔ : Γ.Embeds Δ) :
    ECtx.JEqH ∅ Δ A a b :=
  weaken_of_hypotheses h (fun h => False.elim h) hΔ hΓΔ

end Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.DerivationStructure
