module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Derivability.Weakening.Defs

@[expose] public section

namespace Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W

open Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W

theorem lookupLE_cons {Γ Δ : Ctx} (e : Γ.LookupLE Δ) (x : String) (A : Tm 0) :
    (Γ.cons x A).LookupLE (Δ.cons x A) := by
  intro y B h
  cases h with
  | here => exact .here Δ x A
  | there _ _ _ _ _ h hy => exact .there _ _ _ _ _ (e h) hy

theorem lookup_mem_dv {Γ : Ctx} {x : String} {A : Tm 0} (h : Γ.Lookup x A) : x ∈ Γ.dv := by
  induction h with
  | here => exact Finset.mem_insert_self _ _
  | there _ _ _ _ _ h hxy ih => exact Finset.mem_insert_of_mem ih

theorem lookupLE_fresh {Γ : Ctx} {x : String} (hx : x ∉ Γ.dv) (A : Tm 0) :
    Γ.LookupLE (Γ.cons x A) := by
  intro y B hy
  apply Ctx.Lookup.there _ _ _ _ _ hy
  intro heq
  subst y
  exact hx (lookup_mem_dv hy)

private theorem self {levels : RuleBudget} {H : Set Jdg} {Γ : Ctx} {A a b : Tm 0}
    (h : Γ.JEqB levels H A a b) : Γ.JEqB levels H A a a := .trans h h.symm

private theorem family {levels : RuleBudget} {n : ℕ} {H : Set Jdg} {Γ Δ : Ctx} {A : Tm 0} {L : Finset String}
    {B a b : String → Tm 0} (e : Γ.LookupLE Δ)
    (hΔ : Δ.JEqB levels H .unit .star .star) (hn : RuleBudget.Allows levels n)
    (hA : Δ.JEqB levels H (.univ n) A A)
    (ih : ∀ x ∉ L, ∀ Ξ, (Γ.cons x A).LookupLE Ξ →
      Ξ.JEqB levels H .unit .star .star → Ξ.JEqB levels H (B x) (a x) (b x)) :
    ∀ x ∉ L ∪ Δ.dv, (Δ.cons x A).JEqB levels H (B x) (a x) (b x) := by
  intro x hx
  have hxL : x ∉ L := fun h => hx (Finset.mem_union_left _ h)
  have hxΔ : x ∉ Δ.dv := fun h => hx (Finset.mem_union_right _ h)
  exact ih x hxL _ (lookupLE_cons e x A) (.cons_ok hn hΔ hxΔ hA)

/-- Every rule weakens once the actual original hypothesis leaves can be transported.

Terms and the universe cap are unchanged. The transport contract is used only
in the hypothesis case; every inference rule is reconstructed by induction.
-/
theorem weakening_of_hypotheses {levels : RuleBudget} {H H' : Set Jdg} {Γ : Ctx} {A a b : Tm 0}
    (hh : HypothesisTransport levels H H') (h : Γ.JEqB levels H A a b) :
    ∀ Δ, Γ.LookupLE Δ → Δ.JEqB levels H' .unit .star .star → Δ.JEqB levels H' A a b := by
  induction h with
  | hyp hj =>
    intro Δ e hΔ
    exact hh hj e hΔ
  | nil_ok | cons_ok => intros; assumption
  | var hΓ hx ihΓ =>
    intro Δ e hΔ
    exact .var hΔ (e hx)
  | univ hn hΓ ihΓ =>
    intro Δ e hΔ
    exact .univ hn hΔ
  | empty hn hΓ ihΓ =>
    intro Δ e hΔ
    exact .empty hn hΔ
  | unit hn hΓ ihΓ =>
    intro Δ e hΔ
    exact .unit hn hΔ
  | nats hn hΓ ihΓ =>
    intro Δ e hΔ
    exact .nats hn hΔ
  | zero hΓ ihΓ =>
    intro Δ e hΔ
    exact .zero hΔ
  | succ h ih =>
    intro Δ e hΔ
    exact .succ (ih Δ e hΔ)
  | @pi Γ n hn A A' B B' L hA hB ihA ihB =>
    intro Δ e hΔ
    have ha : Δ.JEqB levels H' (.univ n) A A' := ihA Δ e hΔ
    exact .pi hn ha (family e hΔ hn (self ha) ihB)
  | @sigma Γ n hn A A' B B' L hA hB ihA ihB =>
    intro Δ e hΔ
    have ha : Δ.JEqB levels H' (.univ n) A A' := ihA Δ e hΔ
    exact .sigma hn ha (family e hΔ hn (self ha) ihB)
  | id hn hA ha hb ihA iha ihb =>
    intro Δ e hΔ
    exact .id hn (ihA Δ e hΔ) (iha Δ e hΔ) (ihb Δ e hΔ)
  | @abs Γ n hn A A' B b b' L hA hB hb ihA ihB ihb =>
    intro Δ e hΔ
    have ha : Δ.JEqB levels H' (.univ n) A A' := ihA Δ e hΔ
    exact .abs hn ha (family e hΔ hn (self ha) ihB) (family e hΔ hn (self ha) ihb)
  | @app Γ n hn A f f' a a' B L hA hB hf ha ihA ihB ihf iha =>
    intro Δ e hΔ
    have hA' : Δ.JEqB levels H' (.univ n) A A := ihA Δ e hΔ
    exact .app hn hA' (family e hΔ hn hA' ihB) (ihf Δ e hΔ) (iha Δ e hΔ)
  | @pair Γ n hn A a a' b b' B L hA hB ha hb ihA ihB iha ihb =>
    intro Δ e hΔ
    have hA' : Δ.JEqB levels H' (.univ n) A A := ihA Δ e hΔ
    exact .pair hn hA' (family e hΔ hn hA' ihB) (iha Δ e hΔ) (ihb Δ e hΔ)
  | @fst Γ n hn A p p' B L hA hB hp ihA ihB ihp =>
    intro Δ e hΔ
    have ha : Δ.JEqB levels H' (.univ n) A A := ihA Δ e hΔ
    exact .fst hn ha (family e hΔ hn ha ihB) (ihp Δ e hΔ)
  | @snd Γ n hn A p p' B L hA hB hp ihA ihB ihp =>
    intro Δ e hΔ
    have ha : Δ.JEqB levels H' (.univ n) A A := ihA Δ e hΔ
    exact .snd hn ha (family e hΔ hn ha ihB) (ihp Δ e hΔ)
  | natrec hn hC hz hs hm ihC ihz ihs ihm =>
    intro Δ e hΔ
    exact .natrec hn (family e hΔ hn (.nats hn hΔ) ihC) (ihz Δ e hΔ)
      (family e hΔ hn (.nats hn hΔ) ihs) (ihm Δ e hΔ)
  | refl ha iha =>
    intro Δ e hΔ
    exact .refl (iha Δ e hΔ)
  | absurd hn hC he ihC ihe =>
    intro Δ e hΔ
    exact .absurd hn (ihC Δ e hΔ) (ihe Δ e hΔ)
  | @beta_app Γ n hn A a B b L hA hB hb ha ihA ihB ihb iha =>
    intro Δ e hΔ
    have hA' : Δ.JEqB levels H' (.univ n) A A := ihA Δ e hΔ
    exact .beta_app hn hA' (family e hΔ hn hA' ihB)
      (family e hΔ hn hA' ihb) (iha Δ e hΔ)
  | @beta_fst Γ n hn A a b B L hA hB ha hb ihA ihB iha ihb =>
    intro Δ e hΔ
    have hA' : Δ.JEqB levels H' (.univ n) A A := ihA Δ e hΔ
    exact .beta_fst hn hA' (family e hΔ hn hA' ihB) (iha Δ e hΔ) (ihb Δ e hΔ)
  | @beta_snd Γ n hn A a b B L hA hB ha hb ihA ihB iha ihb =>
    intro Δ e hΔ
    have hA' : Δ.JEqB levels H' (.univ n) A A := ihA Δ e hΔ
    exact .beta_snd hn hA' (family e hΔ hn hA' ihB) (iha Δ e hΔ) (ihb Δ e hΔ)
  | beta_natrec_zero hn hC hz hs ihC ihz ihs =>
    intro Δ e hΔ
    exact .beta_natrec_zero hn (family e hΔ hn (.nats hn hΔ) ihC) (ihz Δ e hΔ)
      (family e hΔ hn (.nats hn hΔ) ihs)
  | beta_natrec_succ hn hC hz hs hm ihC ihz ihs ihm =>
    intro Δ e hΔ
    exact .beta_natrec_succ hn (family e hΔ hn (.nats hn hΔ) ihC) (ihz Δ e hΔ)
      (family e hΔ hn (.nats hn hΔ) ihs) (ihm Δ e hΔ)
  | reflect ha hb hp iha ihb ihp =>
    intro Δ e hΔ
    exact .reflect (iha Δ e hΔ) (ihb Δ e hΔ) (ihp Δ e hΔ)
  | id_uip ha hb hp iha ihb ihp =>
    intro Δ e hΔ
    exact .id_uip (iha Δ e hΔ) (ihb Δ e hΔ) (ihp Δ e hΔ)
  | unit_ext ha iha =>
    intro Δ e hΔ
    exact .unit_ext (iha Δ e hΔ)
  | @pi_ext Γ n hn A f g B L hA hB hf hg hfg ihA ihB ihf ihg ihfg =>
    intro Δ e hΔ
    have ha : Δ.JEqB levels H' (.univ n) A A := ihA Δ e hΔ
    exact .pi_ext hn ha (family e hΔ hn ha ihB) (ihf Δ e hΔ) (ihg Δ e hΔ)
      (family e hΔ hn ha ihfg)
  | @sigma_ext Γ n hn A p q B L hA hB hp hq h1 h2 ihA ihB ihp ihq ih1 ih2 =>
    intro Δ e hΔ
    have ha : Δ.JEqB levels H' (.univ n) A A := ihA Δ e hΔ
    exact .sigma_ext hn ha (family e hΔ hn ha ihB) (ihp Δ e hΔ) (ihq Δ e hΔ)
      (ih1 Δ e hΔ) (ih2 Δ e hΔ)
  | symm h ih =>
    intro Δ e hΔ
    exact (ih Δ e hΔ).symm
  | trans hab hbc ihab ihbc =>
    intro Δ e hΔ
    exact .trans (ihab Δ e hΔ) (ihbc Δ e hΔ)
  | conv hn hA ha ihA iha =>
    intro Δ e hΔ
    exact .conv hn (ihA Δ e hΔ) (iha Δ e hΔ)
  | cumul hn hmn hA ihA =>
    intro Δ e hΔ
    exact .cumul hn hmn (ihA Δ e hΔ)
  | @wtype Γ n hn A A' B B' L hA hB ihA ihB =>
    intro Δ e hΔ
    have ha : Δ.JEqB levels H' (.univ n) A A' := ihA Δ e hΔ
    exact .wtype hn ha (family e hΔ hn (self ha) ihB)
  | @sup Γ n hn A a a' f f' B L hA hB ha hf ihA ihB iha ihf =>
    intro Δ e hΔ
    have hA' : Δ.JEqB levels H' (.univ n) A A := ihA Δ e hΔ
    exact .sup hn hA' (family e hΔ hn hA' ihB) (iha Δ e hΔ) (ihf Δ e hΔ)
  | @wrec Γ n m hn hm A s s' t t' B C C' L hA hB hC hs ht ihA ihB ihC ihs iht =>
    intro Δ e hΔ
    have ha : Δ.JEqB levels H' (.univ n) A A := ihA Δ e hΔ
    have hb : ∀ x ∉ L ∪ Δ.dv, (Δ.cons x A).JEqB levels H' (.univ n)
        (B.open x) (B.open x) := family e hΔ hn ha ihB
    have hw : Δ.JEqB levels H' (.univ n) (.wtype A B) (.wtype A B) :=
      Ctx.JEqB.wtype hn ha hb
    exact .wrec hn hm ha hb (family e hΔ hn hw ihC) (ihs Δ e hΔ) (iht Δ e hΔ)
  | @beta_wrec Γ n m hn hm A s a f B C L hA hB hC hs ha hf ihA ihB ihC ihs iha ihf =>
    show ∀ Δ, Γ.LookupLE Δ → Δ.JEqB levels H' .unit .star .star →
      Δ.JEqB levels H' (C.lst (.sup A B a f)) (.wrec A B C s (.sup A B a f))
        (.app (.app (.app s a) f) (Tm.recChildren A B C s a f))
    intro Δ e hΔ
    have hA' : Δ.JEqB levels H' (.univ n) A A := ihA Δ e hΔ
    have hB' : ∀ x ∉ L ∪ Δ.dv, (Δ.cons x A).JEqB levels H' (.univ n)
        (B.open x) (B.open x) := family e hΔ hn hA' ihB
    have hw : Δ.JEqB levels H' (.univ n) (.wtype A B) (.wtype A B) :=
      Ctx.JEqB.wtype hn hA' hB'
    exact .beta_wrec hn hm hA' hB' (family e hΔ hn hw ihC)
      (ihs Δ e hΔ) (iha Δ e hΔ) (ihf Δ e hΔ)

/-- The existing empty-theory theorem is the vacuous hypothesis-transport instance. -/
theorem weakening {levels : RuleBudget} {Γ : Ctx} {A a b : Tm 0}
    (h : Γ.JEqB levels ∅ A a b) : ∀ Δ, Γ.LookupLE Δ →
      Δ.JEqB levels ∅ .unit .star .star → Δ.JEqB levels ∅ A a b :=
  weakening_of_hypotheses (H := ∅) (H' := ∅) (fun hj _ _ => False.elim hj) h

theorem weakening_cons {levels : RuleBudget} {n : ℕ} {Γ : Ctx} {x : String} {B : Tm 0}
    (hΓ : Γ.JEqB levels ∅ .unit .star .star) (hx : x ∉ Γ.dv) (hn : RuleBudget.Allows levels n)
    (hB : Γ.JEqB levels ∅ (.univ n) B B) {A a b : Tm 0}
    (h : Γ.JEqB levels ∅ A a b) : (Γ.cons x B).JEqB levels ∅ A a b :=
  weakening h _ (lookupLE_fresh hx B) (.cons_ok hn hΓ hx hB)

end Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W
