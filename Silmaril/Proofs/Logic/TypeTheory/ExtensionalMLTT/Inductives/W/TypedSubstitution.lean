module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.NamedSubstitution

@[expose] public section

namespace Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W

open Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W

variable {H : Set Jdg} {levels : RuleBudget} {x : String} {v : Tm 0}

private theorem self {Γ : Ctx} {A a b : Tm 0} (h : Γ.JEqB levels H A a b) :
    Γ.JEqB levels H A a a := .trans h h.symm

theorem lookup_subst_cons_of_hypotheses (hh : HypothesisTransport levels H H) {Γ Δ : Ctx} {y : String} {A : Tm 0}
    (e : Ctx.SubstB levels x v Γ Δ H) (hy : y ≠ x) (hyΔ : y ∉ Δ.dv)
    (hctx : (Δ.cons y (A.fsubst x v)).JEqB levels H .unit .star .star) :
    Ctx.SubstB levels x v (Γ.cons y A) (Δ.cons y (A.fsubst x v)) H := by
  intro z B h
  cases h with
  | here =>
    simpa only [Tm.fsubst, hy, ite_false] using
      Ctx.JEqB.var hctx (Ctx.Lookup.here Δ y (A.fsubst x v))
  | there _ _ _ _ _ h hz =>
    exact Ctx.JEqB.weaken_of_hypotheses hh (e h) (Ctx.LookupLE.fresh_cons hyΔ (A.fsubst x v)) hctx

private def names (L : Finset String) (Δ : Ctx) (x : String) (v : Tm 0) : Finset String :=
  L ∪ insert x (Δ.dv ∪ v.fvs)

private theorem fresh_left {L : Finset String} {Δ : Ctx} {y : String}
    (hy : y ∉ names L Δ x v) : y ∉ L :=
  fun h => hy (Finset.mem_union_left _ h)

private theorem fresh_name {L : Finset String} {Δ : Ctx} {y : String}
    (hy : y ∉ names L Δ x v) : y ≠ x := by
  intro h
  subst y
  exact hy (Finset.mem_union_right _ (Finset.mem_insert_self _ _))

private theorem fresh_target {L : Finset String} {Δ : Ctx} {y : String}
    (hy : y ∉ names L Δ x v) : y ∉ Δ.dv :=
  fun h => hy (Finset.mem_union_right _ (Finset.mem_insert_of_mem (Finset.mem_union_left _ h)))

private theorem family (hh : HypothesisTransport levels H H) {n : ℕ} {Γ Δ : Ctx} {A : Tm 0} {L : Finset String}
    {B a b : String → Tm 0} (e : Ctx.SubstB levels x v Γ Δ H)
    (hΔ : Δ.JEqB levels H .unit .star .star) (hn : RuleBudget.Allows levels n)
    (hA : Δ.JEqB levels H (.univ n) (A.fsubst x v) (A.fsubst x v))
    (ih : ∀ y ∉ L, ∀ Ξ, Ctx.SubstB levels x v (Γ.cons y A) Ξ H →
      Ξ.JEqB levels H .unit .star .star →
      Ξ.JEqB levels H ((B y).fsubst x v) ((a y).fsubst x v) ((b y).fsubst x v)) :
    ∀ y ∉ names L Δ x v, (Δ.cons y (A.fsubst x v)).JEqB levels H
      ((B y).fsubst x v) ((a y).fsubst x v) ((b y).fsubst x v) := by
  intro y hy
  have hctx : (Δ.cons y (A.fsubst x v)).JEqB levels H .unit .star .star :=
    .cons_ok hn hΔ (fresh_target hy) hA
  exact ih y (fresh_left hy) _ (lookup_subst_cons_of_hypotheses hh e (fresh_name hy) (fresh_target hy) hctx) hctx

private theorem formFamily (hh : HypothesisTransport levels H H) {n m : ℕ} {Γ Δ : Ctx} {A : Tm 0} {L : Finset String}
    {B B' : Tm 1} (e : Ctx.SubstB levels x v Γ Δ H)
    (hΔ : Δ.JEqB levels H .unit .star .star) (hn : RuleBudget.Allows levels n)
    (hA : Δ.JEqB levels H (.univ n) (A.fsubst x v) (A.fsubst x v))
    (ih : ∀ y ∉ L, ∀ Ξ, Ctx.SubstB levels x v (Γ.cons y A) Ξ H →
      Ξ.JEqB levels H .unit .star .star →
      Ξ.JEqB levels H (.univ m) ((B.open y).fsubst x v) ((B'.open y).fsubst x v)) :
    ∀ y ∉ names L Δ x v, (Δ.cons y (A.fsubst x v)).JEqB levels H (.univ m)
      ((B.fsubst x v).open y) ((B'.fsubst x v).open y) := by
  intro y hy
  have hctx : (Δ.cons y (A.fsubst x v)).JEqB levels H .unit .star .star :=
    .cons_ok hn hΔ (fresh_target hy) hA
  simpa only [Tm.fsubst_open x v _ (fresh_name hy)] using
    ih y (fresh_left hy) _ (lookup_subst_cons_of_hypotheses hh e (fresh_name hy) (fresh_target hy) hctx) hctx

private theorem openFamily (hh : HypothesisTransport levels H H) {n : ℕ} {Γ Δ : Ctx} {A : Tm 0} {L : Finset String}
    {B a b : Tm 1} (e : Ctx.SubstB levels x v Γ Δ H)
    (hΔ : Δ.JEqB levels H .unit .star .star) (hn : RuleBudget.Allows levels n)
    (hA : Δ.JEqB levels H (.univ n) (A.fsubst x v) (A.fsubst x v))
    (ih : ∀ y ∉ L, ∀ Ξ, Ctx.SubstB levels x v (Γ.cons y A) Ξ H →
      Ξ.JEqB levels H .unit .star .star →
      Ξ.JEqB levels H ((B.open y).fsubst x v) ((a.open y).fsubst x v) ((b.open y).fsubst x v)) :
    ∀ y ∉ names L Δ x v, (Δ.cons y (A.fsubst x v)).JEqB levels H
      ((B.fsubst x v).open y) ((a.fsubst x v).open y) ((b.fsubst x v).open y) := by
  intro y hy
  simpa only [Tm.fsubst_open x v _ (fresh_name hy)] using family hh e hΔ hn hA ih y hy

theorem substitution_of_hypotheses {levels : RuleBudget} {H H' : Set Jdg} (x : String) (v : Tm 0)
    (hw : HypothesisTransport levels H' H') (hs : HypothesisSubstitution levels H H' x v)
    {Γ : Ctx} {A a b : Tm 0} (h : Γ.JEqB levels H A a b) :
    ∀ Δ, Ctx.SubstB levels x v Γ Δ H' → Δ.JEqB levels H' .unit .star .star →
      Δ.JEqB levels H' (A.fsubst x v) (a.fsubst x v) (b.fsubst x v) := by
  induction h
  case hyp Γ A a b hj =>
    intro Δ e hΔ
    exact hs hj e hΔ
  all_goals intro Δ e hΔ
  all_goals try simp [Tm.fsubst] at *
  case nil_ok => exact hΔ
  case cons_ok => exact hΔ
  case var Γ y A hΓ hx ihΓ =>
    simpa [Tm.fsubst] using e hx
  case univ Γ n hn hΓ ihΓ =>
    exact .univ hn hΔ
  case empty Γ n hn hΓ ihΓ =>
    exact .empty hn hΔ
  case unit Γ n hn hΓ ihΓ =>
    exact .unit hn hΔ
  case nats Γ n hn hΓ ihΓ =>
    exact .nats hn hΔ
  case zero Γ hΓ ihΓ =>
    exact .zero hΔ
  case succ Γ m m' h ih =>
    exact .succ (ih Δ e hΔ)
  case pi Γ n hn A A' B B' L hA hB ihA ihB =>
    have ha : Δ.JEqB levels H' (.univ n) (A.fsubst x v) (A'.fsubst x v) := ihA Δ e hΔ
    exact .pi hn ha (formFamily hw e hΔ hn (self ha) ihB)
  case sigma Γ n hn A A' B B' L hA hB ihA ihB =>
    have ha : Δ.JEqB levels H' (.univ n) (A.fsubst x v) (A'.fsubst x v) := ihA Δ e hΔ
    exact .sigma hn ha (formFamily hw e hΔ hn (self ha) ihB)
  case id Γ n hn A A' a a' b b' hA ha hb ihA iha ihb =>
    exact .id hn (ihA Δ e hΔ) (iha Δ e hΔ) (ihb Δ e hΔ)
  case abs Γ n hn A A' B b b' L hA hB hb ihA ihB ihb =>
    have ha : Δ.JEqB levels H' (.univ n) (A.fsubst x v) (A'.fsubst x v) := ihA Δ e hΔ
    exact .abs hn ha (formFamily hw e hΔ hn (self ha) ihB) (openFamily hw e hΔ hn (self ha) ihb)
  case app Γ n hn A f f' a a' B L hA hB hf ha ihA ihB ihf iha =>
    have hA' : Δ.JEqB levels H' (.univ n) (A.fsubst x v) (A.fsubst x v) := ihA Δ e hΔ
    exact .app hn hA' (formFamily hw e hΔ hn hA' ihB) (ihf Δ e hΔ) (iha Δ e hΔ)
  case pair Γ n hn A a a' b b' B L hA hB ha hb ihA ihB iha ihb =>
    have hA' : Δ.JEqB levels H' (.univ n) (A.fsubst x v) (A.fsubst x v) := ihA Δ e hΔ
    exact .pair hn hA' (formFamily hw e hΔ hn hA' ihB) (iha Δ e hΔ) (ihb Δ e hΔ)
  case fst Γ n hn A p p' B L hA hB hp ihA ihB ihp =>
    have ha : Δ.JEqB levels H' (.univ n) (A.fsubst x v) (A.fsubst x v) := ihA Δ e hΔ
    exact .fst hn ha (formFamily hw e hΔ hn ha ihB) (ihp Δ e hΔ)
  case snd Γ n hn A p p' B L hA hB hp ihA ihB ihp =>
    have ha : Δ.JEqB levels H' (.univ n) (A.fsubst x v) (A.fsubst x v) := ihA Δ e hΔ
    exact .snd hn ha (formFamily hw e hΔ hn ha ihB) (ihp Δ e hΔ)
  case natrec Γ n hn C C' s s' z z' m m' L hC hz hs hm ihC ihm ihz ihs =>
    show Δ.JEqB levels H' ((C.fsubst x v).lst (m.fsubst x v))
      (.natrec (C.fsubst x v) (s.fsubst x v) (z.fsubst x v) (m.fsubst x v))
      (.natrec (C'.fsubst x v) (s'.fsubst x v) (z'.fsubst x v) (m'.fsubst x v))
    exact .natrec hn (formFamily hw (A := .nats) e hΔ hn (by simpa only [Tm.fsubst] using Ctx.JEqB.nats hn hΔ) ihC) (ihz Δ e hΔ)
      (fun y hy => by
        have hctx : (Δ.cons y (Tm.nats.fsubst x v)).JEqB levels H' .unit .star .star := by
          simpa only [Tm.fsubst] using Ctx.JEqB.cons_ok hn hΔ (fresh_target hy) (.nats hn hΔ)
        have he : Ctx.SubstB levels x v (Ctx.cons _ y .nats)
            (Δ.cons y (Tm.nats.fsubst x v)) H' :=
          lookup_subst_cons_of_hypotheses hw (A := .nats) e (fresh_name hy) (fresh_target hy) hctx
        simpa [Tm.fsubst, fresh_name hy] using ihs y (fresh_left hy) _ he hctx) (ihm Δ e hΔ)
  case refl Γ A a a' ha iha =>
    exact .refl (iha Δ e hΔ)
  case absurd Γ n hn C C' e e' hC he ihC ihe =>
    exact .absurd hn (ihC Δ e hΔ) (ihe Δ e hΔ)
  case beta_app Γ n hn A a B b L hA hB hb ha ihA ihB ihb iha =>
    have hA' : Δ.JEqB levels H' (.univ n) (A.fsubst x v) (A.fsubst x v) := ihA Δ e hΔ
    exact .beta_app hn hA' (formFamily hw e hΔ hn hA' ihB)
      (openFamily hw e hΔ hn hA' ihb) (iha Δ e hΔ)
  case beta_fst Γ n hn A a b B L hA hB ha hb ihA ihB iha ihb =>
    have hA' : Δ.JEqB levels H' (.univ n) (A.fsubst x v) (A.fsubst x v) := ihA Δ e hΔ
    exact .beta_fst hn hA' (formFamily hw e hΔ hn hA' ihB) (iha Δ e hΔ) (ihb Δ e hΔ)
  case beta_snd Γ n hn A a b B L hA hB ha hb ihA ihB iha ihb =>
    have hA' : Δ.JEqB levels H' (.univ n) (A.fsubst x v) (A.fsubst x v) := ihA Δ e hΔ
    exact .beta_snd hn hA' (formFamily hw e hΔ hn hA' ihB) (iha Δ e hΔ) (ihb Δ e hΔ)
  case beta_natrec_zero Γ n hn C s z L hC hz hs ihC ihz ihs =>
    show Δ.JEqB levels H' ((C.fsubst x v).lst .zero)
      (.natrec (C.fsubst x v) (s.fsubst x v) (z.fsubst x v) .zero) (z.fsubst x v)
    exact .beta_natrec_zero hn (formFamily hw (A := .nats) e hΔ hn (by simpa only [Tm.fsubst] using Ctx.JEqB.nats hn hΔ) ihC) (ihz Δ e hΔ)
      (fun y hy => by
        have hctx : (Δ.cons y (Tm.nats.fsubst x v)).JEqB levels H' .unit .star .star := by
          simpa only [Tm.fsubst] using Ctx.JEqB.cons_ok hn hΔ (fresh_target hy) (.nats hn hΔ)
        have he : Ctx.SubstB levels x v (Ctx.cons _ y .nats)
            (Δ.cons y (Tm.nats.fsubst x v)) H' :=
          lookup_subst_cons_of_hypotheses hw (A := .nats) e (fresh_name hy) (fresh_target hy) hctx
        simpa [Tm.fsubst, fresh_name hy] using ihs y (fresh_left hy) _ he hctx)
  case beta_natrec_succ Γ n hn C s z m L hC hz hs hm ihC ihm ihz ihs =>
    show Δ.JEqB levels H' ((C.fsubst x v).lst (.succ (m.fsubst x v)))
      (.natrec (C.fsubst x v) (s.fsubst x v) (z.fsubst x v) (.succ (m.fsubst x v)))
      (.app ((s.fsubst x v).lst (m.fsubst x v))
        (.natrec (C.fsubst x v) (s.fsubst x v) (z.fsubst x v) (m.fsubst x v)))
    exact .beta_natrec_succ hn (formFamily hw (A := .nats) e hΔ hn (by simpa only [Tm.fsubst] using Ctx.JEqB.nats hn hΔ) ihC) (ihz Δ e hΔ)
      (fun y hy => by
        have hctx : (Δ.cons y (Tm.nats.fsubst x v)).JEqB levels H' .unit .star .star := by
          simpa only [Tm.fsubst] using Ctx.JEqB.cons_ok hn hΔ (fresh_target hy) (.nats hn hΔ)
        have he : Ctx.SubstB levels x v (Ctx.cons _ y .nats)
            (Δ.cons y (Tm.nats.fsubst x v)) H' :=
          lookup_subst_cons_of_hypotheses hw (A := .nats) e (fresh_name hy) (fresh_target hy) hctx
        simpa [Tm.fsubst, fresh_name hy] using ihs y (fresh_left hy) _ he hctx) (ihm Δ e hΔ)
  case reflect Γ A a b p ha hb hp iha ihb ihp =>
    exact .reflect (iha Δ e hΔ) (ihb Δ e hΔ) (ihp Δ e hΔ)
  case id_uip Γ A a b p ha hb hp iha ihb ihp =>
    exact .id_uip (iha Δ e hΔ) (ihb Δ e hΔ) (ihp Δ e hΔ)
  case unit_ext Γ a ha iha =>
    exact .unit_ext (iha Δ e hΔ)
  case pi_ext Γ n hn A f g B L hA hB hf hg hfg ihA ihB ihf ihg ihfg =>
    show Δ.JEqB levels H' (.pi (A.fsubst x v) (B.fsubst x v)) (f.fsubst x v) (g.fsubst x v)
    have ha : Δ.JEqB levels H' (.univ n) (A.fsubst x v) (A.fsubst x v) := ihA Δ e hΔ
    exact .pi_ext hn ha (formFamily hw e hΔ hn ha ihB) (ihf Δ e hΔ) (ihg Δ e hΔ)
      (fun y hy => by
        have hctx : (Δ.cons y (A.fsubst x v)).JEqB levels H' .unit .star .star :=
          .cons_ok hn hΔ (fresh_target hy) ha
        have he : Ctx.SubstB levels x v (Γ.cons y A) (Δ.cons y (A.fsubst x v)) H' :=
          lookup_subst_cons_of_hypotheses hw (A := A) e (fresh_name hy) (fresh_target hy) hctx
        simpa [Tm.fsubst, fresh_name hy] using ihfg y (fresh_left hy) _ he hctx)
  case sigma_ext Γ n hn A p q B L hA hB hp hq h1 h2 ihA ihB ihp ihq ih1 ih2 =>
    have ha : Δ.JEqB levels H' (.univ n) (A.fsubst x v) (A.fsubst x v) := ihA Δ e hΔ
    exact .sigma_ext hn ha (formFamily hw e hΔ hn ha ihB) (ihp Δ e hΔ) (ihq Δ e hΔ)
      (ih1 Δ e hΔ) (ih2 Δ e hΔ)
  case symm Γ A a b h ih =>
    exact (ih Δ e hΔ).symm
  case trans Γ A a b c hab hbc ihab ihbc =>
    exact .trans (ihab Δ e hΔ) (ihbc Δ e hΔ)
  case conv Γ n hn A A' a a' hA ha ihA iha =>
    exact .conv hn (ihA Δ e hΔ) (iha Δ e hΔ)
  case cumul Γ m n hn A A' hmn hA ihA =>
    exact .cumul hn hmn (ihA Δ e hΔ)
  case wtype Γ n hn A A' B B' L hA hB ihA ihB =>
    have ha : Δ.JEqB levels H' (.univ n) (A.fsubst x v) (A'.fsubst x v) := ihA Δ e hΔ
    exact .wtype hn ha (formFamily hw e hΔ hn (self ha) ihB)
  case sup Γ n hn A a a' f f' B L hA hB ha hf ihA ihB iha ihf =>
    have hA' : Δ.JEqB levels H' (.univ n) (A.fsubst x v) (A.fsubst x v) := ihA Δ e hΔ
    exact .sup hn hA' (formFamily hw e hΔ hn hA' ihB) (iha Δ e hΔ) (ihf Δ e hΔ)
  case wrec Γ n m hn hm A s s' t t' B C C' L hA hB hC hs ht ihA ihB ihC iht ihs =>
    have ha : Δ.JEqB levels H' (.univ n) (A.fsubst x v) (A.fsubst x v) := ihA Δ e hΔ
    have hb : ∀ y ∉ names L Δ x v, (Δ.cons y (A.fsubst x v)).JEqB levels H' (.univ n)
        ((B.fsubst x v).open y) ((B.fsubst x v).open y) := formFamily hw e hΔ hn ha ihB
    have hWType : Δ.JEqB levels H' (.univ n) (.wtype (A.fsubst x v) (B.fsubst x v))
        (.wtype (A.fsubst x v) (B.fsubst x v)) :=
      Ctx.JEqB.wtype hn ha hb
    exact .wrec hn hm ha hb (formFamily hw (A := .wtype A B) e hΔ hn (by simpa only [Tm.fsubst] using hWType) ihC) (ihs Δ e hΔ) (iht Δ e hΔ)
  case beta_wrec Γ n m hn hm A s a f B C L hA hB hC hs ha hf ihA ihB ihC iha ihs ihf =>
    show Δ.JEqB levels H' ((C.fsubst x v).lst
      (.sup (A.fsubst x v) (B.fsubst x v) (a.fsubst x v) (f.fsubst x v)))
      (.wrec (A.fsubst x v) (B.fsubst x v) (C.fsubst x v) (s.fsubst x v)
        (.sup (A.fsubst x v) (B.fsubst x v) (a.fsubst x v) (f.fsubst x v)))
      (.app (.app (.app (s.fsubst x v) (a.fsubst x v)) (f.fsubst x v))
        (Tm.recChildren (A.fsubst x v) (B.fsubst x v) (C.fsubst x v)
          (s.fsubst x v) (a.fsubst x v) (f.fsubst x v)))
    have hA' : Δ.JEqB levels H' (.univ n) (A.fsubst x v) (A.fsubst x v) := ihA Δ e hΔ
    have hB' : ∀ y ∉ names L Δ x v, (Δ.cons y (A.fsubst x v)).JEqB levels H' (.univ n)
        ((B.fsubst x v).open y) ((B.fsubst x v).open y) := formFamily hw e hΔ hn hA' ihB
    have hWType : Δ.JEqB levels H' (.univ n) (.wtype (A.fsubst x v) (B.fsubst x v))
        (.wtype (A.fsubst x v) (B.fsubst x v)) :=
      Ctx.JEqB.wtype hn hA' hB'
    exact .beta_wrec hn hm hA' hB' (formFamily hw (A := .wtype A B) e hΔ hn (by simpa only [Tm.fsubst] using hWType) ihC)
      (ihs Δ e hΔ) (iha Δ e hΔ) (ihf Δ e hΔ)

theorem lookup_subst_cons {Γ Δ : Ctx} {y : String} {A : Tm 0}
    (e : Ctx.SubstB levels x v Γ Δ) (hy : y ≠ x) (hyΔ : y ∉ Δ.dv)
    (hctx : (Δ.cons y (A.fsubst x v)).JEqB levels ∅ .unit .star .star) :
    Ctx.SubstB levels x v (Γ.cons y A) (Δ.cons y (A.fsubst x v)) :=
  lookup_subst_cons_of_hypotheses (HypothesisTransport.empty levels ∅) e hy hyΔ hctx

theorem substitution {levels : RuleBudget} (x : String) (v : Tm 0) {Γ : Ctx} {A a b : Tm 0}
    (h : Γ.JEqB levels ∅ A a b) : ∀ Δ, Ctx.SubstB levels x v Γ Δ →
      Δ.JEqB levels ∅ .unit .star .star → Δ.JEqB levels ∅ (A.fsubst x v) (a.fsubst x v) (b.fsubst x v) :=
  substitution_of_hypotheses (H := ∅) (H' := ∅) x v (HypothesisTransport.empty levels ∅)
    (fun hj _ _ => False.elim hj) h

theorem drop_lookup {Γ : Ctx} {A : Tm 0}
    (hΓ : Γ.JEqB levels H .unit .star .star) (hv : Γ.JEqB levels H A v v)
    (hxΓ : x ∉ Γ.typeFvs) (hxA : x ∉ A.fvs) :
    Ctx.SubstB levels x v (Γ.cons x A) Γ H := by
  intro y B h
  cases h with
  | here =>
    simpa only [Tm.fsubst, ite_true, Tm.castLE_refl, Tm.fsubst_fresh x v A hxA] using hv
  | there _ _ _ _ _ h hy =>
    have hxB : x ∉ B.fvs := fun hB => hxΓ (h.typeFvs hB)
    simpa only [Tm.fsubst, hy, ite_false, Tm.fsubst_fresh x v B hxB] using Ctx.JEqB.var hΓ h

theorem substitute_last_of_hypotheses {H H' : Set Jdg}
    (hw : HypothesisTransport levels H' H') (hs : HypothesisSubstitution levels H H' x v) {Γ : Ctx} {A B b b' : Tm 0}
    (hΓ : Γ.JEqB levels H' .unit .star .star) (hv : Γ.JEqB levels H' A v v)
    (hxΓ : x ∉ Γ.typeFvs) (hxA : x ∉ A.fvs)
    (h : (Γ.cons x A).JEqB levels H B b b') :
    Γ.JEqB levels H' (B.fsubst x v) (b.fsubst x v) (b'.fsubst x v) :=
  substitution_of_hypotheses x v hw hs h Γ (drop_lookup hΓ hv hxΓ hxA) hΓ

theorem instantiate_of_hypotheses {H H' : Set Jdg}
    (hw : HypothesisTransport levels H' H')
    (hs : ∀ x, HypothesisSubstitution levels H H' x v) {Γ : Ctx} {A : Tm 0} {B b b' : Tm 1} {L : Finset String}
    (hΓ : Γ.JEqB levels H' .unit .star .star) (hv : Γ.JEqB levels H' A v v)
    (h : ∀ y ∉ L, (Γ.cons y A).JEqB levels H (B.open y) (b.open y) (b'.open y)) :
    Γ.JEqB levels H' (B.lst v) (b.lst v) (b'.lst v) := by
  obtain ⟨y, hy⟩ := Infinite.exists_notMem_finset
    (L ∪ Γ.typeFvs ∪ A.fvs ∪ B.fvs ∪ b.fvs ∪ b'.fvs ∪ Γ.dv ∪ v.fvs)
  simp only [Finset.mem_union, not_or] at hy
  have hyL : y ∉ L := hy.1.1.1.1.1.1.1
  have hyΓ : y ∉ Γ.typeFvs := hy.1.1.1.1.1.1.2
  have hyA : y ∉ A.fvs := hy.1.1.1.1.1.2
  have hyB : y ∉ B.fvs := hy.1.1.1.1.2
  have hyb : y ∉ b.fvs := hy.1.1.1.2
  have hyb' : y ∉ b'.fvs := hy.1.1.2
  simpa only [Tm.fsubst_open_self y v B hyB, Tm.fsubst_open_self y v b hyb,
    Tm.fsubst_open_self y v b' hyb'] using
    substitute_last_of_hypotheses (x := y) hw (hs y) hΓ hv hyΓ hyA (h y hyL)

theorem substitute_last {Γ : Ctx} {A B b b' : Tm 0}
    (hΓ : Γ.JEqB levels ∅ .unit .star .star) (hv : Γ.JEqB levels ∅ A v v)
    (hxΓ : x ∉ Γ.typeFvs) (hxA : x ∉ A.fvs)
    (h : (Γ.cons x A).JEqB levels ∅ B b b') :
    Γ.JEqB levels ∅ (B.fsubst x v) (b.fsubst x v) (b'.fsubst x v) :=
  substitution x v h Γ (drop_lookup hΓ hv hxΓ hxA) hΓ

theorem instantiate {Γ : Ctx} {A : Tm 0} {B b b' : Tm 1} {L : Finset String}
    (hΓ : Γ.JEqB levels ∅ .unit .star .star) (hv : Γ.JEqB levels ∅ A v v)
    (h : ∀ y ∉ L, (Γ.cons y A).JEqB levels ∅ (B.open y) (b.open y) (b'.open y)) :
    Γ.JEqB levels ∅ (B.lst v) (b.lst v) (b'.lst v) := by
  obtain ⟨y, hy⟩ := Infinite.exists_notMem_finset
    (L ∪ Γ.typeFvs ∪ A.fvs ∪ B.fvs ∪ b.fvs ∪ b'.fvs ∪ Γ.dv ∪ v.fvs)
  simp only [Finset.mem_union, not_or] at hy
  have hyL : y ∉ L := hy.1.1.1.1.1.1.1
  have hyΓ : y ∉ Γ.typeFvs := hy.1.1.1.1.1.1.2
  have hyA : y ∉ A.fvs := hy.1.1.1.1.1.2
  have hyB : y ∉ B.fvs := hy.1.1.1.1.2
  have hyb : y ∉ b.fvs := hy.1.1.1.2
  have hyb' : y ∉ b'.fvs := hy.1.1.2
  simpa only [Tm.fsubst_open_self y v B hyB, Tm.fsubst_open_self y v b hyb,
    Tm.fsubst_open_self y v b' hyb'] using
    substitute_last (x := y) hΓ hv hyΓ hyA (h y hyL)

private theorem lastCases_zero {α : Sort _} (a : α) (f : Fin 0 → α) :
    Fin.lastCases a f (0 : Fin 1) = a := Fin.lastCases_last

/-- A nonconstant open body computes to successor of zero at the same bound. -/
theorem instantiate_nat_successor : Ctx.JEqB 1 ∅ .nil .nats (.succ .zero) (.succ .zero) := by
  have hbody : ∀ y ∉ (∅ : Finset String), (Ctx.nil.cons y .nats).JEqB 1 ∅
      ((.nats : Tm 1).open y) ((.succ (.bv 0) : Tm 1).open y)
      ((.succ (.bv 0) : Tm 1).open y) := by
    intro y _
    have hctx : (Ctx.nil.cons y .nats).JEqB 1 ∅ .unit .star .star :=
      .cons_ok (n := 0) (by decide) .nil_ok (by simp [Ctx.dv]) (.nats (by decide) .nil_ok)
    simpa only [Tm.open, lastCases_zero] using
      Ctx.JEqB.succ (Ctx.JEqB.var hctx (Ctx.Lookup.here .nil y .nats))
  simpa only [Tm.lst, Tm.castLE, lastCases_zero] using
    instantiate (v := .zero) Ctx.JEqB.nil_ok (Ctx.JEqB.zero .nil_ok) hbody

/-- Nil-context, name-closed axioms constructively supply a nonempty structural theory. -/
theorem contextClosure_structural (levels : RuleBudget) {B : Set Jdg} (hB : ClosedHypotheses B) :
    StructuralTheory levels (ContextClosure B) := by
  refine ⟨ContextClosure.self_transport levels B, ?_⟩
  intro x v Γ Δ A a b hj _ _
  obtain ⟨Ξ, hΞ, _⟩ := hj
  obtain ⟨hContext, hA, ha, hb⟩ := hB _ hΞ
  change Ξ = .nil at hContext
  subst Ξ
  have hxA : x ∉ A.fvs := by simp [hA]
  have hxa : x ∉ a.fvs := by simp [ha]
  have hxb : x ∉ b.fvs := by simp [hb]
  rw [Tm.fsubst_fresh x v A hxA, Tm.fsubst_fresh x v a hxa, Tm.fsubst_fresh x v b hxb]
  apply Ctx.JEqB.hyp
  refine ⟨.nil, hΞ, ?_⟩
  intro y C h
  cases h

end Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W
