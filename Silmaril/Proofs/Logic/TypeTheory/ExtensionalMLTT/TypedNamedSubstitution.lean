module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.NamedSubstitution.Thms
import Mathlib.Data.Fintype.EquivFin

@[expose] public section

namespace Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.TypedNamedSubstitution

open Silmaril.Logic.TypeTheory.ExtensionalMLTT

variable {x : String} {v : ETm 0}

private theorem self {Γ : ECtx} {A a b : ETm 0} (h : ECtx.JEqH ∅ Γ A a b) :
    ECtx.JEqH ∅ Γ A a a := .trans h h.symm

theorem lookup_subst_cons {Γ Δ : ECtx} {y : String} {A : ETm 0}
    (e : ECtx.Subst x v Γ Δ) (hy : y ≠ x) (hyΔ : y ∉ Δ.dv)
    (hctx : ECtx.JEqH ∅ (Δ.cons y (A.fsubst x v)) .unit .star .star) :
    ECtx.Subst x v (Γ.cons y A) (Δ.cons y (A.fsubst x v)) := by
  intro z B h
  cases h with
  | here =>
    simpa only [ETm.fsubst, hy, ite_false] using
      ECtx.JEqH.var hctx (ECtx.Lookup.here Δ y (A.fsubst x v))
  | there _ _ _ _ _ h hz =>
    exact (e h).weaken hctx (ECtx.Embeds.fresh hyΔ (A.fsubst x v))

private def names (L : Finset String) (Δ : ECtx) (x : String) (v : ETm 0) : Finset String :=
  L ∪ insert x (Δ.dv ∪ v.fvs)

private theorem fresh_left {L : Finset String} {Δ : ECtx} {y : String}
    (hy : y ∉ names L Δ x v) : y ∉ L :=
  fun h => hy (Finset.mem_union_left _ h)

private theorem fresh_name {L : Finset String} {Δ : ECtx} {y : String}
    (hy : y ∉ names L Δ x v) : y ≠ x := by
  intro h
  subst y
  exact hy (Finset.mem_union_right _ (Finset.mem_insert_self _ _))

private theorem fresh_target {L : Finset String} {Δ : ECtx} {y : String}
    (hy : y ∉ names L Δ x v) : y ∉ Δ.dv :=
  fun h => hy (Finset.mem_union_right _ (Finset.mem_insert_of_mem (Finset.mem_union_left _ h)))

private theorem family {n : ℕ} {Γ Δ : ECtx} {A : ETm 0} {L : Finset String}
    {B a b : String → ETm 0} (e : ECtx.Subst x v Γ Δ)
    (hΔ : ECtx.JEqH ∅ Δ .unit .star .star) (hA : ECtx.JEqH ∅ Δ (.univ n) (A.fsubst x v) (A.fsubst x v))
    (ih : ∀ y ∉ L, ∀ Ξ, ECtx.Subst x v (Γ.cons y A) Ξ →
      ECtx.JEqH ∅ Ξ .unit .star .star →
      ECtx.JEqH ∅ Ξ ((B y).fsubst x v) ((a y).fsubst x v) ((b y).fsubst x v)) :
    ∀ y ∉ names L Δ x v, ECtx.JEqH ∅ (Δ.cons y (A.fsubst x v))
      ((B y).fsubst x v) ((a y).fsubst x v) ((b y).fsubst x v) := by
  intro y hy
  have hctx : ECtx.JEqH ∅ (Δ.cons y (A.fsubst x v)) .unit .star .star :=
    .cons_ok hΔ (fresh_target hy) hA
  exact ih y (fresh_left hy) _ (lookup_subst_cons e (fresh_name hy) (fresh_target hy) hctx) hctx

private theorem formFamily {n m : ℕ} {Γ Δ : ECtx} {A : ETm 0} {L : Finset String}
    {B B' : ETm 1} (e : ECtx.Subst x v Γ Δ)
    (hΔ : ECtx.JEqH ∅ Δ .unit .star .star) (hA : ECtx.JEqH ∅ Δ (.univ n) (A.fsubst x v) (A.fsubst x v))
    (ih : ∀ y ∉ L, ∀ Ξ, ECtx.Subst x v (Γ.cons y A) Ξ →
      ECtx.JEqH ∅ Ξ .unit .star .star →
      ECtx.JEqH ∅ Ξ (.univ m) ((B.open y).fsubst x v) ((B'.open y).fsubst x v)) :
    ∀ y ∉ names L Δ x v, ECtx.JEqH ∅ (Δ.cons y (A.fsubst x v)) (.univ m)
      ((B.fsubst x v).open y) ((B'.fsubst x v).open y) := by
  intro y hy
  have hctx : ECtx.JEqH ∅ (Δ.cons y (A.fsubst x v)) .unit .star .star :=
    .cons_ok hΔ (fresh_target hy) hA
  simpa only [ETm.fsubst_open x v _ (fresh_name hy)] using
    ih y (fresh_left hy) _ (lookup_subst_cons e (fresh_name hy) (fresh_target hy) hctx) hctx

private theorem openFamily {n : ℕ} {Γ Δ : ECtx} {A : ETm 0} {L : Finset String}
    {B a b : ETm 1} (e : ECtx.Subst x v Γ Δ)
    (hΔ : ECtx.JEqH ∅ Δ .unit .star .star) (hA : ECtx.JEqH ∅ Δ (.univ n) (A.fsubst x v) (A.fsubst x v))
    (ih : ∀ y ∉ L, ∀ Ξ, ECtx.Subst x v (Γ.cons y A) Ξ →
      ECtx.JEqH ∅ Ξ .unit .star .star →
      ECtx.JEqH ∅ Ξ ((B.open y).fsubst x v) ((a.open y).fsubst x v) ((b.open y).fsubst x v)) :
    ∀ y ∉ names L Δ x v, ECtx.JEqH ∅ (Δ.cons y (A.fsubst x v))
      ((B.fsubst x v).open y) ((a.fsubst x v).open y) ((b.fsubst x v).open y) := by
  intro y hy
  simpa only [ETm.fsubst_open x v _ (fresh_name hy)] using family e hΔ hA ih y hy

theorem substitution (x : String) (v : ETm 0) {Γ : ECtx} {A a b : ETm 0}
    (h : ECtx.JEqH ∅ Γ A a b) : ∀ Δ, ECtx.Subst x v Γ Δ →
      ECtx.JEqH ∅ Δ .unit .star .star → ECtx.JEqH ∅ Δ (A.fsubst x v) (a.fsubst x v) (b.fsubst x v) := by
  induction h
  case hyp Γ A a b hj => cases hj
  all_goals intro Δ e hΔ
  all_goals try simp [ETm.fsubst] at *
  case nil_ok => exact hΔ
  case cons_ok => exact hΔ
  case var Γ y A hΓ hx ihΓ =>
    simpa [ETm.fsubst] using e hx
  case univ Γ n hΓ ihΓ =>
    exact .univ hΔ
  case empty Γ n hΓ ihΓ =>
    exact .empty hΔ
  case unit Γ n hΓ ihΓ =>
    exact .unit hΔ
  case nats Γ n hΓ ihΓ =>
    exact .nats hΔ
  case zero Γ hΓ ihΓ =>
    exact .zero hΔ
  case succ Γ m m' h ih =>
    exact .succ (ih Δ e hΔ)
  case pi Γ n A A' B B' L hA hB ihA ihB =>
    have ha : ECtx.JEqH ∅ Δ (.univ n) (A.fsubst x v) (A'.fsubst x v) := ihA Δ e hΔ
    exact .pi ha (formFamily e hΔ (self ha) ihB)
  case sigma Γ n A A' B B' L hA hB ihA ihB =>
    have ha : ECtx.JEqH ∅ Δ (.univ n) (A.fsubst x v) (A'.fsubst x v) := ihA Δ e hΔ
    exact .sigma ha (formFamily e hΔ (self ha) ihB)
  case id Γ n A A' a a' b b' hA ha hb ihA iha ihb =>
    exact .id (ihA Δ e hΔ) (iha Δ e hΔ) (ihb Δ e hΔ)
  case abs Γ n A A' B b b' L hA hB hb ihA ihB ihb =>
    have ha : ECtx.JEqH ∅ Δ (.univ n) (A.fsubst x v) (A'.fsubst x v) := ihA Δ e hΔ
    exact .abs ha (formFamily e hΔ (self ha) ihB) (openFamily e hΔ (self ha) ihb)
  case app Γ n A f f' a a' B L hA hB hf ha ihA ihB ihf iha =>
    have hA' : ECtx.JEqH ∅ Δ (.univ n) (A.fsubst x v) (A.fsubst x v) := ihA Δ e hΔ
    exact .app hA' (formFamily e hΔ hA' ihB) (ihf Δ e hΔ) (iha Δ e hΔ)
  case pair Γ n A a a' b b' B L hA hB ha hb ihA ihB iha ihb =>
    have hA' : ECtx.JEqH ∅ Δ (.univ n) (A.fsubst x v) (A.fsubst x v) := ihA Δ e hΔ
    exact .pair hA' (formFamily e hΔ hA' ihB) (iha Δ e hΔ) (ihb Δ e hΔ)
  case fst Γ n A p p' B L hA hB hp ihA ihB ihp =>
    have ha : ECtx.JEqH ∅ Δ (.univ n) (A.fsubst x v) (A.fsubst x v) := ihA Δ e hΔ
    exact .fst ha (formFamily e hΔ ha ihB) (ihp Δ e hΔ)
  case snd Γ n A p p' B L hA hB hp ihA ihB ihp =>
    have ha : ECtx.JEqH ∅ Δ (.univ n) (A.fsubst x v) (A.fsubst x v) := ihA Δ e hΔ
    exact .snd ha (formFamily e hΔ ha ihB) (ihp Δ e hΔ)
  case natrec Γ n C C' s s' z z' m m' L hC hz hs hm ihC ihm ihz ihs =>
    show ECtx.JEqH ∅ Δ ((C.fsubst x v).lst (m.fsubst x v))
      (.natrec (C.fsubst x v) (s.fsubst x v) (z.fsubst x v) (m.fsubst x v))
      (.natrec (C'.fsubst x v) (s'.fsubst x v) (z'.fsubst x v) (m'.fsubst x v))
    exact .natrec (n := n) (formFamily (A := .nats) e hΔ (by simpa only [ETm.fsubst] using ECtx.JEqH.nats (n := 0) hΔ) ihC) (ihz Δ e hΔ)
      (fun y hy => by
        have hctx : ECtx.JEqH ∅ (Δ.cons y (ETm.nats.fsubst x v)) .unit .star .star := by
          simpa only [ETm.fsubst] using ECtx.JEqH.cons_ok hΔ (fresh_target hy) (.nats (n := 0) hΔ)
        have he : ECtx.Subst x v (ECtx.cons _ y .nats)
            (Δ.cons y (ETm.nats.fsubst x v)) :=
          lookup_subst_cons (A := .nats) e (fresh_name hy) (fresh_target hy) hctx
        simpa [ETm.fsubst, fresh_name hy] using ihs y (fresh_left hy) _ he hctx) (ihm Δ e hΔ)
  case refl Γ A a a' ha iha =>
    exact .refl (iha Δ e hΔ)
  case absurd Γ n C C' e e' hC he ihC ihe =>
    exact .absurd (ihC Δ e hΔ) (ihe Δ e hΔ)
  case beta_app Γ n A a B b L hA hB hb ha ihA ihB ihb iha =>
    have hA' : ECtx.JEqH ∅ Δ (.univ n) (A.fsubst x v) (A.fsubst x v) := ihA Δ e hΔ
    exact .beta_app hA' (formFamily e hΔ hA' ihB)
      (openFamily e hΔ hA' ihb) (iha Δ e hΔ)
  case beta_fst Γ n A a b B L hA hB ha hb ihA ihB iha ihb =>
    have hA' : ECtx.JEqH ∅ Δ (.univ n) (A.fsubst x v) (A.fsubst x v) := ihA Δ e hΔ
    exact .beta_fst hA' (formFamily e hΔ hA' ihB) (iha Δ e hΔ) (ihb Δ e hΔ)
  case beta_snd Γ n A a b B L hA hB ha hb ihA ihB iha ihb =>
    have hA' : ECtx.JEqH ∅ Δ (.univ n) (A.fsubst x v) (A.fsubst x v) := ihA Δ e hΔ
    exact .beta_snd hA' (formFamily e hΔ hA' ihB) (iha Δ e hΔ) (ihb Δ e hΔ)
  case beta_natrec_zero Γ n C s z L hC hz hs ihC ihz ihs =>
    show ECtx.JEqH ∅ Δ ((C.fsubst x v).lst .zero)
      (.natrec (C.fsubst x v) (s.fsubst x v) (z.fsubst x v) .zero) (z.fsubst x v)
    exact .beta_natrec_zero (n := n) (formFamily (A := .nats) e hΔ (by simpa only [ETm.fsubst] using ECtx.JEqH.nats (n := 0) hΔ) ihC) (ihz Δ e hΔ)
      (fun y hy => by
        have hctx : ECtx.JEqH ∅ (Δ.cons y (ETm.nats.fsubst x v)) .unit .star .star := by
          simpa only [ETm.fsubst] using ECtx.JEqH.cons_ok hΔ (fresh_target hy) (.nats (n := 0) hΔ)
        have he : ECtx.Subst x v (ECtx.cons _ y .nats)
            (Δ.cons y (ETm.nats.fsubst x v)) :=
          lookup_subst_cons (A := .nats) e (fresh_name hy) (fresh_target hy) hctx
        simpa [ETm.fsubst, fresh_name hy] using ihs y (fresh_left hy) _ he hctx)
  case beta_natrec_succ Γ n C s z m L hC hz hs hm ihC ihm ihz ihs =>
    show ECtx.JEqH ∅ Δ ((C.fsubst x v).lst (.succ (m.fsubst x v)))
      (.natrec (C.fsubst x v) (s.fsubst x v) (z.fsubst x v) (.succ (m.fsubst x v)))
      (.app ((s.fsubst x v).lst (m.fsubst x v))
        (.natrec (C.fsubst x v) (s.fsubst x v) (z.fsubst x v) (m.fsubst x v)))
    exact .beta_natrec_succ (n := n) (formFamily (A := .nats) e hΔ (by simpa only [ETm.fsubst] using ECtx.JEqH.nats (n := 0) hΔ) ihC) (ihz Δ e hΔ)
      (fun y hy => by
        have hctx : ECtx.JEqH ∅ (Δ.cons y (ETm.nats.fsubst x v)) .unit .star .star := by
          simpa only [ETm.fsubst] using ECtx.JEqH.cons_ok hΔ (fresh_target hy) (.nats (n := 0) hΔ)
        have he : ECtx.Subst x v (ECtx.cons _ y .nats)
            (Δ.cons y (ETm.nats.fsubst x v)) :=
          lookup_subst_cons (A := .nats) e (fresh_name hy) (fresh_target hy) hctx
        simpa [ETm.fsubst, fresh_name hy] using ihs y (fresh_left hy) _ he hctx) (ihm Δ e hΔ)
  case reflect Γ A a b p ha hb hp iha ihb ihp =>
    exact .reflect (iha Δ e hΔ) (ihb Δ e hΔ) (ihp Δ e hΔ)
  case id_uip Γ A a b p ha hb hp iha ihb ihp =>
    exact .id_uip (iha Δ e hΔ) (ihb Δ e hΔ) (ihp Δ e hΔ)
  case unit_ext Γ a ha iha =>
    exact .unit_ext (iha Δ e hΔ)
  case pi_ext Γ n A f g B L hA hB hf hg hfg ihA ihB ihf ihg ihfg =>
    show ECtx.JEqH ∅ Δ (.pi (A.fsubst x v) (B.fsubst x v)) (f.fsubst x v) (g.fsubst x v)
    have ha : ECtx.JEqH ∅ Δ (.univ n) (A.fsubst x v) (A.fsubst x v) := ihA Δ e hΔ
    exact .pi_ext ha (formFamily e hΔ ha ihB) (ihf Δ e hΔ) (ihg Δ e hΔ)
      (fun y hy => by
        have hctx : ECtx.JEqH ∅ (Δ.cons y (A.fsubst x v)) .unit .star .star :=
          .cons_ok hΔ (fresh_target hy) ha
        have he : ECtx.Subst x v (Γ.cons y A) (Δ.cons y (A.fsubst x v)) :=
          lookup_subst_cons (A := A) e (fresh_name hy) (fresh_target hy) hctx
        simpa [ETm.fsubst, fresh_name hy] using ihfg y (fresh_left hy) _ he hctx)
  case sigma_ext Γ n A p q B L hA hB hp hq h1 h2 ihA ihB ihp ihq ih1 ih2 =>
    have ha : ECtx.JEqH ∅ Δ (.univ n) (A.fsubst x v) (A.fsubst x v) := ihA Δ e hΔ
    exact .sigma_ext ha (formFamily e hΔ ha ihB) (ihp Δ e hΔ) (ihq Δ e hΔ)
      (ih1 Δ e hΔ) (ih2 Δ e hΔ)
  case symm Γ A a b h ih =>
    exact (ih Δ e hΔ).symm
  case trans Γ A a b c hab hbc ihab ihbc =>
    exact .trans (ihab Δ e hΔ) (ihbc Δ e hΔ)
  case conv Γ n A A' a a' hA ha ihA iha =>
    exact .conv (ihA Δ e hΔ) (iha Δ e hΔ)
  case cumul Γ m n A A' hmn hA ihA =>
    exact .cumul hmn (ihA Δ e hΔ)

theorem drop_lookup {Γ : ECtx} {A : ETm 0}
    (hΓ : ECtx.JEqH ∅ Γ .unit .star .star) (hv : ECtx.JEqH ∅ Γ A v v)
    (hxΓ : x ∉ Γ.typeFvs) (hxA : x ∉ A.fvs) :
    ECtx.Subst x v (Γ.cons x A) Γ := by
  intro y B h
  cases h with
  | here =>
    simpa only [ETm.fsubst, ite_true, ETm.castLE_refl, ETm.fsubst_fresh x v A hxA] using hv
  | there _ _ _ _ _ h hy =>
    have hxB : x ∉ B.fvs := fun hB => hxΓ (h.typeFvs hB)
    simpa only [ETm.fsubst, hy, ite_false, ETm.fsubst_fresh x v B hxB] using ECtx.JEqH.var hΓ h

theorem substitute_last {Γ : ECtx} {A B b b' : ETm 0}
    (hΓ : ECtx.JEqH ∅ Γ .unit .star .star) (hv : ECtx.JEqH ∅ Γ A v v)
    (hxΓ : x ∉ Γ.typeFvs) (hxA : x ∉ A.fvs)
    (h : ECtx.JEqH ∅ (Γ.cons x A) B b b') :
    ECtx.JEqH ∅ Γ (B.fsubst x v) (b.fsubst x v) (b'.fsubst x v) :=
  substitution x v h Γ (drop_lookup hΓ hv hxΓ hxA) hΓ

theorem instantiate {Γ : ECtx} {A : ETm 0} {B b b' : ETm 1} {L : Finset String}
    (hΓ : ECtx.JEqH ∅ Γ .unit .star .star) (hv : ECtx.JEqH ∅ Γ A v v)
    (h : ∀ y ∉ L, ECtx.JEqH ∅ (Γ.cons y A) (B.open y) (b.open y) (b'.open y)) :
    ECtx.JEqH ∅ Γ (B.lst v) (b.lst v) (b'.lst v) := by
  obtain ⟨y, hy⟩ := Infinite.exists_notMem_finset
    (L ∪ Γ.typeFvs ∪ A.fvs ∪ B.fvs ∪ b.fvs ∪ b'.fvs ∪ Γ.dv ∪ v.fvs)
  simp only [Finset.mem_union, not_or] at hy
  have hyL : y ∉ L := hy.1.1.1.1.1.1.1
  have hyΓ : y ∉ Γ.typeFvs := hy.1.1.1.1.1.1.2
  have hyA : y ∉ A.fvs := hy.1.1.1.1.1.2
  have hyB : y ∉ B.fvs := hy.1.1.1.1.2
  have hyb : y ∉ b.fvs := hy.1.1.1.2
  have hyb' : y ∉ b'.fvs := hy.1.1.2
  simpa only [ETm.fsubst_open_self y v B hyB, ETm.fsubst_open_self y v b hyb,
    ETm.fsubst_open_self y v b' hyb'] using
    substitute_last (x := y) hΓ hv hyΓ hyA (h y hyL)

end Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.TypedNamedSubstitution
