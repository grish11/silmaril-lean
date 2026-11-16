module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Finite.Assignments.Defs
import Mathlib.Data.Finset.Union

@[expose] public section

namespace Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.BoundedAssignments

open Silmaril.Logic.TypeTheory.ExtensionalMLTT

variable {levels : ℕ} {σ : String → ETm 0} {K : Finset String}

private theorem self {Γ : ECtx} {A a b : ETm 0} (h : ECtx.JEqB levels ∅ Γ A a b) :
    ECtx.JEqB levels ∅ Γ A a a := .trans h h.symm

theorem lookup_subst_cons {Γ Δ : ECtx} {y : String} {A : ETm 0}
    (e : ECtx.AssignmentB levels σ Γ Δ) (hy : σ y = .fv y) (hyΔ : y ∉ Δ.dv)
    (hctx : ECtx.JEqB levels ∅ (Δ.cons y (A.fmap σ)) .unit .star .star) :
    ECtx.AssignmentB levels σ (Γ.cons y A) (Δ.cons y (A.fmap σ)) := by
  intro z B h
  cases h with
  | here =>
    simpa only [ETm.fmap, ETm.castLE_refl, hy] using
      ECtx.JEqB.var hctx (ECtx.Lookup.here Δ y (A.fmap σ))
  | there _ _ _ _ _ h hz =>
    exact (e h).weaken hctx (ECtx.Embeds.fresh hyΔ (A.fmap σ))

private def names (L : Finset String) (Δ : ECtx) (σ : String → ETm 0)
    (K : Finset String) : Finset String :=
  L ∪ (K ∪ (Δ.dv ∪ K.biUnion (fun x => (σ x).fvs)))

private theorem fresh_left {L : Finset String} {Δ : ECtx} {y : String}
    (hy : y ∉ names L Δ σ K) : y ∉ L :=
  fun h => hy (Finset.mem_union_left _ h)

private theorem fresh_fixed (hσ : ETm.Supported σ K) {L : Finset String} {Δ : ECtx} {y : String}
    (hy : y ∉ names L Δ σ K) : σ y = .fv y :=
  hσ y (fun h => hy (Finset.mem_union_right _ (Finset.mem_union_left _ h)))

private theorem fresh_target {L : Finset String} {Δ : ECtx} {y : String}
    (hy : y ∉ names L Δ σ K) : y ∉ Δ.dv :=
  fun h => hy (Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_union_left _ h)))

private theorem family {n : ℕ} {Γ Δ : ECtx} {A : ETm 0} {L : Finset String}
    {B a b : String → ETm 0} (hn : n < levels) (hσ : ETm.Supported σ K)
    (e : ECtx.AssignmentB levels σ Γ Δ)
    (hΔ : ECtx.JEqB levels ∅ Δ .unit .star .star) (hA : ECtx.JEqB levels ∅ Δ (.univ n) (A.fmap σ) (A.fmap σ))
    (ih : ∀ y ∉ L, ∀ Ξ, ECtx.AssignmentB levels σ (Γ.cons y A) Ξ →
      ECtx.JEqB levels ∅ Ξ .unit .star .star →
      ECtx.JEqB levels ∅ Ξ ((B y).fmap σ) ((a y).fmap σ) ((b y).fmap σ)) :
    ∀ y ∉ names L Δ σ K, ECtx.JEqB levels ∅ (Δ.cons y (A.fmap σ))
      ((B y).fmap σ) ((a y).fmap σ) ((b y).fmap σ) := by
  intro y hy
  have hctx : ECtx.JEqB levels ∅ (Δ.cons y (A.fmap σ)) .unit .star .star :=
    .cons_ok hn hΔ (fresh_target hy) hA
  exact ih y (fresh_left hy) _ (lookup_subst_cons e (fresh_fixed hσ hy) (fresh_target hy) hctx) hctx

private theorem formFamily {n m : ℕ} {Γ Δ : ECtx} {A : ETm 0} {L : Finset String}
    {B B' : ETm 1} (hn : n < levels) (hσ : ETm.Supported σ K)
    (e : ECtx.AssignmentB levels σ Γ Δ)
    (hΔ : ECtx.JEqB levels ∅ Δ .unit .star .star) (hA : ECtx.JEqB levels ∅ Δ (.univ n) (A.fmap σ) (A.fmap σ))
    (ih : ∀ y ∉ L, ∀ Ξ, ECtx.AssignmentB levels σ (Γ.cons y A) Ξ →
      ECtx.JEqB levels ∅ Ξ .unit .star .star →
      ECtx.JEqB levels ∅ Ξ (.univ m) ((B.open y).fmap σ) ((B'.open y).fmap σ)) :
    ∀ y ∉ names L Δ σ K, ECtx.JEqB levels ∅ (Δ.cons y (A.fmap σ)) (.univ m)
      ((B.fmap σ).open y) ((B'.fmap σ).open y) := by
  intro y hy
  have hctx : ECtx.JEqB levels ∅ (Δ.cons y (A.fmap σ)) .unit .star .star :=
    .cons_ok hn hΔ (fresh_target hy) hA
  simpa only [ETm.fmap_open σ _ (fresh_fixed hσ hy)] using
    ih y (fresh_left hy) _ (lookup_subst_cons e (fresh_fixed hσ hy) (fresh_target hy) hctx) hctx

private theorem openFamily {n : ℕ} {Γ Δ : ECtx} {A : ETm 0} {L : Finset String}
    {B a b : ETm 1} (hn : n < levels) (hσ : ETm.Supported σ K)
    (e : ECtx.AssignmentB levels σ Γ Δ)
    (hΔ : ECtx.JEqB levels ∅ Δ .unit .star .star) (hA : ECtx.JEqB levels ∅ Δ (.univ n) (A.fmap σ) (A.fmap σ))
    (ih : ∀ y ∉ L, ∀ Ξ, ECtx.AssignmentB levels σ (Γ.cons y A) Ξ →
      ECtx.JEqB levels ∅ Ξ .unit .star .star →
      ECtx.JEqB levels ∅ Ξ ((B.open y).fmap σ) ((a.open y).fmap σ) ((b.open y).fmap σ)) :
    ∀ y ∉ names L Δ σ K, ECtx.JEqB levels ∅ (Δ.cons y (A.fmap σ))
      ((B.fmap σ).open y) ((a.fmap σ).open y) ((b.fmap σ).open y) := by
  intro y hy
  simpa only [ETm.fmap_open σ _ (fresh_fixed hσ hy)] using family hn hσ e hΔ hA ih y hy

theorem substitution (σ : String → ETm 0) (K : Finset String) (hσ : ETm.Supported σ K) {Γ : ECtx} {A a b : ETm 0}
    (h : ECtx.JEqB levels ∅ Γ A a b) : ∀ Δ, ECtx.AssignmentB levels σ Γ Δ →
      ECtx.JEqB levels ∅ Δ .unit .star .star → ECtx.JEqB levels ∅ Δ (A.fmap σ) (a.fmap σ) (b.fmap σ) := by
  induction h
  case hyp Γ A a b hj => cases hj
  all_goals intro Δ e hΔ
  all_goals try simp [ETm.fmap] at *
  case nil_ok => exact hΔ
  case cons_ok => exact hΔ
  case var Γ y A hΓ hx ihΓ =>
    simpa [ETm.fmap, ETm.castLE_refl] using e hx
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
    have ha : ECtx.JEqB levels ∅ Δ (.univ n) (A.fmap σ) (A'.fmap σ) := ihA Δ e hΔ
    exact .pi hn ha (formFamily hn hσ e hΔ (self ha) ihB)
  case sigma Γ n hn A A' B B' L hA hB ihA ihB =>
    have ha : ECtx.JEqB levels ∅ Δ (.univ n) (A.fmap σ) (A'.fmap σ) := ihA Δ e hΔ
    exact .sigma hn ha (formFamily hn hσ e hΔ (self ha) ihB)
  case id Γ n hn A A' a a' b b' hA ha hb ihA iha ihb =>
    exact .id hn (ihA Δ e hΔ) (iha Δ e hΔ) (ihb Δ e hΔ)
  case abs Γ n hn A A' B b b' L hA hB hb ihA ihB ihb =>
    have ha : ECtx.JEqB levels ∅ Δ (.univ n) (A.fmap σ) (A'.fmap σ) := ihA Δ e hΔ
    exact .abs hn ha (formFamily hn hσ e hΔ (self ha) ihB) (openFamily hn hσ e hΔ (self ha) ihb)
  case app Γ n hn A f f' a a' B L hA hB hf ha ihA ihB ihf iha =>
    have hA' : ECtx.JEqB levels ∅ Δ (.univ n) (A.fmap σ) (A.fmap σ) := ihA Δ e hΔ
    exact .app hn hA' (formFamily hn hσ e hΔ hA' ihB) (ihf Δ e hΔ) (iha Δ e hΔ)
  case pair Γ n hn A a a' b b' B L hA hB ha hb ihA ihB iha ihb =>
    have hA' : ECtx.JEqB levels ∅ Δ (.univ n) (A.fmap σ) (A.fmap σ) := ihA Δ e hΔ
    exact .pair hn hA' (formFamily hn hσ e hΔ hA' ihB) (iha Δ e hΔ) (ihb Δ e hΔ)
  case fst Γ n hn A p p' B L hA hB hp ihA ihB ihp =>
    have ha : ECtx.JEqB levels ∅ Δ (.univ n) (A.fmap σ) (A.fmap σ) := ihA Δ e hΔ
    exact .fst hn ha (formFamily hn hσ e hΔ ha ihB) (ihp Δ e hΔ)
  case snd Γ n hn A p p' B L hA hB hp ihA ihB ihp =>
    have ha : ECtx.JEqB levels ∅ Δ (.univ n) (A.fmap σ) (A.fmap σ) := ihA Δ e hΔ
    exact .snd hn ha (formFamily hn hσ e hΔ ha ihB) (ihp Δ e hΔ)
  case natrec Γ n hn C C' s s' z z' m m' L hC hz hs hm ihC ihm ihz ihs =>
    show ECtx.JEqB levels ∅ Δ ((C.fmap σ).lst (m.fmap σ))
      (.natrec (C.fmap σ) (s.fmap σ) (z.fmap σ) (m.fmap σ))
      (.natrec (C'.fmap σ) (s'.fmap σ) (z'.fmap σ) (m'.fmap σ))
    exact .natrec (n := n) hn (formFamily (A := .nats) (n := 0) (by omega) hσ e hΔ (by simpa only [ETm.fmap] using ECtx.JEqB.nats (n := 0) (by omega) hΔ) ihC) (ihz Δ e hΔ)
      (fun y hy => by
        have hctx : ECtx.JEqB levels ∅ (Δ.cons y (ETm.nats.fmap σ)) .unit .star .star := by
          simpa only [ETm.fmap] using ECtx.JEqB.cons_ok (n := 0) (by omega) hΔ (fresh_target hy) (.nats (n := 0) (by omega) hΔ)
        have he : ECtx.AssignmentB levels σ (ECtx.cons _ y .nats)
            (Δ.cons y (ETm.nats.fmap σ)) :=
          lookup_subst_cons (A := .nats) e (fresh_fixed hσ hy) (fresh_target hy) hctx
        simpa [ETm.fmap, fresh_fixed hσ hy] using ihs y (fresh_left hy) _ he hctx) (ihm Δ e hΔ)
  case refl Γ A a a' ha iha =>
    exact .refl (iha Δ e hΔ)
  case absurd Γ n hn C C' e e' hC he ihC ihe =>
    exact .absurd hn (ihC Δ e hΔ) (ihe Δ e hΔ)
  case beta_app Γ n hn A a B b L hA hB hb ha ihA ihB ihb iha =>
    have hA' : ECtx.JEqB levels ∅ Δ (.univ n) (A.fmap σ) (A.fmap σ) := ihA Δ e hΔ
    exact .beta_app hn hA' (formFamily hn hσ e hΔ hA' ihB)
      (openFamily hn hσ e hΔ hA' ihb) (iha Δ e hΔ)
  case beta_fst Γ n hn A a b B L hA hB ha hb ihA ihB iha ihb =>
    have hA' : ECtx.JEqB levels ∅ Δ (.univ n) (A.fmap σ) (A.fmap σ) := ihA Δ e hΔ
    exact .beta_fst hn hA' (formFamily hn hσ e hΔ hA' ihB) (iha Δ e hΔ) (ihb Δ e hΔ)
  case beta_snd Γ n hn A a b B L hA hB ha hb ihA ihB iha ihb =>
    have hA' : ECtx.JEqB levels ∅ Δ (.univ n) (A.fmap σ) (A.fmap σ) := ihA Δ e hΔ
    exact .beta_snd hn hA' (formFamily hn hσ e hΔ hA' ihB) (iha Δ e hΔ) (ihb Δ e hΔ)
  case beta_natrec_zero Γ n hn C s z L hC hz hs ihC ihz ihs =>
    show ECtx.JEqB levels ∅ Δ ((C.fmap σ).lst .zero)
      (.natrec (C.fmap σ) (s.fmap σ) (z.fmap σ) .zero) (z.fmap σ)
    exact .beta_natrec_zero (n := n) hn (formFamily (A := .nats) (n := 0) (by omega) hσ e hΔ (by simpa only [ETm.fmap] using ECtx.JEqB.nats (n := 0) (by omega) hΔ) ihC) (ihz Δ e hΔ)
      (fun y hy => by
        have hctx : ECtx.JEqB levels ∅ (Δ.cons y (ETm.nats.fmap σ)) .unit .star .star := by
          simpa only [ETm.fmap] using ECtx.JEqB.cons_ok (n := 0) (by omega) hΔ (fresh_target hy) (.nats (n := 0) (by omega) hΔ)
        have he : ECtx.AssignmentB levels σ (ECtx.cons _ y .nats)
            (Δ.cons y (ETm.nats.fmap σ)) :=
          lookup_subst_cons (A := .nats) e (fresh_fixed hσ hy) (fresh_target hy) hctx
        simpa [ETm.fmap, fresh_fixed hσ hy] using ihs y (fresh_left hy) _ he hctx)
  case beta_natrec_succ Γ n hn C s z m L hC hz hs hm ihC ihm ihz ihs =>
    show ECtx.JEqB levels ∅ Δ ((C.fmap σ).lst (.succ (m.fmap σ)))
      (.natrec (C.fmap σ) (s.fmap σ) (z.fmap σ) (.succ (m.fmap σ)))
      (.app ((s.fmap σ).lst (m.fmap σ))
        (.natrec (C.fmap σ) (s.fmap σ) (z.fmap σ) (m.fmap σ)))
    exact .beta_natrec_succ (n := n) hn (formFamily (A := .nats) (n := 0) (by omega) hσ e hΔ (by simpa only [ETm.fmap] using ECtx.JEqB.nats (n := 0) (by omega) hΔ) ihC) (ihz Δ e hΔ)
      (fun y hy => by
        have hctx : ECtx.JEqB levels ∅ (Δ.cons y (ETm.nats.fmap σ)) .unit .star .star := by
          simpa only [ETm.fmap] using ECtx.JEqB.cons_ok (n := 0) (by omega) hΔ (fresh_target hy) (.nats (n := 0) (by omega) hΔ)
        have he : ECtx.AssignmentB levels σ (ECtx.cons _ y .nats)
            (Δ.cons y (ETm.nats.fmap σ)) :=
          lookup_subst_cons (A := .nats) e (fresh_fixed hσ hy) (fresh_target hy) hctx
        simpa [ETm.fmap, fresh_fixed hσ hy] using ihs y (fresh_left hy) _ he hctx) (ihm Δ e hΔ)
  case reflect Γ A a b p ha hb hp iha ihb ihp =>
    exact .reflect (iha Δ e hΔ) (ihb Δ e hΔ) (ihp Δ e hΔ)
  case id_uip Γ A a b p ha hb hp iha ihb ihp =>
    exact .id_uip (iha Δ e hΔ) (ihb Δ e hΔ) (ihp Δ e hΔ)
  case unit_ext Γ a ha iha =>
    exact .unit_ext (iha Δ e hΔ)
  case pi_ext Γ n hn A f g B L hA hB hf hg hfg ihA ihB ihf ihg ihfg =>
    show ECtx.JEqB levels ∅ Δ (.pi (A.fmap σ) (B.fmap σ)) (f.fmap σ) (g.fmap σ)
    have ha : ECtx.JEqB levels ∅ Δ (.univ n) (A.fmap σ) (A.fmap σ) := ihA Δ e hΔ
    exact .pi_ext hn ha (formFamily hn hσ e hΔ ha ihB) (ihf Δ e hΔ) (ihg Δ e hΔ)
      (fun y hy => by
        have hctx : ECtx.JEqB levels ∅ (Δ.cons y (A.fmap σ)) .unit .star .star :=
          .cons_ok hn hΔ (fresh_target hy) ha
        have he : ECtx.AssignmentB levels σ (Γ.cons y A) (Δ.cons y (A.fmap σ)) :=
          lookup_subst_cons (A := A) e (fresh_fixed hσ hy) (fresh_target hy) hctx
        simpa [ETm.fmap, fresh_fixed hσ hy] using ihfg y (fresh_left hy) _ he hctx)
  case sigma_ext Γ n hn A p q B L hA hB hp hq h1 h2 ihA ihB ihp ihq ih1 ih2 =>
    have ha : ECtx.JEqB levels ∅ Δ (.univ n) (A.fmap σ) (A.fmap σ) := ihA Δ e hΔ
    exact .sigma_ext hn ha (formFamily hn hσ e hΔ ha ihB) (ihp Δ e hΔ) (ihq Δ e hΔ)
      (ih1 Δ e hΔ) (ih2 Δ e hΔ)
  case symm Γ A a b h ih =>
    exact (ih Δ e hΔ).symm
  case trans Γ A a b c hab hbc ihab ihbc =>
    exact .trans (ihab Δ e hΔ) (ihbc Δ e hΔ)
  case conv Γ n hn A A' a a' hA ha ihA iha =>
    exact .conv hn (ihA Δ e hΔ) (iha Δ e hΔ)
  case cumul Γ m n hn A A' hmn hA ihA =>
    exact .cumul hn hmn (ihA Δ e hΔ)

theorem assignment_update {Γ Δ : ECtx} {y : String} {A v : ETm 0}
    (e : ECtx.AssignmentB levels σ Γ Δ) (hyΓ : y ∉ Γ.typeFvs) (hyA : y ∉ A.fvs)
    (hv : ECtx.JEqB levels ∅ Δ (A.fmap σ) v v) :
    ECtx.AssignmentB levels (Function.update σ y v) (Γ.cons y A) Δ := by
  intro z B h
  cases h with
  | here =>
    simpa only [ETm.fmap_update_fresh σ A y v hyA, Function.update_self] using hv
  | there _ _ _ _ _ h hz =>
    have hyB : y ∉ B.fvs := fun hB => hyΓ (h.typeFvs hB)
    simpa only [ETm.fmap_update_fresh σ B y v hyB, Function.update_of_ne hz] using e h

theorem assignment_identity {Γ : ECtx} (hΓ : ECtx.JEqB levels ∅ Γ .unit .star .star) :
    ECtx.AssignmentB levels ETm.fv Γ Γ := by
  intro y B hy
  simpa only [ETm.fmap_id] using ECtx.JEqB.var hΓ hy

theorem instantiate {Γ : ECtx} {A v : ETm 0} {B b b' : ETm 1} {L : Finset String}
    (hΓ : ECtx.JEqB levels ∅ Γ .unit .star .star) (hv : ECtx.JEqB levels ∅ Γ A v v)
    (h : ∀ y ∉ L, ECtx.JEqB levels ∅ (Γ.cons y A) (B.open y) (b.open y) (b'.open y)) :
    ECtx.JEqB levels ∅ Γ (B.lst v) (b.lst v) (b'.lst v) := by
  obtain ⟨y, hy⟩ := Infinite.exists_notMem_finset
    (L ∪ Γ.typeFvs ∪ A.fvs ∪ B.fvs ∪ b.fvs ∪ b'.fvs ∪ Γ.dv ∪ v.fvs)
  simp only [Finset.mem_union, not_or] at hy
  have hyL : y ∉ L := hy.1.1.1.1.1.1.1
  have hyΓ : y ∉ Γ.typeFvs := hy.1.1.1.1.1.1.2
  have hyA : y ∉ A.fvs := hy.1.1.1.1.1.2
  have hyB : y ∉ B.fvs := hy.1.1.1.1.2
  have hyb : y ∉ b.fvs := hy.1.1.1.2
  have hyb' : y ∉ b'.fvs := hy.1.1.2
  have hv' : ECtx.JEqB levels ∅ Γ (A.fmap ETm.fv) v v := by
    simpa only [ETm.fmap_id] using hv
  have e : ECtx.AssignmentB levels (Function.update ETm.fv y v) (Γ.cons y A) Γ :=
    assignment_update (assignment_identity hΓ) hyΓ hyA hv'
  have hσ : ETm.Supported (Function.update ETm.fv y v) (insert y ∅) :=
    ETm.Supported.update ETm.fv (fun _ _ => rfl) y v
  simpa only [ETm.fmap_update_open ETm.fv B y v hyB,
    ETm.fmap_update_open ETm.fv b y v hyb, ETm.fmap_update_open ETm.fv b' y v hyb',
    ETm.fmap_id] using substitution _ _ hσ (h y hyL) Γ e hΓ

theorem changeLast {Γ : ECtx} {x : String} {n : ℕ} {A A' T t u : ETm 0}
    (hΓ : ECtx.JEqB levels ∅ Γ .unit .star .star) (hx : x ∉ Γ.dv) (hn : n < levels)
    (hAA' : ECtx.JEqB levels ∅ Γ (.univ n) A A') (h : ECtx.JEqB levels ∅ (Γ.cons x A) T t u) :
    ECtx.JEqB levels ∅ (Γ.cons x A') T t u := by
  have hctx : ECtx.JEqB levels ∅ (Γ.cons x A') .unit .star .star :=
    .cons_ok hn hΓ hx (.trans (.symm hAA') hAA')
  have e : ECtx.AssignmentB levels ETm.fv (Γ.cons x A) (Γ.cons x A') := by
    intro z B hz
    simp only [ETm.fmap_id]
    cases hz with
    | here =>
      exact .conv hn (.symm (hAA'.weaken hctx (ECtx.Embeds.fresh hx A')))
        (.var hctx (.here _ _ _))
    | there _ _ _ _ _ hz hzx =>
      exact (ECtx.JEqB.var hΓ hz).weaken hctx (ECtx.Embeds.fresh hx A')
  simpa only [ETm.fmap_id] using
    substitution ETm.fv ∅ (fun _ _ => rfl) h _ e hctx

end Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.BoundedAssignments
