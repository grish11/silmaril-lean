module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Finite.HeadInversion.Defs
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Finset.Union

public section

namespace Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.BoundedHeadInversion

open Silmaril.Logic.TypeTheory.ExtensionalMLTT

private def names (L K : Finset String) (Δ : ECtx) (σ : String → ETm 0) : Finset String :=
  L ∪ (K ∪ (Δ.dv ∪ K.biUnion (fun x => (σ x).fvs)))

private theorem fresh_left {L K : Finset String} {Δ : ECtx} {σ : String → ETm 0} {y : String}
    (hy : y ∉ names L K Δ σ) : y ∉ L :=
  fun h => hy (Finset.mem_union_left _ h)

private theorem fresh_fixed {L K : Finset String} {Δ : ECtx} {σ : String → ETm 0} {y : String}
    (hσ : ETm.Supported σ K) (hy : y ∉ names L K Δ σ) : σ y = .fv y :=
  hσ y (fun h => hy (Finset.mem_union_right _ (Finset.mem_union_left _ h)))

private theorem fresh_target {L K : Finset String} {Δ : ECtx} {σ : String → ETm 0} {y : String}
    (hy : y ∉ names L K Δ σ) : y ∉ Δ.dv :=
  fun h => hy (Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_union_left _ h)))

private theorem family {levels n : ℕ} {Γ Δ : ECtx} {A : ETm 0} {B B' : ETm 1}
    {L K : Finset String} {σ : String → ETm 0} (hn : n < levels) (hσ : ETm.Supported σ K)
    (e : ECtx.AssignmentB levels σ Γ Δ) (hΔ : ECtx.JEqB levels ∅ Δ .unit .star .star)
    (hA : ECtx.JEqB levels ∅ Δ (.univ n) (A.fmap σ) (A.fmap σ))
    (hB : ∀ x ∉ L, ECtx.JEqB levels ∅ (Γ.cons x A) (.univ n) (B.open x) (B'.open x)) :
    ∀ x ∉ names L K Δ σ, ECtx.JEqB levels ∅ (Δ.cons x (A.fmap σ)) (.univ n)
      ((B.fmap σ).open x) ((B'.fmap σ).open x) := by
  intro x hx
  have hctx : ECtx.JEqB levels ∅ (Δ.cons x (A.fmap σ)) .unit .star .star :=
    .cons_ok hn hΔ (fresh_target hx) hA
  have e' : ECtx.AssignmentB levels σ (Γ.cons x A) (Δ.cons x (A.fmap σ)) :=
    ECtx.AssignmentB.cons e (fresh_fixed hσ hx) (fresh_target hx) hctx
  simpa only [ETm.fmap, ETm.fmap_open σ _ (fresh_fixed hσ hx)] using
    (hB x (fresh_left hx)).assign σ K hσ e' hctx

/-- Both endpoints retain same-budget head formation under any actual bounded typed assignment. -/
theorem shape_assign {levels : ℕ} {Γ : ECtx} {A a b : ETm 0} (h : ECtx.JEqB levels ∅ Γ A a b)
    {Δ : ECtx} (σ : String → ETm 0) (K : Finset String) (hσ : ETm.Supported σ K)
    (e : ECtx.AssignmentB levels σ Γ Δ) (hΔ : ECtx.JEqB levels ∅ Δ .unit .star .star)
    (hs : ∀ x, ETm.HeadFormedB levels Δ (σ x)) :
    ETm.HeadFormedB levels Δ (a.fmap σ) ∧ ETm.HeadFormedB levels Δ (b.fmap σ) := by
  induction h generalizing Δ σ K
  case hyp Γ A a b hj => cases hj
  all_goals simp only [ETm.fmap, ETm.HeadFormedB, ETm.castLE_refl]
  case nil_ok => trivial
  case cons_ok => trivial
  case var Γ x A hΓ hx ihΓ => exact ⟨hs x, hs x⟩
  case univ => trivial
  case empty => trivial
  case unit => trivial
  case nats => trivial
  case zero => trivial
  case succ => trivial
  case pi Γ n hn A A' B B' L hA hB ihA ihB =>
    show ETm.HeadFormedB levels Δ (.pi (A.fmap σ) (B.fmap σ)) ∧
      ETm.HeadFormedB levels Δ (.pi (A'.fmap σ) (B'.fmap σ))
    have hAσ : ECtx.JEqB levels ∅ Δ (.univ n) (A.fmap σ) (A'.fmap σ) := hA.assign σ K hσ e hΔ
    have hAself : ECtx.JEqB levels ∅ Δ (.univ n) (A.fmap σ) (A.fmap σ) := .trans hAσ (.symm hAσ)
    have hBσ : ∀ x ∉ names L K Δ σ, ECtx.JEqB levels ∅ (Δ.cons x (A.fmap σ)) (.univ n)
        ((B.fmap σ).open x) ((B'.fmap σ).open x) := family hn hσ e hΔ hAself hB
    refine ⟨⟨n, hn, names L K Δ σ, hAself, fun x hx => .trans (hBσ x hx) (.symm (hBσ x hx))⟩,
      ⟨n, hn, names L K Δ σ, .trans (.symm hAσ) hAσ, ?_⟩⟩
    intro x hx
    exact ECtx.JEqB.changeLast hΔ (fresh_target hx) hn hAσ
      (.trans (.symm (hBσ x hx)) (hBσ x hx))
  case sigma Γ n hn A A' B B' L hA hB ihA ihB =>
    show ETm.HeadFormedB levels Δ (.sigma (A.fmap σ) (B.fmap σ)) ∧
      ETm.HeadFormedB levels Δ (.sigma (A'.fmap σ) (B'.fmap σ))
    have hAσ : ECtx.JEqB levels ∅ Δ (.univ n) (A.fmap σ) (A'.fmap σ) := hA.assign σ K hσ e hΔ
    have hAself : ECtx.JEqB levels ∅ Δ (.univ n) (A.fmap σ) (A.fmap σ) := .trans hAσ (.symm hAσ)
    have hBσ : ∀ x ∉ names L K Δ σ, ECtx.JEqB levels ∅ (Δ.cons x (A.fmap σ)) (.univ n)
        ((B.fmap σ).open x) ((B'.fmap σ).open x) := family hn hσ e hΔ hAself hB
    refine ⟨⟨n, hn, names L K Δ σ, hAself, fun x hx => .trans (hBσ x hx) (.symm (hBσ x hx))⟩,
      ⟨n, hn, names L K Δ σ, .trans (.symm hAσ) hAσ, ?_⟩⟩
    intro x hx
    exact ECtx.JEqB.changeLast hΔ (fresh_target hx) hn hAσ
      (.trans (.symm (hBσ x hx)) (hBσ x hx))
  case id => trivial
  case abs => trivial
  case app => trivial
  case pair => trivial
  case fst => trivial
  case snd => trivial
  case natrec => trivial
  case refl => trivial
  case absurd => trivial
  case beta_app Γ n hn A a B b L hA hB hb ha ihA ihB ihb iha =>
    show True ∧ ETm.HeadFormedB levels Δ ((b.lst a).fmap σ)
    obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset
      (L ∪ Γ.typeFvs ∪ A.fvs ∪ b.fvs ∪ Γ.dv ∪ K ∪ Δ.dv ∪ (a.fmap σ).fvs)
    simp only [Finset.mem_union, not_or] at hx
    have hxL : x ∉ L := hx.1.1.1.1.1.1.1
    have hxΓ : x ∉ Γ.typeFvs := hx.1.1.1.1.1.1.2
    have hxA : x ∉ A.fvs := hx.1.1.1.1.1.2
    have hxb : x ∉ b.fvs := hx.1.1.1.1.2
    have hv : ECtx.JEqB levels ∅ Δ (A.fmap σ) (a.fmap σ) (a.fmap σ) := ha.assign σ K hσ e hΔ
    have e' : ECtx.AssignmentB levels (Function.update σ x (a.fmap σ)) (Γ.cons x A) Δ :=
      ECtx.AssignmentB.update e hxΓ hxA hv
    have hs' : ∀ y, ETm.HeadFormedB levels Δ (Function.update σ x (a.fmap σ) y) := by
      intro y
      by_cases hy : y = x
      · subst y
        simpa only [Function.update_self] using (iha σ K hσ e hΔ hs).1
      · simpa only [Function.update_of_ne hy] using hs y
    refine ⟨True.intro, ?_⟩
    simpa only [ETm.fmap_update_open σ b x (a.fmap σ) hxb, ETm.fmap_lst, ETm.HeadFormedB] using
      (ihb x hxL (Function.update σ x (a.fmap σ)) (insert x K)
        (ETm.Supported.update σ hσ x (a.fmap σ)) e' hΔ hs').1
  case beta_fst Γ n hn A a b B L hA hB ha hb ihA ihB iha ihb =>
    exact ⟨True.intro, (iha σ K hσ e hΔ hs).1⟩
  case beta_snd Γ n hn A a b B L hA hB ha hb ihA ihB iha ihb =>
    exact ⟨True.intro, (ihb σ K hσ e hΔ hs).1⟩
  case beta_natrec_zero Γ n hn C s z L hC hz hs' ihC ihz ihs =>
    exact ⟨True.intro, (ihz σ K hσ e hΔ hs).1⟩
  case beta_natrec_succ => trivial
  case reflect Γ A a b p ha hb hp iha ihb ihp =>
    exact ⟨(iha σ K hσ e hΔ hs).1, (ihb σ K hσ e hΔ hs).1⟩
  case id_uip Γ A a b p ha hb hp iha ihb ihp =>
    exact ⟨(ihp σ K hσ e hΔ hs).1, True.intro⟩
  case unit_ext Γ a ha iha => exact ⟨(iha σ K hσ e hΔ hs).1, True.intro⟩
  case pi_ext Γ n hn A f g B L hA hB hf hg hfg ihA ihB ihf ihg ihfg =>
    exact ⟨(ihf σ K hσ e hΔ hs).1, (ihg σ K hσ e hΔ hs).1⟩
  case sigma_ext Γ n hn A p q B L hA hB hp hq h1 h2 ihA ihB ihp ihq ih1 ih2 =>
    exact ⟨(ihp σ K hσ e hΔ hs).1, (ihq σ K hσ e hΔ hs).1⟩
  case symm Γ A a b h ih => exact (ih σ K hσ e hΔ hs).symm
  case trans Γ A a b c hab hbc ihab ihbc =>
    exact ⟨(ihab σ K hσ e hΔ hs).1, (ihbc σ K hσ e hΔ hs).2⟩
  case conv Γ n hn A A' a a' hA ha ihA iha => exact iha σ K hσ e hΔ hs
  case cumul Γ m n A A' hmn hA ihA => exact ihA σ K hσ e hΔ hs

theorem shape {levels : ℕ} {Γ : ECtx} {A a b : ETm 0} (h : ECtx.JEqB levels ∅ Γ A a b) :
    ETm.HeadFormedB levels Γ a ∧ ETm.HeadFormedB levels Γ b := by
  have e : ECtx.AssignmentB levels ETm.fv Γ Γ := by
    intro x B hx
    simpa only [ETm.fmap_id] using ECtx.JEqB.var h.context hx
  simpa only [ETm.fmap_id] using
    shape_assign h ETm.fv ∅ (fun _ _ => rfl) e h.context (fun _ => True.intro)

theorem pi_formation {levels : ℕ} {Γ : ECtx} {A T v : ETm 0} {B : ETm 1}
    (h : ECtx.JEqB levels ∅ Γ T (.pi A B) v) :
    ∃ n : ℕ, n < levels ∧ ∃ L : Finset String, ECtx.JEqB levels ∅ Γ (.univ n) A A ∧ ∀ x ∉ L,
      ECtx.JEqB levels ∅ (Γ.cons x A) (.univ n) (B.open x) (B.open x) :=
  (shape h).1

theorem sigma_formation {levels : ℕ} {Γ : ECtx} {A T v : ETm 0} {B : ETm 1}
    (h : ECtx.JEqB levels ∅ Γ T (.sigma A B) v) :
    ∃ n : ℕ, n < levels ∧ ∃ L : Finset String, ECtx.JEqB levels ∅ Γ (.univ n) A A ∧ ∀ x ∉ L,
      ECtx.JEqB levels ∅ (Γ.cons x A) (.univ n) (B.open x) (B.open x) :=
  (shape h).1

end Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.BoundedHeadInversion
