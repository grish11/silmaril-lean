module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Finite.Assignments.Thms
import Mathlib.Tactic

public section

namespace Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.BoundedRegularity

open Silmaril.Logic.TypeTheory.ExtensionalMLTT

theorem lookup_formation {levels : ℕ} {Γ : ECtx} {T t u : ETm 0}
    (h : ECtx.JEqB levels ∅ Γ T t u) :
    ∀ {x A}, Γ.Lookup x A → ∃ n, n < levels ∧ ECtx.JEqB levels ∅ Γ (.univ n) A A := by
  induction h
  case hyp Γ A a b hj => cases hj
  case nil_ok => intro x A hx; cases hx
  case cons_ok Γ x A n hn hΓ hx hA ihΓ ihA =>
    show ∀ {y B}, (Γ.cons x A).Lookup y B →
      ∃ m, m < levels ∧ ECtx.JEqB levels ∅ (Γ.cons x A) (.univ m) B B
    intro y B hy
    have hctx : ECtx.JEqB levels ∅ (Γ.cons x A) .unit .star .star := .cons_ok hn hΓ hx hA
    cases hy with
    | here => exact ⟨n, hn, hA.weaken hctx (ECtx.Embeds.fresh hx A)⟩
    | there _ _ _ _ _ hy hne =>
      obtain ⟨m, hm, hB⟩ := ihΓ hy
      exact ⟨m, hm, hB.weaken hctx (ECtx.Embeds.fresh hx A)⟩
  all_goals assumption

private theorem instantiate_formation {levels : ℕ} {Γ : ECtx} {A v : ETm 0} {B : ETm 1}
    {n : ℕ} {L : Finset String} (hΓ : ECtx.JEqB levels ∅ Γ .unit .star .star)
    (hv : ECtx.JEqB levels ∅ Γ A v v)
    (hB : ∀ x ∉ L, ECtx.JEqB levels ∅ (Γ.cons x A) (.univ n) (B.open x) (B.open x)) :
    ECtx.JEqB levels ∅ Γ (.univ n) (B.lst v) (B.lst v) := by
  have hB' : ∀ x ∉ L, ECtx.JEqB levels ∅ (Γ.cons x A) ((.univ n : ETm 1).open x)
      (B.open x) (B.open x) := by
    simpa only [ETm.open] using hB
  simpa only [ETm.lst] using
    ECtx.JEqB.instantiate (B := .univ n) (b := B) (b' := B) hΓ hv hB'

private theorem raise_formation {levels n : ℕ} {Γ : ECtx} {A : ETm 0}
    (hn : n < levels) (hA : ECtx.JEqB levels ∅ Γ (.univ n) A A) :
    ∃ m, m < levels + 1 ∧ ECtx.JEqB (levels + 1) ∅ Γ (.univ m) A A :=
  ⟨n, Nat.lt_trans hn (Nat.lt_succ_self levels), hA.weakenLevels (Nat.le_succ levels)⟩

private theorem univ_formation {levels n : ℕ} {Γ : ECtx} (hn : n < levels)
    (hΓ : ECtx.JEqB levels ∅ Γ .unit .star .star) :
    ∃ m, m < levels + 1 ∧ ECtx.JEqB (levels + 1) ∅ Γ (.univ m) (.univ n) (.univ n) :=
  ⟨n + 1, by omega, .univ (by omega) (hΓ.weakenLevels (Nat.le_succ levels))⟩

theorem type_formation {levels : ℕ} {Γ : ECtx} {A a b : ETm 0}
    (h : ECtx.JEqB levels ∅ Γ A a b) :
    ∃ n, n < levels + 1 ∧ ECtx.JEqB (levels + 1) ∅ Γ (.univ n) A A := by
  induction h with
  | hyp h => exact False.elim h
  | nil_ok => exact ⟨0, Nat.zero_lt_succ levels, .unit (Nat.zero_lt_succ levels) .nil_ok⟩
  | cons_ok hn hΓ hx hA _ _ =>
    exact ⟨0, Nat.zero_lt_succ levels,
      .unit (Nat.zero_lt_succ levels) ((ECtx.JEqB.cons_ok hn hΓ hx hA).weakenLevels (Nat.le_succ levels))⟩
  | var hΓ hx _ =>
    obtain ⟨n, hn, hA⟩ := lookup_formation hΓ hx
    exact raise_formation hn hA
  | univ hn hΓ _ => exact univ_formation hn hΓ
  | empty hn hΓ _ => exact univ_formation hn hΓ
  | unit hn hΓ _ => exact univ_formation hn hΓ
  | nats hn hΓ _ => exact univ_formation hn hΓ
  | zero hΓ _ =>
    exact ⟨0, Nat.zero_lt_succ levels,
      .nats (Nat.zero_lt_succ levels) (hΓ.weakenLevels (Nat.le_succ levels))⟩
  | succ _ ih => exact ih
  | pi hn hA hB _ _ => exact univ_formation hn hA.context
  | sigma hn hA hB _ _ => exact univ_formation hn hA.context
  | id hn hA ha hb _ _ _ => exact univ_formation hn hA.context
  | abs hn hA hB hb _ _ _ => exact raise_formation hn (.pi hn (.trans hA (.symm hA)) hB)
  | app hn hA hB hf ha _ _ _ _ =>
    exact raise_formation hn (instantiate_formation hA.context (.trans ha (.symm ha)) hB)
  | pair hn hA hB ha hb _ _ _ _ => exact raise_formation hn (.sigma hn hA hB)
  | fst hn hA hB hp _ _ _ => exact raise_formation hn hA
  | @snd Γ n hn A p p' B L hA hB hp _ _ _ =>
    have hFst : ECtx.JEqB levels ∅ Γ A (.fst p) (.fst p) := .fst hn hA hB (.trans hp (.symm hp))
    exact raise_formation hn (instantiate_formation hp.context hFst hB)
  | @natrec Γ n hn C C' s s' z z' m m' L hC hz hs hm _ _ _ _ =>
    have hCself : ∀ x ∉ L, ECtx.JEqB levels ∅ (Γ.cons x .nats) (.univ n) (C.open x) (C.open x) :=
      fun x hx => .trans (hC x hx) (.symm (hC x hx))
    exact raise_formation hn (instantiate_formation hm.context (.trans hm (.symm hm)) hCself)
  | refl ha ih =>
    obtain ⟨n, hn, hA⟩ := ih
    have ha' := (.trans ha (.symm ha) : ECtx.JEqB levels ∅ _ _ _ _).weakenLevels (Nat.le_succ levels)
    exact ⟨n, hn, .id hn hA ha' ha'⟩
  | absurd hn hC he _ _ => exact raise_formation hn (.trans hC (.symm hC))
  | beta_app hn hA hB hb ha _ _ _ _ =>
    exact raise_formation hn (instantiate_formation hA.context ha hB)
  | beta_fst hn hA hB ha hb _ _ _ _ => exact raise_formation hn hA
  | beta_snd hn hA hB ha hb _ _ _ _ =>
    exact raise_formation hn (instantiate_formation hA.context ha hB)
  | beta_natrec_zero hn hC hz hs _ _ _ =>
    exact raise_formation hn (instantiate_formation hz.context (.zero hz.context) hC)
  | beta_natrec_succ hn hC hz hs hm _ _ _ _ =>
    exact raise_formation hn (instantiate_formation hm.context (.succ hm) hC)
  | reflect _ _ _ iha _ _ => exact iha
  | id_uip ha hb hp iha _ _ =>
    obtain ⟨n, hn, hA⟩ := iha
    exact ⟨n, hn, .id hn hA (ha.weakenLevels (Nat.le_succ levels)) (hb.weakenLevels (Nat.le_succ levels))⟩
  | unit_ext ha _ =>
    exact ⟨0, Nat.zero_lt_succ levels,
      .unit (Nat.zero_lt_succ levels) (ha.context.weakenLevels (Nat.le_succ levels))⟩
  | pi_ext hn hA hB hf hg hfg _ _ _ _ _ => exact raise_formation hn (.pi hn hA hB)
  | sigma_ext hn hA hB hp hq h1 h2 _ _ _ _ _ _ => exact raise_formation hn (.sigma hn hA hB)
  | symm _ ih => exact ih
  | trans _ _ ih _ => exact ih
  | conv hn hA ha _ _ => exact raise_formation hn (.trans (.symm hA) hA)
  | cumul hn hmn hA _ => exact univ_formation hn hA.context

end Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.BoundedRegularity
