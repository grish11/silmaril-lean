module

public import Silmaril.Proofs.Wasm.Abstract.ExposePTyped.TensorBasic

/-!
Proofs for `Silmaril.Wasm.Abstract.ExposePTyped.Thms`: a checked run of `EvalOXP C` under an
arity-respecting oracle keeps the context, ends as its check says (`GoodO`), and runs on any
stack with a passive suffix to the same store and frame, its result whiskered and read at its
target's arity (`Fwd`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.ExposePTyped

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Interp Silmaril.Wasm.Abstract.ExposePStruct Silmaril.Wasm.Abstract.ExposePTyped
open Silmaril.Wasm.Abstract.CallX Silmaril.Wasm.Abstract.CallXP
open Silmaril.Wasm.Abstract.CallXT (typeArity tailAnn)

variable {H : Type}

/-- The forward statement for one run. -/
def Fwd (Γ : Ctx H) (C : Abstract.CallRel H) (s : Store H) (f : Frame) (stk : List Val)
    (es : List BExpr) (r : Store H × Frame × POut) : Prop :=
  ∀ {labels : List Nat} {ret : Nat} {oc : Option Nat}, Γ.Good s →
    chkE (ehExt Γ.tags) s.funcs f.module f.locals.length ret labels (some stk.length) es = some oc →
    Γ.Good r.1 ∧ r.2.1.module = f.module ∧ r.2.1.locals.length = f.locals.length ∧
      GoodO labels ret oc r.2.2 ∧ ∀ rest, ∃ o', EvalOXP C s f (stk ++ rest) es (r.1, r.2.1, o') ∧
        trimO labels ret o' = trimO labels ret (whiskO rest r.2.2)

variable {Γ : Ctx H} {C : Abstract.CallRel H}

/-- The continuation of a run, its check moved to the state it starts in. -/
theorem fwd_cont {s s₁ : Store H} {f f₁ : Frame} {stk' : List Val} {es : List BExpr}
    {r : Store H × Frame × POut} {labels : List Nat} {ret : Nat} {oc : Option Nat} {n : Nat}
    (hg : Γ.Good s) (hg₁ : Γ.Good s₁) (hm : f₁.module = f.module)
    (hl : f₁.locals.length = f.locals.length)
    (hc : chkE (ehExt Γ.tags) s.funcs f.module f.locals.length ret labels (some n) es = some oc)
    (hn : stk'.length = n) (ih : Fwd Γ C s₁ f₁ stk' es r) :
    Γ.Good r.1 ∧ r.2.1.module = f.module ∧ r.2.1.locals.length = f.locals.length ∧
      GoodO labels ret oc r.2.2 ∧ ∀ rest, ∃ o', EvalOXP C s₁ f₁ (stk' ++ rest) es (r.1, r.2.1, o') ∧
        trimO labels ret o' = trimO labels ret (whiskO rest r.2.2) := by
  have hc' : chkE (ehExt Γ.tags) s₁.funcs f₁.module f₁.locals.length ret labels
      (some stk'.length) es = some oc := by
    rw [chk_eq (good_funcs hg hg₁) hm hl, hn]; exact hc
  obtain ⟨g, m, l, go, t⟩ := ih hg₁ hc'
  exact ⟨g, m.trans hm, l.trans hl, go, t⟩

theorem len_take_drop {vs stk : List Val} {n p : Nat} (hn : n ≤ vs.length) (hp : p ≤ stk.length) :
    (vs.take n ++ stk.drop p).length = stk.length - p + n := by
  simp; omega

theorem take_drop_append {vs stk rest : List Val} {n p : Nat} (hp : p ≤ stk.length) :
    vs.take n ++ (stk ++ rest).drop p = (vs.take n ++ stk.drop p) ++ rest := by
  rw [List.drop_append_of_le_length hp, List.append_assoc]

/-- **The forward tensor.** -/
theorem evalOXP_fwd (hC : ArityResp Γ C) {s : Store H} {f : Frame} {stk : List Val}
    {es : List BExpr} {r : Store H × Frame × POut} (d : EvalOXP C s f stk es r) :
    Fwd Γ C s f stk es r := by
  induction d with
  | nil =>
    intro labels ret oc hg hc
    simp only [chk_nilE, Option.some.injEq] at hc
    subst hc
    exact ⟨hg, rfl, rfl, rfl, fun rest => ⟨_, .nil, rfl⟩⟩
  | argsAbort _ ho iha =>
    intro labels ret oc hg hc
    obtain ⟨o₁, h1, -⟩ := chk_consE.mp hc
    obtain ⟨oa, ha, -⟩ := chk1_opE h1
    obtain ⟨g, m, l, go, t⟩ := iha hg ha
    refine ⟨g, m, l, goodO_abrupt ho go, fun rest => ?_⟩
    obtain ⟨o', d', e'⟩ := t rest
    rw [whiskO_abrupt ho] at e' ⊢
    exact ⟨o', .argsAbort d' (notNormal_of_trim ho e'), e'⟩
  | @callOk s s₁ s₂ f f₁ stk stk₁ vs x args es a fi ps rs fl r hargs hfi hty hcall hvs hk iha
      ihk =>
    intro labels ret oc hg hc
    obtain ⟨o₁, h1, h2⟩ := chk_consE.mp hc
    obtain ⟨oa, ha, hb⟩ := chk1_opE h1
    obtain ⟨g₁, m₁, l₁, go₁, t₁⟩ := iha hg ha
    have hoa : oa = some stk₁.length := go₁
    obtain ⟨p, q, hpq, hp, ho₁⟩ := flatChk_call (flatChkE_call (hb _ hoa))
    have hpq' := callArity_eq hfi hty
    rw [good_funcs hg g₁, m₁, hpq, Option.some.injEq, Prod.mk.injEq] at hpq'
    obtain ⟨rfl, rfl⟩ := hpq'
    obtain ⟨g₂, hlen⟩ := hC _ _ _ _ _ hcall g₁
    have hrs := hlen fi ps rs vs (funcs_of_func? hfi) hty hvs
    obtain ⟨g, m, l, go, t⟩ := fwd_cont hg g₂ m₁ l₁ (ho₁ ▸ h2) (len_take_drop hrs hp) ihk
    refine ⟨g, m, l, go, fun rest => ?_⟩
    obtain ⟨o', d', e'⟩ := t rest
    have ha' := eq_of_trim_normal (t₁ rest).choose_spec.2
    have hargs' := (t₁ rest).choose_spec.1
    rw [ha'] at hargs'
    have hcall' : C s₁ a ((stk₁ ++ rest).take ps.length).reverse (s₂, fl) := by
      rwa [List.take_append_of_le_length hp]
    refine ⟨o', .callOk hargs' hfi hty hcall' hvs ?_, e'⟩
    rwa [take_drop_append hp]
  | @callTrap s s₁ s₂ f f₁ stk stk₁ x args es a fi ps rs hargs hfi hty hcall iha =>
    intro labels ret oc hg hc
    obtain ⟨o₁, h1, -⟩ := chk_consE.mp hc
    obtain ⟨oa, ha, hb⟩ := chk1_opE h1
    obtain ⟨g₁, m₁, l₁, go₁, t₁⟩ := iha hg ha
    have hoa : oa = some stk₁.length := go₁
    obtain ⟨p, q, hpq, hp, -⟩ := flatChk_call (flatChkE_call (hb _ hoa))
    have hpq' := callArity_eq hfi hty
    rw [good_funcs hg g₁, m₁, hpq, Option.some.injEq, Prod.mk.injEq] at hpq'
    obtain ⟨rfl, rfl⟩ := hpq'
    refine ⟨(hC _ _ _ _ _ hcall g₁).1, m₁, l₁, trivial, fun rest => ?_⟩
    have ha' := eq_of_trim_normal (t₁ rest).choose_spec.2
    have hargs' := (t₁ rest).choose_spec.1
    rw [ha'] at hargs'
    refine ⟨_, .callTrap hargs' hfi hty ?_, rfl⟩
    rwa [List.take_append_of_le_length hp]
  | @callThrow s s₁ s₂ f f₁ stk stk₁ x args es a fi ps rs t hargs hfi hty hcall iha =>
    intro labels ret oc hg hc
    obtain ⟨o₁, h1, -⟩ := chk_consE.mp hc
    obtain ⟨oa, ha, hb⟩ := chk1_opE h1
    obtain ⟨g₁, m₁, l₁, go₁, t₁⟩ := iha hg ha
    have hoa : oa = some stk₁.length := go₁
    obtain ⟨p, q, hpq, hp, -⟩ := flatChk_call (flatChkE_call (hb _ hoa))
    have hpq' := callArity_eq hfi hty
    rw [good_funcs hg g₁, m₁, hpq, Option.some.injEq, Prod.mk.injEq] at hpq'
    obtain ⟨rfl, rfl⟩ := hpq'
    refine ⟨(hC _ _ _ _ _ hcall g₁).1, m₁, l₁, trivial, fun rest => ?_⟩
    have ha' := eq_of_trim_normal (t₁ rest).choose_spec.2
    have hargs' := (t₁ rest).choose_spec.1
    rw [ha'] at hargs'
    refine ⟨_, .callThrow hargs' hfi hty ?_, rfl⟩
    rwa [List.take_append_of_le_length hp]
  | @opOk s s₁ s₂ f f₁ f₂ stk stk₁ stk₂ i args es r hi hargs hflat hk iha ihk =>
    intro labels ret oc hg hc
    obtain ⟨o₁, h1, h2⟩ := chk_consE.mp hc
    obtain ⟨oa, ha, hb⟩ := chk1_opE h1
    obtain ⟨g₁, m₁, l₁, go₁, t₁⟩ := iha hg ha
    have hoa : oa = some stk₁.length := go₁
    have hck := hb _ hoa
    have hck' : flatChkE (ehExt Γ.tags) s₁.funcs f₁.module f₁.locals.length ret labels
        stk₁.length i = some o₁ := by
      rw [flatChkE_eq (good_funcs hg g₁) m₁ l₁]; exact hck
    obtain ⟨ho, inv⟩ := flat_normal (ext := ehExt Γ.tags) hflat (flatChk_of_evalFlat hflat hck')
    have g₂ : Γ.Good s₂ := ⟨(Abstract.XRecursion.evalFlat_funcs hflat).trans g₁.1, TagsOk.evalFlat g₁.2 hflat⟩
    obtain ⟨g, m, l, go, t⟩ := fwd_cont hg g₂ (inv.2.1.trans m₁) (inv.2.2.trans l₁) (ho ▸ h2) rfl ihk
    refine ⟨g, m, l, go, fun rest => ?_⟩
    obtain ⟨o', d', e'⟩ := t rest
    have ha' := eq_of_trim_normal (t₁ rest).choose_spec.2
    have hargs' := (t₁ rest).choose_spec.1
    rw [ha'] at hargs'
    have hfl' := evalFlat_whisk (s := s₁) (f := f₁) (stackPure_of_evalFlat hflat) hck rest
    rw [hflat] at hfl'
    exact ⟨o', .opOk hi hargs' hfl' d', e'⟩
  | @opStop s s₁ s₂ f f₁ f₂ stk stk₁ i args es fl hi hargs hflat hfl iha =>
    intro labels ret oc hg hc
    obtain ⟨o₁, h1, -⟩ := chk_consE.mp hc
    obtain ⟨oa, ha, hb⟩ := chk1_opE h1
    obtain ⟨g₁, m₁, l₁, go₁, t₁⟩ := iha hg ha
    have hoa : oa = some stk₁.length := go₁
    have hck := hb _ hoa
    have hck' : flatChkE (ehExt Γ.tags) s₁.funcs f₁.module f₁.locals.length ret labels
        stk₁.length i = some o₁ := by
      rw [flatChkE_eq (good_funcs hg g₁) m₁ l₁]; exact hck
    obtain ⟨hok, inv⟩ := flat_abrupt (ext := ehExt Γ.tags) hflat hfl (flatChk_of_evalFlat hflat hck') oc
    have g₂ : Γ.Good s₂ := ⟨(Abstract.XRecursion.evalFlat_funcs hflat).trans g₁.1, TagsOk.evalFlat g₁.2 hflat⟩
    refine ⟨g₂, inv.2.1.trans m₁, inv.2.2.trans l₁, goodO_of_flowOk hok, fun rest => ?_⟩
    have ha' := eq_of_trim_normal (t₁ rest).choose_spec.2
    have hargs' := (t₁ rest).choose_spec.1
    rw [ha'] at hargs'
    have hfl' := evalFlat_whisk (s := s₁) (f := f₁) (stackPure_of_evalFlat hflat) hck rest
    rw [hflat] at hfl'
    exact ⟨_, .opStop hi hargs' hfl' (notNormal_wFl hfl), trimO_wFl hok⟩
  | @blockOk s s₁ f f₁ stk vs bt body es np nr fl r har hbody hvs hk ihb ihk =>
    intro labels ret oc hg hc
    obtain ⟨o₁, h1, h2⟩ := chk_consE.mp hc
    obtain ⟨np', nr', hba, hle, hends, ho₁⟩ := chk1_blockE h1
    rw [← arity_eq, har, Option.some.injEq, Prod.mk.injEq] at hba
    obtain ⟨rfl, rfl⟩ := hba
    obtain ⟨ob, hob, hob'⟩ := endsAt_eqE hends
    have hlen : (stk.take np).length = np := by simp; omega
    obtain ⟨g₁, m₁, l₁, go₁, -⟩ := ihb hg (by rw [hlen]; exact hob)
    have hnr := goodO_blockVals go₁ hob' hvs
    obtain ⟨g, m, l, go, t⟩ := fwd_cont hg g₁ m₁ l₁ (ho₁ ▸ h2) (len_take_drop hnr hle) ihk
    refine ⟨g, m, l, go, fun rest => ?_⟩
    obtain ⟨o', d', e'⟩ := t rest
    refine ⟨o', .blockOk (s₁ := s₁) (f₁ := f₁) har ?_ hvs ?_, e'⟩
    · rwa [List.take_append_of_le_length hle]
    · rwa [take_drop_append hle]
  | @blockBrk s s₁ f f₁ stk vs bt body es np nr k har hbody ihb =>
    intro labels ret oc hg hc
    obtain ⟨o₁, h1, -⟩ := chk_consE.mp hc
    obtain ⟨np', nr', hba, hle, hends, -⟩ := chk1_blockE h1
    rw [← arity_eq, har, Option.some.injEq, Prod.mk.injEq] at hba
    obtain ⟨rfl, rfl⟩ := hba
    obtain ⟨ob, hob, -⟩ := endsAt_eqE hends
    have hlen : (stk.take np).length = np := by simp; omega
    obtain ⟨g₁, m₁, l₁, go₁, -⟩ := ihb hg (by rw [hlen]; exact hob)
    refine ⟨g₁, m₁, l₁, goodO_brk_succ go₁, fun rest => ⟨_, .blockBrk har ?_, rfl⟩⟩
    rwa [List.take_append_of_le_length hle]
  | @blockEsc s s₁ f f₁ stk bt body es np nr o har hbody ho ihb =>
    intro labels ret oc hg hc
    obtain ⟨o₁, h1, -⟩ := chk_consE.mp hc
    obtain ⟨np', nr', hba, hle, hends, -⟩ := chk1_blockE h1
    rw [← arity_eq, har, Option.some.injEq, Prod.mk.injEq] at hba
    obtain ⟨rfl, rfl⟩ := hba
    obtain ⟨ob, hob, -⟩ := endsAt_eqE hends
    have hlen : (stk.take np).length = np := by simp; omega
    obtain ⟨g₁, m₁, l₁, go₁, -⟩ := ihb hg (by rw [hlen]; exact hob)
    refine ⟨g₁, m₁, l₁, goodO_escape go₁ ho, fun rest => ⟨_, .blockEsc har ?_ ho, by rw [whiskO_abrupt (notNormal_of_escapes ho)]⟩⟩
    rwa [List.take_append_of_le_length hle]
  | @loopOk s s₁ f f₁ stk vs bt body es np nr r har hbody hk ihb ihk =>
    intro labels ret oc hg hc
    obtain ⟨o₁, h1, h2⟩ := chk_consE.mp hc
    obtain ⟨np', nr', hba, hle, hends, ho₁⟩ := chk1_loopE h1
    rw [← arity_eq, har, Option.some.injEq, Prod.mk.injEq] at hba
    obtain ⟨rfl, rfl⟩ := hba
    obtain ⟨ob, hob, hob'⟩ := endsAt_eqE hends
    have hlen : (stk.take np).length = np := by simp; omega
    obtain ⟨g₁, m₁, l₁, go₁, -⟩ := ihb hg (by rw [hlen]; exact hob)
    have hnr := (goodO_normal go₁ hob').ge
    obtain ⟨g, m, l, go, t⟩ := fwd_cont hg g₁ m₁ l₁ (ho₁ ▸ h2) (len_take_drop hnr hle) ihk
    refine ⟨g, m, l, go, fun rest => ?_⟩
    obtain ⟨o', d', e'⟩ := t rest
    refine ⟨o', .loopOk (s₁ := s₁) (f₁ := f₁) (vs := vs) har ?_ ?_, e'⟩
    · rwa [List.take_append_of_le_length hle]
    · rwa [take_drop_append hle]
  | @loopBack s s₁ f f₁ stk vs bt body es np nr r har hbody hk ihb ihk =>
    intro labels ret oc hg hc
    obtain ⟨o₁, h1, -⟩ := chk_consE.mp hc
    obtain ⟨np', nr', hba, hle, hends, -⟩ := chk1_loopE h1
    rw [← arity_eq, har, Option.some.injEq, Prod.mk.injEq] at hba
    obtain ⟨rfl, rfl⟩ := hba
    obtain ⟨ob, hob, -⟩ := endsAt_eqE hends
    have hlen : (stk.take np).length = np := by simp; omega
    obtain ⟨g₁, m₁, l₁, go₁, -⟩ := ihb hg (by rw [hlen]; exact hob)
    have hnp : np ≤ vs.length := by
      obtain ⟨n, hn, hle'⟩ := go₁
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hn
      exact hn ▸ hle'
    have hlen' : (vs.take np ++ stk.drop np).length = stk.length := by
      rw [len_take_drop hnp hle]; omega
    obtain ⟨g, m, l, go, t⟩ := fwd_cont hg g₁ m₁ l₁ hc hlen' ihk
    refine ⟨g, m, l, go, fun rest => ?_⟩
    obtain ⟨o', d', e'⟩ := t rest
    refine ⟨o', .loopBack (s₁ := s₁) (f₁ := f₁) (vs := vs) har ?_ ?_, e'⟩
    · rwa [List.take_append_of_le_length hle]
    · rwa [take_drop_append hle]
  | @loopBrk s s₁ f f₁ stk vs bt body es np nr k har hbody ihb =>
    intro labels ret oc hg hc
    obtain ⟨o₁, h1, -⟩ := chk_consE.mp hc
    obtain ⟨np', nr', hba, hle, hends, -⟩ := chk1_loopE h1
    rw [← arity_eq, har, Option.some.injEq, Prod.mk.injEq] at hba
    obtain ⟨rfl, rfl⟩ := hba
    obtain ⟨ob, hob, -⟩ := endsAt_eqE hends
    have hlen : (stk.take np).length = np := by simp; omega
    obtain ⟨g₁, m₁, l₁, go₁, -⟩ := ihb hg (by rw [hlen]; exact hob)
    refine ⟨g₁, m₁, l₁, goodO_brk_succ go₁, fun rest => ⟨_, .loopBrk har ?_, rfl⟩⟩
    rwa [List.take_append_of_le_length hle]
  | @loopEsc s s₁ f f₁ stk bt body es np nr o har hbody ho ihb =>
    intro labels ret oc hg hc
    obtain ⟨o₁, h1, -⟩ := chk_consE.mp hc
    obtain ⟨np', nr', hba, hle, hends, -⟩ := chk1_loopE h1
    rw [← arity_eq, har, Option.some.injEq, Prod.mk.injEq] at hba
    obtain ⟨rfl, rfl⟩ := hba
    obtain ⟨ob, hob, -⟩ := endsAt_eqE hends
    have hlen : (stk.take np).length = np := by simp; omega
    obtain ⟨g₁, m₁, l₁, go₁, -⟩ := ihb hg (by rw [hlen]; exact hob)
    refine ⟨g₁, m₁, l₁, goodO_escape go₁ ho, fun rest => ⟨_, .loopEsc har ?_ ho, by rw [whiskO_abrupt (notNormal_of_escapes ho)]⟩⟩
    rwa [List.take_append_of_le_length hle]
  | @ifOk s s₁ s₂ f f₁ f₂ stk stk₁ vs cv b bt c t el es np nr fl r hc' hb har harm hvs hk ihc
      iharm ihk =>
    intro labels ret oc hg hc
    obtain ⟨o₁, h1, h2⟩ := chk_consE.mp hc
    obtain ⟨occ, hcc, hrest⟩ := chk1_ifE h1
    obtain ⟨g₁, m₁, l₁, go₁, t₁⟩ := ihc hg hcc
    have hocc : occ = some (stk₁.length + 1) := go₁
    obtain ⟨np', nr', hba, hle, het, hee, ho₁⟩ := hrest _ hocc
    rw [← m₁, ← arity_eq, har, Option.some.injEq, Prod.mk.injEq] at hba
    obtain ⟨rfl, rfl⟩ := hba
    have hends : endsAt (chkE (ehExt Γ.tags) s₁.funcs f₁.module f₁.locals.length ret
        (nr :: labels) (some np) (if b then t else el)) nr = true := by
      rw [chk_eq (good_funcs hg g₁) m₁ l₁]; cases b <;> assumption
    obtain ⟨ob, hob, hob'⟩ := endsAt_eqE hends
    have hle' : np ≤ stk₁.length := by omega
    have hlen : (stk₁.take np).length = np := by simp; omega
    obtain ⟨g₂, m₂, l₂, go₂, -⟩ := iharm g₁ (by rw [hlen]; exact hob)
    have hnr := goodO_blockVals go₂ hob' hvs
    obtain ⟨g, m, l, go, t⟩ := fwd_cont hg g₂ (m₂.trans m₁) (l₂.trans l₁)
      (by rw [ho₁] at h2; convert h2 using 3; omega) (len_take_drop hnr hle') ihk
    refine ⟨g, m, l, go, fun rest => ?_⟩
    obtain ⟨o', d', e'⟩ := t rest
    have hc₁ := eq_of_trim_normal (t₁ rest).choose_spec.2
    have hcd := (t₁ rest).choose_spec.1
    rw [hc₁, List.cons_append] at hcd
    refine ⟨o', .ifOk (s₂ := s₂) (f₂ := f₂) hcd hb har ?_ hvs ?_, e'⟩
    · rwa [List.take_append_of_le_length hle']
    · rwa [take_drop_append hle']
  | @ifBrk s s₁ s₂ f f₁ f₂ stk stk₁ vs cv b bt c t el es np nr k hc' hb har harm ihc iharm =>
    intro labels ret oc hg hc
    obtain ⟨o₁, h1, -⟩ := chk_consE.mp hc
    obtain ⟨occ, hcc, hrest⟩ := chk1_ifE h1
    obtain ⟨g₁, m₁, l₁, go₁, t₁⟩ := ihc hg hcc
    have hocc : occ = some (stk₁.length + 1) := go₁
    obtain ⟨np', nr', hba, hle, het, hee, -⟩ := hrest _ hocc
    rw [← m₁, ← arity_eq, har, Option.some.injEq, Prod.mk.injEq] at hba
    obtain ⟨rfl, rfl⟩ := hba
    have hends : endsAt (chkE (ehExt Γ.tags) s₁.funcs f₁.module f₁.locals.length ret
        (nr :: labels) (some np) (if b then t else el)) nr = true := by
      rw [chk_eq (good_funcs hg g₁) m₁ l₁]; cases b <;> assumption
    obtain ⟨ob, hob, -⟩ := endsAt_eqE hends
    have hle' : np ≤ stk₁.length := by omega
    have hlen : (stk₁.take np).length = np := by simp; omega
    obtain ⟨g₂, m₂, l₂, go₂, -⟩ := iharm g₁ (by rw [hlen]; exact hob)
    refine ⟨g₂, m₂.trans m₁, l₂.trans l₁, goodO_brk_succ go₂, fun rest => ?_⟩
    have hc₁ := eq_of_trim_normal (t₁ rest).choose_spec.2
    have hcd := (t₁ rest).choose_spec.1
    rw [hc₁, List.cons_append] at hcd
    refine ⟨_, .ifBrk hcd hb har ?_, rfl⟩
    rwa [List.take_append_of_le_length hle']
  | @ifEsc s s₁ s₂ f f₁ f₂ stk stk₁ cv b bt c t el es np nr o hc' hb har harm ho ihc iharm =>
    intro labels ret oc hg hc
    obtain ⟨o₁, h1, -⟩ := chk_consE.mp hc
    obtain ⟨occ, hcc, hrest⟩ := chk1_ifE h1
    obtain ⟨g₁, m₁, l₁, go₁, t₁⟩ := ihc hg hcc
    have hocc : occ = some (stk₁.length + 1) := go₁
    obtain ⟨np', nr', hba, hle, het, hee, -⟩ := hrest _ hocc
    rw [← m₁, ← arity_eq, har, Option.some.injEq, Prod.mk.injEq] at hba
    obtain ⟨rfl, rfl⟩ := hba
    have hends : endsAt (chkE (ehExt Γ.tags) s₁.funcs f₁.module f₁.locals.length ret
        (nr :: labels) (some np) (if b then t else el)) nr = true := by
      rw [chk_eq (good_funcs hg g₁) m₁ l₁]; cases b <;> assumption
    obtain ⟨ob, hob, -⟩ := endsAt_eqE hends
    have hle' : np ≤ stk₁.length := by omega
    have hlen : (stk₁.take np).length = np := by simp; omega
    obtain ⟨g₂, m₂, l₂, go₂, -⟩ := iharm g₁ (by rw [hlen]; exact hob)
    refine ⟨g₂, m₂.trans m₁, l₂.trans l₁, goodO_escape go₂ ho, fun rest => ?_⟩
    have hc₁ := eq_of_trim_normal (t₁ rest).choose_spec.2
    have hcd := (t₁ rest).choose_spec.1
    rw [hc₁, List.cons_append] at hcd
    refine ⟨_, .ifEsc hcd hb har ?_ ho, by rw [whiskO_abrupt (notNormal_of_escapes ho)]⟩
    rwa [List.take_append_of_le_length hle']
  | ifAbort _ ho ihc =>
    intro labels ret oc hg hc
    obtain ⟨o₁, h1, -⟩ := chk_consE.mp hc
    obtain ⟨occ, hcc, -⟩ := chk1_ifE h1
    obtain ⟨g, m, l, go, t⟩ := ihc hg hcc
    refine ⟨g, m, l, goodO_abrupt ho go, fun rest => ?_⟩
    obtain ⟨o', d', e'⟩ := t rest
    rw [whiskO_abrupt ho] at e' ⊢
    exact ⟨o', .ifAbort d' (notNormal_of_trim ho e'), e'⟩
  | @callIndOk s s₁ s₂ f f₁ stk stk₁ vs x y args es ad i fa fi ps rs fl r hargs hres hfi hty hy
      hcall hvs hk iha ihk =>
    intro labels ret oc hg hc
    obtain ⟨o₁, h1, h2⟩ := chk_consE.mp hc
    obtain ⟨oa, ha, hb⟩ := chk1_opE h1
    obtain ⟨g₁, m₁, l₁, go₁, t₁⟩ := iha hg ha
    have hoa : oa = some (stk₁.length + 1) := go₁
    obtain ⟨hp, ho₁⟩ := flatChk_irT (.inl ⟨_, rfl⟩) (m₁ ▸ hy)
      (show flatChkE tExt s.funcs f.module f.locals.length ret labels _ (.callIndirect x y) = some o₁
        from hb _ hoa)
    obtain ⟨g₂, hlen⟩ := hC _ _ _ _ _ hcall g₁
    have hrs := hlen fi ps rs vs hfi hty hvs
    have hp' : ps.length ≤ stk₁.length := by omega
    obtain ⟨g, m, l, go, t⟩ := fwd_cont hg g₂ m₁ l₁
      (by rw [ho₁] at h2; convert h2 using 3; omega) (len_take_drop hrs hp') ihk
    refine ⟨g, m, l, go, fun rest => ?_⟩
    obtain ⟨o', d', e'⟩ := t rest
    have ha' := eq_of_trim_normal (t₁ rest).choose_spec.2
    have hargs' := (t₁ rest).choose_spec.1
    rw [ha', List.cons_append] at hargs'
    refine ⟨o', .callIndOk (s₂ := s₂) hargs' hres hfi hty hy ?_ hvs ?_, e'⟩
    · rwa [List.take_append_of_le_length hp']
    · rwa [take_drop_append hp']
  | @callIndRes s s₁ f f₁ stk stk₁ x y args es ad i hargs hres iha =>
    intro labels ret oc hg hc
    obtain ⟨o₁, h1, -⟩ := chk_consE.mp hc
    obtain ⟨oa, ha, -⟩ := chk1_opE h1
    obtain ⟨g₁, m₁, l₁, -, t₁⟩ := iha hg ha
    refine ⟨g₁, m₁, l₁, trivial, fun rest => ?_⟩
    have ha' := eq_of_trim_normal (t₁ rest).choose_spec.2
    have hargs' := (t₁ rest).choose_spec.1
    rw [ha', List.cons_append] at hargs'
    exact ⟨_, .callIndRes hargs' hres, rfl⟩
  | @callIndStop s s₁ s₂ f f₁ stk stk₁ x y args es ad i fa fi ps rs fl hargs hres hfi hty hy
      hcall hfl iha =>
    intro labels ret oc hg hc
    obtain ⟨o₁, h1, -⟩ := chk_consE.mp hc
    obtain ⟨oa, ha, hb⟩ := chk1_opE h1
    obtain ⟨g₁, m₁, l₁, go₁, t₁⟩ := iha hg ha
    have hoa : oa = some (stk₁.length + 1) := go₁
    obtain ⟨hp, -⟩ := flatChk_irT (.inl ⟨_, rfl⟩) (m₁ ▸ hy)
      (show flatChkE tExt s.funcs f.module f.locals.length ret labels _ (.callIndirect x y) = some o₁
        from hb _ hoa)
    have hp' : ps.length ≤ stk₁.length := by omega
    have hgo : GoodO labels ret oc (.flow fl) := by
      rcases fl with _ | _ | _ | _ | _ <;> trivial
    refine ⟨(hC _ _ _ _ _ hcall g₁).1, m₁, l₁, hgo, fun rest => ?_⟩
    have ha' := eq_of_trim_normal (t₁ rest).choose_spec.2
    have hargs' := (t₁ rest).choose_spec.1
    rw [ha', List.cons_append] at hargs'
    refine ⟨_, .callIndStop hargs' hres hfi hty hy ?_ hfl, ?_⟩
    · rwa [List.take_append_of_le_length hp']
    · rw [whiskO_abrupt (by rcases fl with _ | _ | _ | _ | _ <;> simp_all [POut.IsNormal,
        Flow.IsNormal, Flow.Abrupt])]
  | @callRefOk s s₁ s₂ f f₁ stk stk₁ vs y args es fa fi ps rs fl r hargs hfi hty hy hcall hvs hk
      iha ihk =>
    intro labels ret oc hg hc
    obtain ⟨o₁, h1, h2⟩ := chk_consE.mp hc
    obtain ⟨oa, ha, hb⟩ := chk1_opE h1
    obtain ⟨g₁, m₁, l₁, go₁, t₁⟩ := iha hg ha
    have hoa : oa = some (stk₁.length + 1) := go₁
    obtain ⟨hp, ho₁⟩ := flatChk_irT (.inr rfl) (m₁ ▸ hy)
      (show flatChkE tExt s.funcs f.module f.locals.length ret labels _ (.callRef y) = some o₁ from
        hb _ hoa)
    obtain ⟨g₂, hlen⟩ := hC _ _ _ _ _ hcall g₁
    have hrs := hlen fi ps rs vs hfi hty hvs
    have hp' : ps.length ≤ stk₁.length := by omega
    obtain ⟨g, m, l, go, t⟩ := fwd_cont hg g₂ m₁ l₁
      (by rw [ho₁] at h2; convert h2 using 3; omega) (len_take_drop hrs hp') ihk
    refine ⟨g, m, l, go, fun rest => ?_⟩
    obtain ⟨o', d', e'⟩ := t rest
    have ha' := eq_of_trim_normal (t₁ rest).choose_spec.2
    have hargs' := (t₁ rest).choose_spec.1
    rw [ha', List.cons_append] at hargs'
    refine ⟨o', .callRefOk (s₂ := s₂) hargs' hfi hty hy ?_ hvs ?_, e'⟩
    · rwa [List.take_append_of_le_length hp']
    · rwa [take_drop_append hp']
  | @callRefNull s s₁ f f₁ stk stk₁ y args es hargs iha =>
    intro labels ret oc hg hc
    obtain ⟨o₁, h1, -⟩ := chk_consE.mp hc
    obtain ⟨oa, ha, -⟩ := chk1_opE h1
    obtain ⟨g₁, m₁, l₁, -, t₁⟩ := iha hg ha
    refine ⟨g₁, m₁, l₁, trivial, fun rest => ?_⟩
    have ha' := eq_of_trim_normal (t₁ rest).choose_spec.2
    have hargs' := (t₁ rest).choose_spec.1
    rw [ha', List.cons_append] at hargs'
    exact ⟨_, .callRefNull hargs', rfl⟩
  | @callRefStop s s₁ s₂ f f₁ stk stk₁ y args es fa fi ps rs fl hargs hfi hty hy hcall hfl iha =>
    intro labels ret oc hg hc
    obtain ⟨o₁, h1, -⟩ := chk_consE.mp hc
    obtain ⟨oa, ha, hb⟩ := chk1_opE h1
    obtain ⟨g₁, m₁, l₁, go₁, t₁⟩ := iha hg ha
    have hoa : oa = some (stk₁.length + 1) := go₁
    obtain ⟨hp, -⟩ := flatChk_irT (.inr rfl) (m₁ ▸ hy)
      (show flatChkE tExt s.funcs f.module f.locals.length ret labels _ (.callRef y) = some o₁ from
        hb _ hoa)
    have hp' : ps.length ≤ stk₁.length := by omega
    have hgo : GoodO labels ret oc (.flow fl) := by
      rcases fl with _ | _ | _ | _ | _ <;> trivial
    refine ⟨(hC _ _ _ _ _ hcall g₁).1, m₁, l₁, hgo, fun rest => ?_⟩
    have ha' := eq_of_trim_normal (t₁ rest).choose_spec.2
    have hargs' := (t₁ rest).choose_spec.1
    rw [ha', List.cons_append] at hargs'
    refine ⟨_, .callRefStop hargs' hfi hty hy ?_ hfl, ?_⟩
    · rwa [List.take_append_of_le_length hp']
    · rw [whiskO_abrupt (by rcases fl with _ | _ | _ | _ | _ <;> simp_all [POut.IsNormal,
        Flow.IsNormal, Flow.Abrupt])]
  | @tail s s₁ f f₁ stk stk₁ i args es fa fi ps rs hargs hres hfi hty hy iha =>
    intro labels ret oc hg hc
    obtain ⟨o₁, h1, -⟩ := chk_consE.mp hc
    obtain ⟨oa, ha, hb⟩ := chk1_opE h1
    obtain ⟨g₁, m₁, l₁, go₁, t₁⟩ := iha hg ha
    have hoa : oa = some stk₁.length := go₁
    have hck := hb _ hoa
    rw [flatChkE_eh_tail hres, ← flatChkE_eq (good_funcs hg g₁) m₁ l₁] at hck
    obtain ⟨hp, -, -⟩ := flatChk_tailForm (tExt_tail hres hfi hty hy) hck
    have htp := tailRes_pop hres
    refine ⟨g₁, m₁, l₁, trivial, fun rest => ?_⟩
    have ha' := eq_of_trim_normal (t₁ rest).choose_spec.2
    have hargs' := (t₁ rest).choose_spec.1
    rw [ha'] at hargs'
    have hres' := tailRes_append (rest := rest) hres
    rw [← List.drop_append_of_le_length htp] at hres'
    refine ⟨_, .tail hargs' hres' hfi hty hy, ?_⟩
    rw [List.drop_append_of_le_length htp,
      List.take_append_of_le_length (by simp only [List.length_drop]; omega)]
    rfl
  | @tailRes s s₁ f f₁ stk stk₁ i args es hargs hres iha =>
    intro labels ret oc hg hc
    obtain ⟨o₁, h1, -⟩ := chk_consE.mp hc
    obtain ⟨oa, ha, -⟩ := chk1_opE h1
    obtain ⟨g₁, m₁, l₁, -, t₁⟩ := iha hg ha
    refine ⟨g₁, m₁, l₁, trivial, fun rest => ?_⟩
    have ha' := eq_of_trim_normal (t₁ rest).choose_spec.2
    have hargs' := (t₁ rest).choose_spec.1
    rw [ha'] at hargs'
    exact ⟨_, .tailRes hargs' (tailRes_append_none hres), rfl⟩
  | @throw s s₁ f f₁ stk stk₁ x args es ta ti ts hargs ht he hn iha =>
    intro labels ret oc hg hc
    obtain ⟨o₁, h1, -⟩ := chk_consE.mp hc
    obtain ⟨oa, ha, -⟩ := chk1_opE h1
    obtain ⟨g₁, m₁, l₁, -, t₁⟩ := iha hg ha
    have g₂ : Γ.Good (s₁.addExn ⟨ta, (stk₁.take ts.length).reverse⟩) :=
      ⟨g₁.1, tagsOk_throw g₁.2 ht he (by simp; omega)⟩
    refine ⟨g₂, m₁, l₁, trivial, fun rest => ?_⟩
    have ha' := eq_of_trim_normal (t₁ rest).choose_spec.2
    have hargs' := (t₁ rest).choose_spec.1
    rw [ha'] at hargs'
    have hd := EvalOXP.throw (es := es) hargs' ht he (by simp; omega)
    rw [List.take_append_of_le_length hn] at hd
    exact ⟨_, hd, rfl⟩
  | @throwRefNull s s₁ f f₁ stk stk₁ args es hargs iha =>
    intro labels ret oc hg hc
    obtain ⟨o₁, h1, -⟩ := chk_consE.mp hc
    obtain ⟨oa, ha, -⟩ := chk1_opE h1
    obtain ⟨g₁, m₁, l₁, -, t₁⟩ := iha hg ha
    refine ⟨g₁, m₁, l₁, trivial, fun rest => ?_⟩
    have ha' := eq_of_trim_normal (t₁ rest).choose_spec.2
    have hargs' := (t₁ rest).choose_spec.1
    rw [ha', List.cons_append] at hargs'
    exact ⟨_, .throwRefNull hargs', rfl⟩
  | @throwRefExn s s₁ f f₁ stk stk₁ a args es hargs iha =>
    intro labels ret oc hg hc
    obtain ⟨o₁, h1, -⟩ := chk_consE.mp hc
    obtain ⟨oa, ha, -⟩ := chk1_opE h1
    obtain ⟨g₁, m₁, l₁, -, t₁⟩ := iha hg ha
    refine ⟨g₁, m₁, l₁, trivial, fun rest => ?_⟩
    have ha' := eq_of_trim_normal (t₁ rest).choose_spec.2
    have hargs' := (t₁ rest).choose_spec.1
    rw [ha', List.cons_append] at hargs'
    exact ⟨_, .throwRefExn hargs', rfl⟩
  | @tryOk s s₁ f f₁ stk vs bt cs body es np nr fl r har hbody hvs hk ihb ihk =>
    intro labels ret oc hg hc
    obtain ⟨-, -, -, hle, hends, h2⟩ := arity_try_pre har hc
    obtain ⟨ob, hob, hob'⟩ := endsAt_eqE hends
    have hlen : (stk.take np).length = np := by simp; omega
    obtain ⟨g₁, m₁, l₁, go₁, -⟩ := ihb hg (by rw [hlen]; exact hob)
    have hnr := goodO_blockVals go₁ hob' hvs
    obtain ⟨g, m, l, go, t⟩ := fwd_cont hg g₁ m₁ l₁ h2 (len_take_drop hnr hle) ihk
    refine ⟨g, m, l, go, fun rest => ?_⟩
    obtain ⟨o', d', e'⟩ := t rest
    refine ⟨o', .tryOk (s₁ := s₁) (f₁ := f₁) har ?_ hvs ?_, e'⟩
    · rwa [List.take_append_of_le_length hle]
    · rwa [take_drop_append hle]
  | @tryBrk s s₁ f f₁ stk vs bt cs body es np nr k har hbody ihb =>
    intro labels ret oc hg hc
    obtain ⟨-, -, -, hle, hends, -⟩ := arity_try_pre har hc
    obtain ⟨ob, hob, -⟩ := endsAt_eqE hends
    have hlen : (stk.take np).length = np := by simp; omega
    obtain ⟨g₁, m₁, l₁, go₁, -⟩ := ihb hg (by rw [hlen]; exact hob)
    refine ⟨g₁, m₁, l₁, goodO_brk_succ go₁, fun rest => ⟨_, .tryBrk har ?_, rfl⟩⟩
    rwa [List.take_append_of_le_length hle]
  | @tryEsc s s₁ f f₁ stk bt cs body es np nr o har hbody ho hnt ihb =>
    intro labels ret oc hg hc
    obtain ⟨-, -, -, hle, hends, -⟩ := arity_try_pre har hc
    obtain ⟨ob, hob, -⟩ := endsAt_eqE hends
    have hlen : (stk.take np).length = np := by simp; omega
    obtain ⟨g₁, m₁, l₁, go₁, -⟩ := ihb hg (by rw [hlen]; exact hob)
    refine ⟨g₁, m₁, l₁, goodO_escape go₁ ho, fun rest => ⟨_, .tryEsc har ?_ ho hnt, by rw [whiskO_abrupt (notNormal_of_escapes ho)]⟩⟩
    rwa [List.take_append_of_le_length hle]
  | @tryCatch s s₁ f f₁ stk us bt cs body es np nr a l har hbody hcs ihb =>
    intro labels ret oc hg hc
    obtain ⟨ns, hns, hok, hle, hends, -⟩ := arity_try_pre har hc
    obtain ⟨ob, hob, -⟩ := endsAt_eqE hends
    have hlen : (stk.take np).length = np := by simp; omega
    obtain ⟨g₁, m₁, l₁, -, -⟩ := ihb hg (by rw [hlen]; exact hob)
    rw [← m₁] at hns
    obtain ⟨n, hn, hle'⟩ := catches_count g₁.2.2 hcs hns hok
    have hgo : GoodO labels ret oc (.flow (.brk l.toNat (us.reverse ++ stk.drop np))) :=
      ⟨n, hn, by simp; omega⟩
    refine ⟨g₁, m₁, l₁, hgo, fun rest => ?_⟩
    have hd := EvalOXP.tryCatch (es := es) (stk := stk ++ rest) har (by
      rwa [List.take_append_of_le_length hle]) hcs
    refine ⟨_, hd, ?_⟩
    rw [List.drop_append_of_le_length hle, ← List.append_assoc]
    exact trimO_brk_append ⟨n, hn, by simp; omega⟩
  | @tryRethrow s s₁ f f₁ stk bt cs body es np nr a har hbody hcs ihb =>
    intro labels ret oc hg hc
    obtain ⟨-, -, -, hle, hends, -⟩ := arity_try_pre har hc
    obtain ⟨ob, hob, -⟩ := endsAt_eqE hends
    have hlen : (stk.take np).length = np := by simp; omega
    obtain ⟨g₁, m₁, l₁, -, -⟩ := ihb hg (by rw [hlen]; exact hob)
    refine ⟨g₁, m₁, l₁, trivial, fun rest => ⟨_, .tryRethrow har ?_ hcs, rfl⟩⟩
    rwa [List.take_append_of_le_length hle]

end Silmaril.Proofs.Wasm.Abstract.ExposePTyped
