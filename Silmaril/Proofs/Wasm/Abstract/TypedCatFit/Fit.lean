module

public import Silmaril.Wasm.Abstract.TypedCat.Defs
public import Silmaril.Proofs.Wasm.Abstract.ExposePTyped.Fwd

/-!
Proofs for `Silmaril.Wasm.Abstract.TypedCatFit.Thms`: **checked code calls with exactly the
callee's parameter count.** A run of `EvalOXP C` of checked code from a store agreeing with the
context is a run of `EvalOXP (fitP C)`, provided the fitting answers respect arities
(`ArityResp Γ (fitP C)`): by induction on the run, carrying the result invariant of the check
(`GoodO`, as `ExposePTyped.Fwd`). At every call site the check has at least the callee's parameter
count on the stack (`flatChk_call`, `flatChk_irT`), so the arguments `stk₁.take ps.length` have
exactly that length; the fitting answer then returns at least the callee's result count, which
keeps the check's height for the continuation.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.TypedCatFit

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Interp Silmaril.Wasm.Abstract.ExposePStruct Silmaril.Wasm.Abstract.ExposePTyped
open Silmaril.Wasm.Abstract.CallX Silmaril.Wasm.Abstract.CallXP
open Silmaril.Wasm.Abstract.CallXT (typeArity tailAnn)
open Silmaril.Wasm.Abstract.TypedCat
open Silmaril.Proofs.Wasm.Abstract.ExposePTyped

variable {H : Type}

/-- The arguments a call takes off a stack holding at least the callee's parameter count fit. -/
theorem argsFit_take {s : Store H} {a : Nat} {fi : FuncInst H} {ps rs : List Validation.CValType}
    {stk : List Val} (hp : ps.length ≤ stk.length) (hfi : s.funcs[a]? = some fi)
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) :
    ArgsFit s a (stk.take ps.length).reverse := by
  intro fi' ps' rs' hfi' hty'
  rw [hfi] at hfi'
  cases hfi'
  rw [hty, Option.some.injEq, Prod.mk.injEq] at hty'
  obtain ⟨rfl, rfl⟩ := hty'
  simp only [List.length_reverse, List.length_take]
  omega

theorem fitP_mk {C : Abstract.CallRel H} {s : Store H} {a : Nat} {args : List Val}
    {out : Store H × Flow} (h : C s a args out) (hf : ArgsFit s a args) :
    fitP C s a args out :=
  And.intro h hf

/-- The fitting statement for one run. -/
def FitRun (Γ : Ctx H) (C : Abstract.CallRel H) (s : Store H) (f : Frame) (stk : List Val)
    (es : List BExpr) (r : Store H × Frame × POut) : Prop :=
  ∀ {labels : List Nat} {ret : Nat} {oc : Option Nat}, Γ.Good s →
    chkE (ehExt Γ.tags) s.funcs f.module f.locals.length ret labels (some stk.length) es = some oc →
    Γ.Good r.1 ∧ r.2.1.module = f.module ∧ r.2.1.locals.length = f.locals.length ∧
      GoodO labels ret oc r.2.2 ∧ EvalOXP (fitP C) s f stk es r

variable {Γ : Ctx H} {C : Abstract.CallRel H}

/-- The continuation of a run, its check moved to the state it starts in. -/
theorem fit_cont {s s₁ : Store H} {f f₁ : Frame} {stk' : List Val} {es : List BExpr}
    {r : Store H × Frame × POut} {labels : List Nat} {ret : Nat} {oc : Option Nat} {n : Nat}
    (hg : Γ.Good s) (hg₁ : Γ.Good s₁) (hm : f₁.module = f.module)
    (hl : f₁.locals.length = f.locals.length)
    (hc : chkE (ehExt Γ.tags) s.funcs f.module f.locals.length ret labels (some n) es = some oc)
    (hn : stk'.length = n) (ih : FitRun Γ C s₁ f₁ stk' es r) :
    Γ.Good r.1 ∧ r.2.1.module = f.module ∧ r.2.1.locals.length = f.locals.length ∧
      GoodO labels ret oc r.2.2 ∧ EvalOXP (fitP C) s₁ f₁ stk' es r := by
  have hc' : chkE (ehExt Γ.tags) s₁.funcs f₁.module f₁.locals.length ret labels
      (some stk'.length) es = some oc := by
    rw [chk_eq (good_funcs hg hg₁) hm hl, hn]; exact hc
  obtain ⟨g, m, l, go, t⟩ := ih hg₁ hc'
  exact ⟨g, m.trans hm, l.trans hl, go, t⟩

/-- **Checked runs make only fitting calls.** -/
theorem evalOXP_fit (hC : ArityResp Γ (fitP C)) {s : Store H} {f : Frame} {stk : List Val}
    {es : List BExpr} {r : Store H × Frame × POut} (d : EvalOXP C s f stk es r) :
    FitRun Γ C s f stk es r := by
  induction d with
  | nil =>
    intro labels ret oc hg hc
    simp only [chk_nilE, Option.some.injEq] at hc
    subst hc
    exact ⟨hg, rfl, rfl, rfl, .nil⟩
  | argsAbort _ ho iha =>
    intro labels ret oc hg hc
    obtain ⟨o₁, h1, -⟩ := chk_consE.mp hc
    obtain ⟨oa, ha, -⟩ := chk1_opE h1
    obtain ⟨g, m, l, go, d'⟩ := iha hg ha
    exact ⟨g, m, l, goodO_abrupt ho go, .argsAbort d' ho⟩
  | @callOk s s₁ s₂ f f₁ stk stk₁ vs x args es a fi ps rs fl r hargs hfi hty hcall hvs hk iha
      ihk =>
    intro labels ret oc hg hc
    obtain ⟨o₁, h1, h2⟩ := chk_consE.mp hc
    obtain ⟨oa, ha, hb⟩ := chk1_opE h1
    obtain ⟨g₁, m₁, l₁, go₁, d₁⟩ := iha hg ha
    have hoa : oa = some stk₁.length := go₁
    obtain ⟨p, q, hpq, hp, ho₁⟩ := flatChk_call (flatChkE_call (hb _ hoa))
    have hpq' := callArity_eq hfi hty
    rw [good_funcs hg g₁, m₁, hpq, Option.some.injEq, Prod.mk.injEq] at hpq'
    obtain ⟨rfl, rfl⟩ := hpq'
    have hcall' := fitP_mk hcall (argsFit_take hp (funcs_of_func? hfi) hty)
    obtain ⟨g₂, hlen⟩ := hC _ _ _ _ _ hcall' g₁
    have hrs := hlen fi ps rs vs (funcs_of_func? hfi) hty hvs
    obtain ⟨g, m, l, go, dk⟩ := fit_cont hg g₂ m₁ l₁ (ho₁ ▸ h2) (len_take_drop hrs hp) ihk
    exact ⟨g, m, l, go, .callOk d₁ hfi hty hcall' hvs dk⟩
  | @callTrap s s₁ s₂ f f₁ stk stk₁ x args es a fi ps rs hargs hfi hty hcall iha =>
    intro labels ret oc hg hc
    obtain ⟨o₁, h1, -⟩ := chk_consE.mp hc
    obtain ⟨oa, ha, hb⟩ := chk1_opE h1
    obtain ⟨g₁, m₁, l₁, go₁, d₁⟩ := iha hg ha
    have hoa : oa = some stk₁.length := go₁
    obtain ⟨p, q, hpq, hp, -⟩ := flatChk_call (flatChkE_call (hb _ hoa))
    have hpq' := callArity_eq hfi hty
    rw [good_funcs hg g₁, m₁, hpq, Option.some.injEq, Prod.mk.injEq] at hpq'
    obtain ⟨rfl, rfl⟩ := hpq'
    have hcall' := fitP_mk hcall (argsFit_take hp (funcs_of_func? hfi) hty)
    exact ⟨(hC _ _ _ _ _ hcall' g₁).1, m₁, l₁, trivial, .callTrap d₁ hfi hty hcall'⟩
  | @callThrow s s₁ s₂ f f₁ stk stk₁ x args es a fi ps rs t hargs hfi hty hcall iha =>
    intro labels ret oc hg hc
    obtain ⟨o₁, h1, -⟩ := chk_consE.mp hc
    obtain ⟨oa, ha, hb⟩ := chk1_opE h1
    obtain ⟨g₁, m₁, l₁, go₁, d₁⟩ := iha hg ha
    have hoa : oa = some stk₁.length := go₁
    obtain ⟨p, q, hpq, hp, -⟩ := flatChk_call (flatChkE_call (hb _ hoa))
    have hpq' := callArity_eq hfi hty
    rw [good_funcs hg g₁, m₁, hpq, Option.some.injEq, Prod.mk.injEq] at hpq'
    obtain ⟨rfl, rfl⟩ := hpq'
    have hcall' := fitP_mk hcall (argsFit_take hp (funcs_of_func? hfi) hty)
    exact ⟨(hC _ _ _ _ _ hcall' g₁).1, m₁, l₁, trivial, .callThrow d₁ hfi hty hcall'⟩
  | @opOk s s₁ s₂ f f₁ f₂ stk stk₁ stk₂ i args es r hi hargs hflat hk iha ihk =>
    intro labels ret oc hg hc
    obtain ⟨o₁, h1, h2⟩ := chk_consE.mp hc
    obtain ⟨oa, ha, hb⟩ := chk1_opE h1
    obtain ⟨g₁, m₁, l₁, go₁, d₁⟩ := iha hg ha
    have hoa : oa = some stk₁.length := go₁
    have hck := hb _ hoa
    have hck' : flatChkE (ehExt Γ.tags) s₁.funcs f₁.module f₁.locals.length ret labels
        stk₁.length i = some o₁ := by
      rw [flatChkE_eq (good_funcs hg g₁) m₁ l₁]; exact hck
    obtain ⟨ho, inv⟩ := flat_normal (ext := ehExt Γ.tags) hflat (flatChk_of_evalFlat hflat hck')
    have g₂ : Γ.Good s₂ :=
      ⟨(Abstract.XRecursion.evalFlat_funcs hflat).trans g₁.1, TagsOk.evalFlat g₁.2 hflat⟩
    obtain ⟨g, m, l, go, dk⟩ :=
      fit_cont hg g₂ (inv.2.1.trans m₁) (inv.2.2.trans l₁) (ho ▸ h2) rfl ihk
    exact ⟨g, m, l, go, .opOk hi d₁ hflat dk⟩
  | @opStop s s₁ s₂ f f₁ f₂ stk stk₁ i args es fl hi hargs hflat hfl iha =>
    intro labels ret oc hg hc
    obtain ⟨o₁, h1, -⟩ := chk_consE.mp hc
    obtain ⟨oa, ha, hb⟩ := chk1_opE h1
    obtain ⟨g₁, m₁, l₁, go₁, d₁⟩ := iha hg ha
    have hoa : oa = some stk₁.length := go₁
    have hck := hb _ hoa
    have hck' : flatChkE (ehExt Γ.tags) s₁.funcs f₁.module f₁.locals.length ret labels
        stk₁.length i = some o₁ := by
      rw [flatChkE_eq (good_funcs hg g₁) m₁ l₁]; exact hck
    obtain ⟨hok, inv⟩ :=
      flat_abrupt (ext := ehExt Γ.tags) hflat hfl (flatChk_of_evalFlat hflat hck') oc
    have g₂ : Γ.Good s₂ :=
      ⟨(Abstract.XRecursion.evalFlat_funcs hflat).trans g₁.1, TagsOk.evalFlat g₁.2 hflat⟩
    exact ⟨g₂, inv.2.1.trans m₁, inv.2.2.trans l₁, goodO_of_flowOk hok, .opStop hi d₁ hflat hfl⟩
  | @blockOk s s₁ f f₁ stk vs bt body es np nr fl r har hbody hvs hk ihb ihk =>
    intro labels ret oc hg hc
    obtain ⟨o₁, h1, h2⟩ := chk_consE.mp hc
    obtain ⟨np', nr', hba, hle, hends, ho₁⟩ := chk1_blockE h1
    rw [← arity_eq, har, Option.some.injEq, Prod.mk.injEq] at hba
    obtain ⟨rfl, rfl⟩ := hba
    obtain ⟨ob, hob, hob'⟩ := endsAt_eqE hends
    have hlen : (stk.take np).length = np := by simp; omega
    obtain ⟨g₁, m₁, l₁, go₁, db⟩ := ihb hg (by rw [hlen]; exact hob)
    have hnr := goodO_blockVals go₁ hob' hvs
    obtain ⟨g, m, l, go, dk⟩ := fit_cont hg g₁ m₁ l₁ (ho₁ ▸ h2) (len_take_drop hnr hle) ihk
    exact ⟨g, m, l, go, .blockOk har db hvs dk⟩
  | @blockBrk s s₁ f f₁ stk vs bt body es np nr k har hbody ihb =>
    intro labels ret oc hg hc
    obtain ⟨o₁, h1, -⟩ := chk_consE.mp hc
    obtain ⟨np', nr', hba, hle, hends, -⟩ := chk1_blockE h1
    rw [← arity_eq, har, Option.some.injEq, Prod.mk.injEq] at hba
    obtain ⟨rfl, rfl⟩ := hba
    obtain ⟨ob, hob, -⟩ := endsAt_eqE hends
    have hlen : (stk.take np).length = np := by simp; omega
    obtain ⟨g₁, m₁, l₁, go₁, db⟩ := ihb hg (by rw [hlen]; exact hob)
    exact ⟨g₁, m₁, l₁, goodO_brk_succ go₁, .blockBrk har db⟩
  | @blockEsc s s₁ f f₁ stk bt body es np nr o har hbody ho ihb =>
    intro labels ret oc hg hc
    obtain ⟨o₁, h1, -⟩ := chk_consE.mp hc
    obtain ⟨np', nr', hba, hle, hends, -⟩ := chk1_blockE h1
    rw [← arity_eq, har, Option.some.injEq, Prod.mk.injEq] at hba
    obtain ⟨rfl, rfl⟩ := hba
    obtain ⟨ob, hob, -⟩ := endsAt_eqE hends
    have hlen : (stk.take np).length = np := by simp; omega
    obtain ⟨g₁, m₁, l₁, go₁, db⟩ := ihb hg (by rw [hlen]; exact hob)
    exact ⟨g₁, m₁, l₁, goodO_escape go₁ ho, .blockEsc har db ho⟩
  | @loopOk s s₁ f f₁ stk vs bt body es np nr r har hbody hk ihb ihk =>
    intro labels ret oc hg hc
    obtain ⟨o₁, h1, h2⟩ := chk_consE.mp hc
    obtain ⟨np', nr', hba, hle, hends, ho₁⟩ := chk1_loopE h1
    rw [← arity_eq, har, Option.some.injEq, Prod.mk.injEq] at hba
    obtain ⟨rfl, rfl⟩ := hba
    obtain ⟨ob, hob, hob'⟩ := endsAt_eqE hends
    have hlen : (stk.take np).length = np := by simp; omega
    obtain ⟨g₁, m₁, l₁, go₁, db⟩ := ihb hg (by rw [hlen]; exact hob)
    have hnr := (goodO_normal go₁ hob').ge
    obtain ⟨g, m, l, go, dk⟩ := fit_cont hg g₁ m₁ l₁ (ho₁ ▸ h2) (len_take_drop hnr hle) ihk
    exact ⟨g, m, l, go, .loopOk har db dk⟩
  | @loopBack s s₁ f f₁ stk vs bt body es np nr r har hbody hk ihb ihk =>
    intro labels ret oc hg hc
    obtain ⟨o₁, h1, -⟩ := chk_consE.mp hc
    obtain ⟨np', nr', hba, hle, hends, -⟩ := chk1_loopE h1
    rw [← arity_eq, har, Option.some.injEq, Prod.mk.injEq] at hba
    obtain ⟨rfl, rfl⟩ := hba
    obtain ⟨ob, hob, -⟩ := endsAt_eqE hends
    have hlen : (stk.take np).length = np := by simp; omega
    obtain ⟨g₁, m₁, l₁, go₁, db⟩ := ihb hg (by rw [hlen]; exact hob)
    have hnp : np ≤ vs.length := by
      obtain ⟨n, hn, hle'⟩ := go₁
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hn
      exact hn ▸ hle'
    have hlen' : (vs.take np ++ stk.drop np).length = stk.length := by
      rw [len_take_drop hnp hle]; omega
    obtain ⟨g, m, l, go, dk⟩ := fit_cont hg g₁ m₁ l₁ hc hlen' ihk
    exact ⟨g, m, l, go, .loopBack har db dk⟩
  | @loopBrk s s₁ f f₁ stk vs bt body es np nr k har hbody ihb =>
    intro labels ret oc hg hc
    obtain ⟨o₁, h1, -⟩ := chk_consE.mp hc
    obtain ⟨np', nr', hba, hle, hends, -⟩ := chk1_loopE h1
    rw [← arity_eq, har, Option.some.injEq, Prod.mk.injEq] at hba
    obtain ⟨rfl, rfl⟩ := hba
    obtain ⟨ob, hob, -⟩ := endsAt_eqE hends
    have hlen : (stk.take np).length = np := by simp; omega
    obtain ⟨g₁, m₁, l₁, go₁, db⟩ := ihb hg (by rw [hlen]; exact hob)
    exact ⟨g₁, m₁, l₁, goodO_brk_succ go₁, .loopBrk har db⟩
  | @loopEsc s s₁ f f₁ stk bt body es np nr o har hbody ho ihb =>
    intro labels ret oc hg hc
    obtain ⟨o₁, h1, -⟩ := chk_consE.mp hc
    obtain ⟨np', nr', hba, hle, hends, -⟩ := chk1_loopE h1
    rw [← arity_eq, har, Option.some.injEq, Prod.mk.injEq] at hba
    obtain ⟨rfl, rfl⟩ := hba
    obtain ⟨ob, hob, -⟩ := endsAt_eqE hends
    have hlen : (stk.take np).length = np := by simp; omega
    obtain ⟨g₁, m₁, l₁, go₁, db⟩ := ihb hg (by rw [hlen]; exact hob)
    exact ⟨g₁, m₁, l₁, goodO_escape go₁ ho, .loopEsc har db ho⟩
  | @ifOk s s₁ s₂ f f₁ f₂ stk stk₁ vs cv b bt c t el es np nr fl r hc' hb har harm hvs hk ihc
      iharm ihk =>
    intro labels ret oc hg hc
    obtain ⟨o₁, h1, h2⟩ := chk_consE.mp hc
    obtain ⟨occ, hcc, hrest⟩ := chk1_ifE h1
    obtain ⟨g₁, m₁, l₁, go₁, dc⟩ := ihc hg hcc
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
    obtain ⟨g₂, m₂, l₂, go₂, darm⟩ := iharm g₁ (by rw [hlen]; exact hob)
    have hnr := goodO_blockVals go₂ hob' hvs
    obtain ⟨g, m, l, go, dk⟩ := fit_cont hg g₂ (m₂.trans m₁) (l₂.trans l₁)
      (by rw [ho₁] at h2; convert h2 using 3; omega) (len_take_drop hnr hle') ihk
    exact ⟨g, m, l, go, .ifOk dc hb har darm hvs dk⟩
  | @ifBrk s s₁ s₂ f f₁ f₂ stk stk₁ vs cv b bt c t el es np nr k hc' hb har harm ihc iharm =>
    intro labels ret oc hg hc
    obtain ⟨o₁, h1, -⟩ := chk_consE.mp hc
    obtain ⟨occ, hcc, hrest⟩ := chk1_ifE h1
    obtain ⟨g₁, m₁, l₁, go₁, dc⟩ := ihc hg hcc
    have hocc : occ = some (stk₁.length + 1) := go₁
    obtain ⟨np', nr', hba, hle, het, hee, -⟩ := hrest _ hocc
    rw [← m₁, ← arity_eq, har, Option.some.injEq, Prod.mk.injEq] at hba
    obtain ⟨rfl, rfl⟩ := hba
    have hends : endsAt (chkE (ehExt Γ.tags) s₁.funcs f₁.module f₁.locals.length ret
        (nr :: labels) (some np) (if b then t else el)) nr = true := by
      rw [chk_eq (good_funcs hg g₁) m₁ l₁]; cases b <;> assumption
    obtain ⟨ob, hob, -⟩ := endsAt_eqE hends
    have hlen : (stk₁.take np).length = np := by simp; omega
    obtain ⟨g₂, m₂, l₂, go₂, darm⟩ := iharm g₁ (by rw [hlen]; exact hob)
    exact ⟨g₂, m₂.trans m₁, l₂.trans l₁, goodO_brk_succ go₂, .ifBrk dc hb har darm⟩
  | @ifEsc s s₁ s₂ f f₁ f₂ stk stk₁ cv b bt c t el es np nr o hc' hb har harm ho ihc iharm =>
    intro labels ret oc hg hc
    obtain ⟨o₁, h1, -⟩ := chk_consE.mp hc
    obtain ⟨occ, hcc, hrest⟩ := chk1_ifE h1
    obtain ⟨g₁, m₁, l₁, go₁, dc⟩ := ihc hg hcc
    have hocc : occ = some (stk₁.length + 1) := go₁
    obtain ⟨np', nr', hba, hle, het, hee, -⟩ := hrest _ hocc
    rw [← m₁, ← arity_eq, har, Option.some.injEq, Prod.mk.injEq] at hba
    obtain ⟨rfl, rfl⟩ := hba
    have hends : endsAt (chkE (ehExt Γ.tags) s₁.funcs f₁.module f₁.locals.length ret
        (nr :: labels) (some np) (if b then t else el)) nr = true := by
      rw [chk_eq (good_funcs hg g₁) m₁ l₁]; cases b <;> assumption
    obtain ⟨ob, hob, -⟩ := endsAt_eqE hends
    have hlen : (stk₁.take np).length = np := by simp; omega
    obtain ⟨g₂, m₂, l₂, go₂, darm⟩ := iharm g₁ (by rw [hlen]; exact hob)
    exact ⟨g₂, m₂.trans m₁, l₂.trans l₁, goodO_escape go₂ ho, .ifEsc dc hb har darm ho⟩
  | ifAbort _ ho ihc =>
    intro labels ret oc hg hc
    obtain ⟨o₁, h1, -⟩ := chk_consE.mp hc
    obtain ⟨occ, hcc, -⟩ := chk1_ifE h1
    obtain ⟨g, m, l, go, dc⟩ := ihc hg hcc
    exact ⟨g, m, l, goodO_abrupt ho go, .ifAbort dc ho⟩
  | @callIndOk s s₁ s₂ f f₁ stk stk₁ vs x y args es ad i fa fi ps rs fl r hargs hres hfi hty hy
      hcall hvs hk iha ihk =>
    intro labels ret oc hg hc
    obtain ⟨o₁, h1, h2⟩ := chk_consE.mp hc
    obtain ⟨oa, ha, hb⟩ := chk1_opE h1
    obtain ⟨g₁, m₁, l₁, go₁, d₁⟩ := iha hg ha
    have hoa : oa = some (stk₁.length + 1) := go₁
    obtain ⟨hp, ho₁⟩ := flatChk_irT (.inl ⟨_, rfl⟩) (m₁ ▸ hy)
      (show flatChkE tExt s.funcs f.module f.locals.length ret labels _ (.callIndirect x y) = some o₁
        from hb _ hoa)
    have hp' : ps.length ≤ stk₁.length := by omega
    have hcall' := fitP_mk hcall (argsFit_take hp' hfi hty)
    obtain ⟨g₂, hlen⟩ := hC _ _ _ _ _ hcall' g₁
    have hrs := hlen fi ps rs vs hfi hty hvs
    obtain ⟨g, m, l, go, dk⟩ := fit_cont hg g₂ m₁ l₁
      (by rw [ho₁] at h2; convert h2 using 3; omega) (len_take_drop hrs hp') ihk
    exact ⟨g, m, l, go, .callIndOk d₁ hres hfi hty hy hcall' hvs dk⟩
  | @callIndRes s s₁ f f₁ stk stk₁ x y args es ad i hargs hres iha =>
    intro labels ret oc hg hc
    obtain ⟨o₁, h1, -⟩ := chk_consE.mp hc
    obtain ⟨oa, ha, -⟩ := chk1_opE h1
    obtain ⟨g₁, m₁, l₁, -, d₁⟩ := iha hg ha
    exact ⟨g₁, m₁, l₁, trivial, .callIndRes d₁ hres⟩
  | @callIndStop s s₁ s₂ f f₁ stk stk₁ x y args es ad i fa fi ps rs fl hargs hres hfi hty hy
      hcall hfl iha =>
    intro labels ret oc hg hc
    obtain ⟨o₁, h1, -⟩ := chk_consE.mp hc
    obtain ⟨oa, ha, hb⟩ := chk1_opE h1
    obtain ⟨g₁, m₁, l₁, go₁, d₁⟩ := iha hg ha
    have hoa : oa = some (stk₁.length + 1) := go₁
    obtain ⟨hp, -⟩ := flatChk_irT (.inl ⟨_, rfl⟩) (m₁ ▸ hy)
      (show flatChkE tExt s.funcs f.module f.locals.length ret labels _ (.callIndirect x y) = some o₁
        from hb _ hoa)
    have hp' : ps.length ≤ stk₁.length := by omega
    have hcall' := fitP_mk hcall (argsFit_take hp' hfi hty)
    have hgo : GoodO labels ret oc (.flow fl) := by
      rcases fl with _ | _ | _ | _ | _ <;> trivial
    exact ⟨(hC _ _ _ _ _ hcall' g₁).1, m₁, l₁, hgo, .callIndStop d₁ hres hfi hty hy hcall' hfl⟩
  | @callRefOk s s₁ s₂ f f₁ stk stk₁ vs y args es fa fi ps rs fl r hargs hfi hty hy hcall hvs hk
      iha ihk =>
    intro labels ret oc hg hc
    obtain ⟨o₁, h1, h2⟩ := chk_consE.mp hc
    obtain ⟨oa, ha, hb⟩ := chk1_opE h1
    obtain ⟨g₁, m₁, l₁, go₁, d₁⟩ := iha hg ha
    have hoa : oa = some (stk₁.length + 1) := go₁
    obtain ⟨hp, ho₁⟩ := flatChk_irT (.inr rfl) (m₁ ▸ hy)
      (show flatChkE tExt s.funcs f.module f.locals.length ret labels _ (.callRef y) = some o₁ from
        hb _ hoa)
    have hp' : ps.length ≤ stk₁.length := by omega
    have hcall' := fitP_mk hcall (argsFit_take hp' hfi hty)
    obtain ⟨g₂, hlen⟩ := hC _ _ _ _ _ hcall' g₁
    have hrs := hlen fi ps rs vs hfi hty hvs
    obtain ⟨g, m, l, go, dk⟩ := fit_cont hg g₂ m₁ l₁
      (by rw [ho₁] at h2; convert h2 using 3; omega) (len_take_drop hrs hp') ihk
    exact ⟨g, m, l, go, .callRefOk d₁ hfi hty hy hcall' hvs dk⟩
  | @callRefNull s s₁ f f₁ stk stk₁ y args es hargs iha =>
    intro labels ret oc hg hc
    obtain ⟨o₁, h1, -⟩ := chk_consE.mp hc
    obtain ⟨oa, ha, -⟩ := chk1_opE h1
    obtain ⟨g₁, m₁, l₁, -, d₁⟩ := iha hg ha
    exact ⟨g₁, m₁, l₁, trivial, .callRefNull d₁⟩
  | @callRefStop s s₁ s₂ f f₁ stk stk₁ y args es fa fi ps rs fl hargs hfi hty hy hcall hfl iha =>
    intro labels ret oc hg hc
    obtain ⟨o₁, h1, -⟩ := chk_consE.mp hc
    obtain ⟨oa, ha, hb⟩ := chk1_opE h1
    obtain ⟨g₁, m₁, l₁, go₁, d₁⟩ := iha hg ha
    have hoa : oa = some (stk₁.length + 1) := go₁
    obtain ⟨hp, -⟩ := flatChk_irT (.inr rfl) (m₁ ▸ hy)
      (show flatChkE tExt s.funcs f.module f.locals.length ret labels _ (.callRef y) = some o₁ from
        hb _ hoa)
    have hp' : ps.length ≤ stk₁.length := by omega
    have hcall' := fitP_mk hcall (argsFit_take hp' hfi hty)
    have hgo : GoodO labels ret oc (.flow fl) := by
      rcases fl with _ | _ | _ | _ | _ <;> trivial
    exact ⟨(hC _ _ _ _ _ hcall' g₁).1, m₁, l₁, hgo, .callRefStop d₁ hfi hty hy hcall' hfl⟩
  | @tail s s₁ f f₁ stk stk₁ i args es fa fi ps rs hargs hres hfi hty hy iha =>
    intro labels ret oc hg hc
    obtain ⟨o₁, h1, -⟩ := chk_consE.mp hc
    obtain ⟨oa, ha, -⟩ := chk1_opE h1
    obtain ⟨g₁, m₁, l₁, -, d₁⟩ := iha hg ha
    exact ⟨g₁, m₁, l₁, trivial, .tail d₁ hres hfi hty hy⟩
  | @tailRes s s₁ f f₁ stk stk₁ i args es hargs hres iha =>
    intro labels ret oc hg hc
    obtain ⟨o₁, h1, -⟩ := chk_consE.mp hc
    obtain ⟨oa, ha, -⟩ := chk1_opE h1
    obtain ⟨g₁, m₁, l₁, -, d₁⟩ := iha hg ha
    exact ⟨g₁, m₁, l₁, trivial, .tailRes d₁ hres⟩
  | @throw s s₁ f f₁ stk stk₁ x args es ta ti ts hargs ht he hn iha =>
    intro labels ret oc hg hc
    obtain ⟨o₁, h1, -⟩ := chk_consE.mp hc
    obtain ⟨oa, ha, -⟩ := chk1_opE h1
    obtain ⟨g₁, m₁, l₁, -, d₁⟩ := iha hg ha
    have g₂ : Γ.Good (s₁.addExn ⟨ta, (stk₁.take ts.length).reverse⟩) :=
      ⟨g₁.1, tagsOk_throw g₁.2 ht he (by simp; omega)⟩
    exact ⟨g₂, m₁, l₁, trivial, .throw d₁ ht he hn⟩
  | @throwRefNull s s₁ f f₁ stk stk₁ args es hargs iha =>
    intro labels ret oc hg hc
    obtain ⟨o₁, h1, -⟩ := chk_consE.mp hc
    obtain ⟨oa, ha, -⟩ := chk1_opE h1
    obtain ⟨g₁, m₁, l₁, -, d₁⟩ := iha hg ha
    exact ⟨g₁, m₁, l₁, trivial, .throwRefNull d₁⟩
  | @throwRefExn s s₁ f f₁ stk stk₁ a args es hargs iha =>
    intro labels ret oc hg hc
    obtain ⟨o₁, h1, -⟩ := chk_consE.mp hc
    obtain ⟨oa, ha, -⟩ := chk1_opE h1
    obtain ⟨g₁, m₁, l₁, -, d₁⟩ := iha hg ha
    exact ⟨g₁, m₁, l₁, trivial, .throwRefExn d₁⟩
  | @tryOk s s₁ f f₁ stk vs bt cs body es np nr fl r har hbody hvs hk ihb ihk =>
    intro labels ret oc hg hc
    obtain ⟨-, -, -, hle, hends, h2⟩ := arity_try_pre har hc
    obtain ⟨ob, hob, hob'⟩ := endsAt_eqE hends
    have hlen : (stk.take np).length = np := by simp; omega
    obtain ⟨g₁, m₁, l₁, go₁, db⟩ := ihb hg (by rw [hlen]; exact hob)
    have hnr := goodO_blockVals go₁ hob' hvs
    obtain ⟨g, m, l, go, dk⟩ := fit_cont hg g₁ m₁ l₁ h2 (len_take_drop hnr hle) ihk
    exact ⟨g, m, l, go, .tryOk har db hvs dk⟩
  | @tryBrk s s₁ f f₁ stk vs bt cs body es np nr k har hbody ihb =>
    intro labels ret oc hg hc
    obtain ⟨-, -, -, hle, hends, -⟩ := arity_try_pre har hc
    obtain ⟨ob, hob, -⟩ := endsAt_eqE hends
    have hlen : (stk.take np).length = np := by simp; omega
    obtain ⟨g₁, m₁, l₁, go₁, db⟩ := ihb hg (by rw [hlen]; exact hob)
    exact ⟨g₁, m₁, l₁, goodO_brk_succ go₁, .tryBrk har db⟩
  | @tryEsc s s₁ f f₁ stk bt cs body es np nr o har hbody ho hnt ihb =>
    intro labels ret oc hg hc
    obtain ⟨-, -, -, hle, hends, -⟩ := arity_try_pre har hc
    obtain ⟨ob, hob, -⟩ := endsAt_eqE hends
    have hlen : (stk.take np).length = np := by simp; omega
    obtain ⟨g₁, m₁, l₁, go₁, db⟩ := ihb hg (by rw [hlen]; exact hob)
    exact ⟨g₁, m₁, l₁, goodO_escape go₁ ho, .tryEsc har db ho hnt⟩
  | @tryCatch s s₁ f f₁ stk us bt cs body es np nr a l har hbody hcs ihb =>
    intro labels ret oc hg hc
    obtain ⟨ns, hns, hok, hle, hends, -⟩ := arity_try_pre har hc
    obtain ⟨ob, hob, -⟩ := endsAt_eqE hends
    have hlen : (stk.take np).length = np := by simp; omega
    obtain ⟨g₁, m₁, l₁, -, db⟩ := ihb hg (by rw [hlen]; exact hob)
    rw [← m₁] at hns
    obtain ⟨n, hn, hle'⟩ := catches_count g₁.2.2 hcs hns hok
    have hgo : GoodO labels ret oc (.flow (.brk l.toNat (us.reverse ++ stk.drop np))) :=
      ⟨n, hn, by simp; omega⟩
    exact ⟨g₁, m₁, l₁, hgo, .tryCatch har db hcs⟩
  | @tryRethrow s s₁ f f₁ stk bt cs body es np nr a har hbody hcs ihb =>
    intro labels ret oc hg hc
    obtain ⟨-, -, -, hle, hends, -⟩ := arity_try_pre har hc
    obtain ⟨ob, hob, -⟩ := endsAt_eqE hends
    have hlen : (stk.take np).length = np := by simp; omega
    obtain ⟨g₁, m₁, l₁, -, db⟩ := ihb hg (by rw [hlen]; exact hob)
    exact ⟨g₁, m₁, l₁, trivial, .tryRethrow har db hcs⟩

end Silmaril.Proofs.Wasm.Abstract.TypedCatFit
