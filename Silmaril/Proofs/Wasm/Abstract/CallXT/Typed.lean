module

public import Silmaril.Proofs.Wasm.Abstract.CallXT.Cast
public import Silmaril.Proofs.Wasm.Abstract.XRecursion.Basic

/-!
Proofs for `Silmaril.Wasm.Abstract.CallXT.Thms`: **the arity premise of
`call_indirect` from typing.** On a store with valid function types, in an
instance with valid types, code without `call_ref` whose `call_indirect`s name
types of the instance (`indOkL`) runs in `EvalOXT` whenever it runs in `EvalOX`,
for an oracle that keeps function types valid (`evalOXT_of_evalOX_ind`). The
premise of each indirect call is the cast fact `typeArity_of_cast`: frames keep
their instance and runs keep valid function types along the way.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.CallXT

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Abstract (CallRel)
open Silmaril.Wasm.Abstract.CallX Silmaril.Wasm.Abstract.CallXT
open Silmaril.Proofs.Wasm.Abstract.XRecursion (evalFlat_funcs)

variable {H : Type}

/-- Flat instructions keep the frame's instance. -/
theorem evalFlat_module {s s' : Store H} {f f' : Frame} {stk : List Val} {i : Instr} {fl : Flow}
    (h : evalFlat s f stk i = some (s', f', fl)) : f'.module = f.module := by
  unfold evalFlat at h
  repeat' (first | split at h | (simp only [Option.map_eq_some_iff, Option.bind_eq_bind,
    Option.bind_eq_some_iff] at h))
  all_goals first
    | (simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h; obtain ⟨-, rfl, -⟩ := h; rfl)
    | (obtain ⟨_, -, h⟩ := h; simp only [Option.some.injEq, Prod.mk.injEq] at h
       obtain ⟨-, rfl, -⟩ := h; rfl)
    | (simp at h; done)
    | (obtain ⟨_, -, _, -, -, rfl, -⟩ := h; rfl)
    | (obtain ⟨a, -, b, -, h⟩ := h
       split at h <;> (simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl, -⟩ := h; rfl))

/-- Runs keep the frame's instance. -/
theorem evalOX_module {C : CallRel H} {s : Store H} {f : Frame} {stk : List Val}
    {es : List BExpr} {r : Store H × Frame × Flow} (h : EvalOX C s f stk es r) :
    r.2.1.module = f.module := by
  induction h with
  | nil => rfl
  | argsAbort _ _ ih => exact ih
  | callOk _ _ _ _ _ _ ih₁ ih₂ => exact ih₂.trans ih₁
  | callTrap _ _ _ _ ih => exact ih
  | callThrow _ _ _ _ ih => exact ih
  | opOk _ _ hflat _ ih₁ ih₂ => exact ih₂.trans ((evalFlat_module hflat).trans ih₁)
  | opStop _ _ hflat _ ih => exact (evalFlat_module hflat).trans ih
  | blockOk _ _ _ _ ih₁ ih₂ => exact ih₂.trans ih₁
  | blockBrk _ _ ih => exact ih
  | blockEsc _ _ _ ih => exact ih
  | loopOk _ _ _ ih₁ ih₂ => exact ih₂.trans ih₁
  | loopBack _ _ _ ih₁ ih₂ => exact ih₂.trans ih₁
  | loopBrk _ _ ih => exact ih
  | loopEsc _ _ _ ih => exact ih
  | ifOk _ _ _ _ _ _ ih₁ ih₂ ih₃ => exact ih₃.trans (ih₂.trans ih₁)
  | ifBrk _ _ _ _ ih₁ ih₂ => exact ih₂.trans ih₁
  | ifEsc _ _ _ _ _ ih₁ ih₂ => exact ih₂.trans ih₁
  | ifAbort _ _ ih => exact ih
  | callIndOk _ _ _ _ _ _ _ ih₁ ih₂ => exact ih₂.trans ih₁
  | callIndRes _ _ ih => exact ih
  | callIndStop _ _ _ _ _ _ ih => exact ih
  | callRefOk _ _ _ _ _ _ ih₁ ih₂ => exact ih₂.trans ih₁
  | callRefNull _ ih => exact ih
  | callRefStop _ _ _ _ _ ih => exact ih
  | tail _ _ _ _ _ _ ih => exact ih
  | tailRes _ _ ih => exact ih

theorem tyFuncs_of_funcs {s s' : Store H} (h : s'.funcs = s.funcs) (hs : TyFuncs s) : TyFuncs s' :=
  fun a fi hfi => hs a fi (h ▸ hfi)

/-- Runs keep function types valid. -/
theorem evalOX_tyFuncs {C : CallRel H} (hC : KeepsTy C) {s : Store H} {f : Frame}
    {stk : List Val} {es : List BExpr} {r : Store H × Frame × Flow} (h : EvalOX C s f stk es r) :
    TyFuncs s → TyFuncs r.1 := by
  induction h with
  | nil => exact id
  | argsAbort _ _ ih => exact ih
  | callOk _ _ _ hcall _ _ ih₁ ih₂ => exact fun hs => ih₂ (hC _ _ _ _ hcall (ih₁ hs))
  | callTrap _ _ _ hcall ih => exact fun hs => hC _ _ _ _ hcall (ih hs)
  | callThrow _ _ _ hcall ih => exact fun hs => hC _ _ _ _ hcall (ih hs)
  | opOk _ _ hflat _ ih₁ ih₂ => exact fun hs => ih₂ (tyFuncs_of_funcs (evalFlat_funcs hflat) (ih₁ hs))
  | opStop _ _ hflat _ ih => exact fun hs => tyFuncs_of_funcs (evalFlat_funcs hflat) (ih hs)
  | blockOk _ _ _ _ ih₁ ih₂ => exact fun hs => ih₂ (ih₁ hs)
  | blockBrk _ _ ih => exact ih
  | blockEsc _ _ _ ih => exact ih
  | loopOk _ _ _ ih₁ ih₂ => exact fun hs => ih₂ (ih₁ hs)
  | loopBack _ _ _ ih₁ ih₂ => exact fun hs => ih₂ (ih₁ hs)
  | loopBrk _ _ ih => exact ih
  | loopEsc _ _ _ ih => exact ih
  | ifOk _ _ _ _ _ _ ih₁ ih₂ ih₃ => exact fun hs => ih₃ (ih₂ (ih₁ hs))
  | ifBrk _ _ _ _ ih₁ ih₂ => exact fun hs => ih₂ (ih₁ hs)
  | ifEsc _ _ _ _ _ ih₁ ih₂ => exact fun hs => ih₂ (ih₁ hs)
  | ifAbort _ _ ih => exact ih
  | callIndOk _ _ _ _ hcall _ _ ih₁ ih₂ => exact fun hs => ih₂ (hC _ _ _ _ hcall (ih₁ hs))
  | callIndRes _ _ ih => exact ih
  | callIndStop _ _ _ _ hcall _ ih => exact fun hs => hC _ _ _ _ hcall (ih hs)
  | callRefOk _ _ _ hcall _ _ ih₁ ih₂ => exact fun hs => ih₂ (hC _ _ _ _ hcall (ih₁ hs))
  | callRefNull _ ih => exact ih
  | callRefStop _ _ _ hcall _ ih => exact fun hs => hC _ _ _ _ hcall (ih hs)
  | tail _ _ _ _ hcall _ ih => exact fun hs => hC _ _ _ _ hcall (ih hs)
  | tailRes _ _ ih => exact ih

/-- The arity premise of a resolved indirect call. -/
theorem typeArity_of_indRes {s : Store H} {f : Frame} {x : TableIdx} {y : TypeIdx} {ad : AddrType}
    {i : BitVec ad.intType.width} {fa : Nat} {fi : FuncInst H} {ps rs : List Validation.CValType}
    (hres : Silmaril.Wasm.Abstract.CallRes.IndRes s f x y ad i (some fa))
    (hfi : s.funcs[fa]? = some fi) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    (hs : TyFuncs s) (hm : TyTypes f.module) (hy : (f.module.types[y.toNat]?).isSome = true) :
    typeArity f.module y = some (ps.length, rs.length) := by
  obtain ⟨d, hd⟩ := Option.isSome_iff_exists.1 hy
  cases hres with
  | func _ _ hc => exact typeArity_of_cast hd hfi hty (hs _ _ hfi) (hm _ _ hd) hc

/-- **The `call_indirect` premise from typing.** -/
theorem evalOXT_of_evalOX_ind {C : CallRel H} (hC : KeepsTy C) {s : Store H} {f : Frame}
    {stk : List Val} {es : List BExpr} {r : Store H × Frame × Flow} (h : EvalOX C s f stk es r) :
    TyFuncs s → TyTypes f.module → indOkL f.module es = true → EvalOXT C s f stk es r := by
  induction h with
  | nil => intro _ _ _; exact .nil
  | argsAbort _ hfl ih =>
    intro hs hm hx; simp only [indOkL, indOk, Bool.and_eq_true] at hx
    exact .argsAbort (ih hs hm hx.1.2) hfl
  | callOk hargs hfi hty hcall hvs hk ih₁ ih₂ =>
    intro hs hm hx; simp only [indOkL, indOk, Bool.and_eq_true] at hx
    have hs₂ := hC _ _ _ _ hcall (evalOX_tyFuncs hC hargs hs)
    have he := evalOX_module hargs
    exact .callOk (ih₁ hs hm hx.1.2) hfi hty hcall hvs (ih₂ hs₂ (he ▸ hm) (he ▸ hx.2))
  | callTrap _ hfi hty hcall ih =>
    intro hs hm hx; simp only [indOkL, indOk, Bool.and_eq_true] at hx
    exact .callTrap (ih hs hm hx.1.2) hfi hty hcall
  | callThrow _ hfi hty hcall ih =>
    intro hs hm hx; simp only [indOkL, indOk, Bool.and_eq_true] at hx
    exact .callThrow (ih hs hm hx.1.2) hfi hty hcall
  | opOk hi hargs hflat hk ih₁ ih₂ =>
    intro hs hm hx; simp only [indOkL, indOk, Bool.and_eq_true] at hx
    have hs₂ := tyFuncs_of_funcs (evalFlat_funcs hflat) (evalOX_tyFuncs hC hargs hs)
    have he := (evalFlat_module hflat).trans (evalOX_module hargs)
    exact .opOk hi (ih₁ hs hm hx.1.2) hflat (ih₂ hs₂ (he ▸ hm) (he ▸ hx.2))
  | opStop hi _ hflat hfl ih =>
    intro hs hm hx; simp only [indOkL, indOk, Bool.and_eq_true] at hx
    exact .opStop hi (ih hs hm hx.1.2) hflat hfl
  | blockOk har hbody hvs hk ih₁ ih₂ =>
    intro hs hm hx; simp only [indOkL, indOk, Bool.and_eq_true] at hx
    have he := evalOX_module hbody
    exact .blockOk har (ih₁ hs hm hx.1) hvs (ih₂ (evalOX_tyFuncs hC hbody hs) (he ▸ hm) (he ▸ hx.2))
  | blockBrk har _ ih =>
    intro hs hm hx; simp only [indOkL, indOk, Bool.and_eq_true] at hx
    exact .blockBrk har (ih hs hm hx.1)
  | blockEsc har _ hfl ih =>
    intro hs hm hx; simp only [indOkL, indOk, Bool.and_eq_true] at hx
    exact .blockEsc har (ih hs hm hx.1) hfl
  | loopOk har hbody hk ih₁ ih₂ =>
    intro hs hm hx; simp only [indOkL, indOk, Bool.and_eq_true] at hx
    have he := evalOX_module hbody
    exact .loopOk har (ih₁ hs hm hx.1) (ih₂ (evalOX_tyFuncs hC hbody hs) (he ▸ hm) (he ▸ hx.2))
  | loopBack har hbody hk ih₁ ih₂ =>
    intro hs hm hx
    have hx' := hx
    simp only [indOkL, indOk, Bool.and_eq_true] at hx'
    have he := evalOX_module hbody
    exact .loopBack har (ih₁ hs hm hx'.1) (ih₂ (evalOX_tyFuncs hC hbody hs) (he ▸ hm) (he ▸ hx))
  | loopBrk har _ ih =>
    intro hs hm hx; simp only [indOkL, indOk, Bool.and_eq_true] at hx
    exact .loopBrk har (ih hs hm hx.1)
  | loopEsc har _ hfl ih =>
    intro hs hm hx; simp only [indOkL, indOk, Bool.and_eq_true] at hx
    exact .loopEsc har (ih hs hm hx.1) hfl
  | @ifOk s s₁ s₂ f f₁ f₂ stk stk₁ vs cv b bt c t el es np nr fl r hc hb har harm hvs hk ih₁ ih₂ ih₃ =>
    intro hs hm hx; simp only [indOkL, indOk, Bool.and_eq_true] at hx
    have he₁ := evalOX_module hc
    have he₂ := evalOX_module harm
    have hs₁ := evalOX_tyFuncs hC hc hs
    have hxa : indOkL f₁.module (if b then t else el) = true := by
      rw [he₁]; cases b <;> simp [hx.1.1.2, hx.1.2]
    exact .ifOk (ih₁ hs hm hx.1.1.1) hb har (ih₂ hs₁ (he₁ ▸ hm) hxa) hvs
      (ih₃ (evalOX_tyFuncs hC harm hs₁) (he₂ ▸ he₁ ▸ hm) (he₂ ▸ he₁ ▸ hx.2))
  | @ifBrk s s₁ s₂ f f₁ f₂ stk stk₁ vs cv b bt c t el es np nr k hc hb har harm ih₁ ih₂ =>
    intro hs hm hx; simp only [indOkL, indOk, Bool.and_eq_true] at hx
    have he₁ := evalOX_module hc
    have hxa : indOkL f₁.module (if b then t else el) = true := by
      rw [he₁]; cases b <;> simp [hx.1.1.2, hx.1.2]
    exact .ifBrk (ih₁ hs hm hx.1.1.1) hb har (ih₂ (evalOX_tyFuncs hC hc hs) (he₁ ▸ hm) hxa)
  | @ifEsc s s₁ s₂ f f₁ f₂ stk stk₁ cv b bt c t el es np nr fl hc hb har harm hfl ih₁ ih₂ =>
    intro hs hm hx; simp only [indOkL, indOk, Bool.and_eq_true] at hx
    have he₁ := evalOX_module hc
    have hxa : indOkL f₁.module (if b then t else el) = true := by
      rw [he₁]; cases b <;> simp [hx.1.1.2, hx.1.2]
    exact .ifEsc (ih₁ hs hm hx.1.1.1) hb har (ih₂ (evalOX_tyFuncs hC hc hs) (he₁ ▸ hm) hxa) hfl
  | ifAbort _ hfl ih =>
    intro hs hm hx; simp only [indOkL, indOk, Bool.and_eq_true] at hx
    exact .ifAbort (ih hs hm hx.1.1.1) hfl
  | callIndOk hargs hres hfi hty hcall hvs hk ih₁ ih₂ =>
    intro hs hm hx; simp only [indOkL, indOk, indInstr, Bool.and_eq_true] at hx
    have hs₁ := evalOX_tyFuncs hC hargs hs
    have he := evalOX_module hargs
    have hs₂ := hC _ _ _ _ hcall hs₁
    exact .callIndOk (ih₁ hs hm hx.1.2) hres hfi hty
      (typeArity_of_indRes hres hfi hty hs₁ (he ▸ hm) (he ▸ hx.1.1)) hcall hvs
      (ih₂ hs₂ (he ▸ hm) (he ▸ hx.2))
  | callIndRes _ hres ih =>
    intro hs hm hx; simp only [indOkL, indOk, Bool.and_eq_true] at hx
    exact .callIndRes (ih hs hm hx.1.2) hres
  | callIndStop hargs hres hfi hty hcall hfl ih =>
    intro hs hm hx; simp only [indOkL, indOk, indInstr, Bool.and_eq_true] at hx
    have he := evalOX_module hargs
    exact .callIndStop (ih hs hm hx.1.2) hres hfi hty
      (typeArity_of_indRes hres hfi hty (evalOX_tyFuncs hC hargs hs) (he ▸ hm) (he ▸ hx.1.1))
      hcall hfl
  | callRefOk => intro _ _ hx; simp [indOkL, indOk, indInstr] at hx
  | callRefNull => intro _ _ hx; simp [indOkL, indOk, indInstr] at hx
  | callRefStop => intro _ _ hx; simp [indOkL, indOk, indInstr] at hx
  | tail _ hres hfi hty hcall hfl ih =>
    intro hs hm hx; simp only [indOkL, indOk, Bool.and_eq_true] at hx
    exact .tail (ih hs hm hx.1.2) hres hfi hty hcall hfl
  | tailRes _ hres ih =>
    intro hs hm hx; simp only [indOkL, indOk, Bool.and_eq_true] at hx
    exact .tailRes (ih hs hm hx.1.2) hres

end Silmaril.Proofs.Wasm.Abstract.CallXT
