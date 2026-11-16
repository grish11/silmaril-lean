module

public import Silmaril.Wasm.Abstract.XRecursion.Defs
public import Silmaril.Wasm.Abstract.Recursion.Thms
import Silmaril.Wasm.Abstract.CallX.Thms

/-!
Proofs for `Silmaril.Wasm.Abstract.XRecursion.Thms`.

* Every run of `EvalOX` keeps the store's functions when its oracle does
  (`evalOX_funcs`); so does the closure (`closedCallX_funcs`).
* On stores whose functions have no extended call form (`StoreXFree`), an
  `EvalOX` run answered by `closedCallX` is an `EvalO` run answered by
  `closedCall` (`evalO_of_evalOX_free`), so the two closures agree there
  (`closedCallX_iff`). Both directions are least-fixpoint inductions.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.XRecursion

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Abstract (CallRel EvalO closedCall bodyCall)
open Silmaril.Wasm.Abstract.CallX Silmaril.Wasm.Abstract.XRecursion

variable {H : Type}

/-- Flat instructions keep the store's functions. -/
theorem evalFlat_funcs {s s' : Store H} {f f' : Frame} {stk : List Val} {i : Instr} {fl : Flow}
    (h : evalFlat s f stk i = some (s', f', fl)) : s'.funcs = s.funcs := by
  unfold evalFlat at h
  repeat' (first | split at h | (simp only [Option.map_eq_some_iff, Option.bind_eq_bind,
    Option.bind_eq_some_iff] at h))
  all_goals first
    | (simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h; obtain ⟨rfl, -⟩ := h; rfl)
    | (obtain ⟨_, -, h⟩ := h; simp only [Option.some.injEq, Prod.mk.injEq] at h
       obtain ⟨rfl, -⟩ := h; rfl)
    | (simp at h; done)
    | (obtain ⟨_, -, _, -, rfl, -⟩ := h; rfl)
    | (obtain ⟨a, -, b, -, h⟩ := h
       split at h <;> (simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h; rfl))

/-- An oracle that keeps the store's functions. -/
def KeepsFuncs (C : CallRel H) : Prop := ∀ s a args out, C s a args out → out.1.funcs = s.funcs

/-- `EvalOX` keeps the store's functions when its oracle does. -/
theorem evalOX_funcs {C : CallRel H} (hC : KeepsFuncs C) {s : Store H} {f : Frame}
    {stk : List Val} {es : List BExpr} {r : Store H × Frame × Flow} (h : EvalOX C s f stk es r) :
    r.1.funcs = s.funcs := by
  induction h with
  | nil => rfl
  | argsAbort _ _ ih => exact ih
  | callOk _ _ _ hcall _ _ ih₁ ih₂ => exact ih₂.trans ((hC _ _ _ _ hcall).trans ih₁)
  | callTrap _ _ _ hcall ih => exact (hC _ _ _ _ hcall).trans ih
  | callThrow _ _ _ hcall ih => exact (hC _ _ _ _ hcall).trans ih
  | opOk _ _ hflat _ ih₁ ih₂ => exact ih₂.trans ((evalFlat_funcs hflat).trans ih₁)
  | opStop _ _ hflat _ ih => exact (evalFlat_funcs hflat).trans ih
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
  | callIndOk _ _ _ _ hcall _ _ ih₁ ih₂ => exact ih₂.trans ((hC _ _ _ _ hcall).trans ih₁)
  | callIndRes _ _ ih => exact ih
  | callIndStop _ _ _ _ hcall _ ih => exact (hC _ _ _ _ hcall).trans ih
  | callRefOk _ _ _ hcall _ _ ih₁ ih₂ => exact ih₂.trans ((hC _ _ _ _ hcall).trans ih₁)
  | callRefNull _ ih => exact ih
  | callRefStop _ _ _ hcall _ ih => exact (hC _ _ _ _ hcall).trans ih
  | tail _ _ _ _ hcall _ ih => exact (hC _ _ _ _ hcall).trans ih
  | tailRes _ _ ih => exact ih

theorem closedCallX_eq_bodyCallX : (closedCallX : CallRel H) = bodyCallX closedCallX :=
  (OrderHom.map_lfp bodyCallXOp).symm

/-- The closure keeps the store's functions. -/
theorem closedCallX_funcs : KeepsFuncs (closedCallX : CallRel H) := by
  have : (closedCallX : CallRel H) ≤ fun s _ _ out => out.1.funcs = s.funcs := by
    refine OrderHom.lfp_le _ ?_
    rintro s a args out ⟨fi, fn, ps, rs, f₂, -, -, -, hb⟩
    exact evalOX_funcs (fun _ _ _ _ h => h) hb
  exact fun s a args out h => this s a args out h

theorem storeXFree_of_funcs {s s' : Store H} (h : s'.funcs = s.funcs) (hs : StoreXFree s) :
    StoreXFree s' := fun a fi fn hfi hc => hs a fi fn (h ▸ hfi) hc

/-- Agreement with the direct closure, as an oracle: functions kept, and on
direct stores, answered by `closedCall`. -/
def DirectAns : CallRel H := fun s a args out =>
  out.1.funcs = s.funcs ∧ (StoreXFree s → closedCall s a args out)

theorem directAns_keeps : KeepsFuncs (DirectAns : CallRel H) := fun _ _ _ _ h => h.1

/-- On a direct store, an `EvalOX DirectAns` run of direct code is an `EvalO
closedCall` run. -/
theorem evalO_of_evalOX_direct {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    {r : Store H × Frame × Flow} (h : EvalOX DirectAns s f stk es r) :
    StoreXFree s → xFreeL es = true → EvalO closedCall s f stk es r := by
  induction h with
  | nil => intro _ _; exact .nil
  | argsAbort _ hfl ih =>
    intro hs hx; simp only [xFreeL, xFree, Bool.and_eq_true] at hx
    exact .argsAbort (ih hs hx.1.2) hfl
  | callOk hargs hfi hty hcall hvs _ ih₁ ih₂ =>
    intro hs hx; simp only [xFreeL, xFree, Bool.and_eq_true] at hx
    have hs₁ := storeXFree_of_funcs (evalOX_funcs directAns_keeps hargs) hs
    exact .callOk (ih₁ hs hx.1.2) hfi hty (hcall.2 hs₁) hvs
      (ih₂ (storeXFree_of_funcs hcall.1 hs₁) hx.2)
  | callTrap hargs hfi hty hcall ih =>
    intro hs hx; simp only [xFreeL, xFree, Bool.and_eq_true] at hx
    have hs₁ := storeXFree_of_funcs (evalOX_funcs directAns_keeps hargs) hs
    exact .callTrap (ih hs hx.1.2) hfi hty (hcall.2 hs₁)
  | callThrow hargs hfi hty hcall ih =>
    intro hs hx; simp only [xFreeL, xFree, Bool.and_eq_true] at hx
    have hs₁ := storeXFree_of_funcs (evalOX_funcs directAns_keeps hargs) hs
    exact .callThrow (ih hs hx.1.2) hfi hty (hcall.2 hs₁)
  | opOk hi hargs hflat _ ih₁ ih₂ =>
    intro hs hx; simp only [xFreeL, xFree, Bool.and_eq_true] at hx
    have hs₁ := storeXFree_of_funcs (evalOX_funcs directAns_keeps hargs) hs
    exact .opOk hi (ih₁ hs hx.1.2) hflat (ih₂ (storeXFree_of_funcs (evalFlat_funcs hflat) hs₁) hx.2)
  | opStop hi _ hflat hfl ih =>
    intro hs hx; simp only [xFreeL, xFree, Bool.and_eq_true] at hx
    exact .opStop hi (ih hs hx.1.2) hflat hfl
  | blockOk har hbody hvs _ ih₁ ih₂ =>
    intro hs hx; simp only [xFreeL, xFree, Bool.and_eq_true] at hx
    exact .blockOk har (ih₁ hs hx.1) hvs
      (ih₂ (storeXFree_of_funcs (evalOX_funcs directAns_keeps hbody) hs) hx.2)
  | blockBrk har _ ih =>
    intro hs hx; simp only [xFreeL, xFree, Bool.and_eq_true] at hx
    exact .blockBrk har (ih hs hx.1)
  | blockEsc har _ hfl ih =>
    intro hs hx; simp only [xFreeL, xFree, Bool.and_eq_true] at hx
    exact .blockEsc har (ih hs hx.1) hfl
  | loopOk har hbody _ ih₁ ih₂ =>
    intro hs hx; simp only [xFreeL, xFree, Bool.and_eq_true] at hx
    exact .loopOk har (ih₁ hs hx.1)
      (ih₂ (storeXFree_of_funcs (evalOX_funcs directAns_keeps hbody) hs) hx.2)
  | loopBack har hbody _ ih₁ ih₂ =>
    intro hs hx
    have hx' := hx
    simp only [xFreeL, xFree, Bool.and_eq_true] at hx'
    exact .loopBack har (ih₁ hs hx'.1)
      (ih₂ (storeXFree_of_funcs (evalOX_funcs directAns_keeps hbody) hs) hx)
  | loopBrk har _ ih =>
    intro hs hx; simp only [xFreeL, xFree, Bool.and_eq_true] at hx
    exact .loopBrk har (ih hs hx.1)
  | loopEsc har _ hfl ih =>
    intro hs hx; simp only [xFreeL, xFree, Bool.and_eq_true] at hx
    exact .loopEsc har (ih hs hx.1) hfl
  | @ifOk s s₁ s₂ f f₁ f₂ stk stk₁ vs cv b bt c t el es np nr fl r hc hb har harm hvs _ ih₁ ih₂ ih₃ =>
    intro hs hx; simp only [xFreeL, xFree, Bool.and_eq_true] at hx
    have hs₁ := storeXFree_of_funcs (evalOX_funcs directAns_keeps hc) hs
    have hs₂ := storeXFree_of_funcs (evalOX_funcs directAns_keeps harm) hs₁
    exact .ifOk (ih₁ hs hx.1.1.1) hb har (ih₂ hs₁ (by cases b <;> simp [hx.1.1.2, hx.1.2])) hvs
      (ih₃ hs₂ hx.2)
  | @ifBrk s s₁ s₂ f f₁ f₂ stk stk₁ vs cv b bt c t el es np nr k hc hb har _ ih₁ ih₂ =>
    intro hs hx; simp only [xFreeL, xFree, Bool.and_eq_true] at hx
    have hs₁ := storeXFree_of_funcs (evalOX_funcs directAns_keeps hc) hs
    exact .ifBrk (ih₁ hs hx.1.1.1) hb har (ih₂ hs₁ (by cases b <;> simp [hx.1.1.2, hx.1.2]))
  | @ifEsc s s₁ s₂ f f₁ f₂ stk stk₁ cv b bt c t el es np nr fl hc hb har _ hfl ih₁ ih₂ =>
    intro hs hx; simp only [xFreeL, xFree, Bool.and_eq_true] at hx
    have hs₁ := storeXFree_of_funcs (evalOX_funcs directAns_keeps hc) hs
    exact .ifEsc (ih₁ hs hx.1.1.1) hb har (ih₂ hs₁ (by cases b <;> simp [hx.1.1.2, hx.1.2])) hfl
  | ifAbort _ hfl ih =>
    intro hs hx; simp only [xFreeL, xFree, Bool.and_eq_true] at hx
    exact .ifAbort (ih hs hx.1.1.1) hfl
  | callIndOk => intro _ hx; simp [xFreeL, xFree, isXCall] at hx
  | callIndRes => intro _ hx; simp [xFreeL, xFree, isXCall] at hx
  | callIndStop => intro _ hx; simp [xFreeL, xFree, isXCall] at hx
  | callRefOk => intro _ hx; simp [xFreeL, xFree, isXCall] at hx
  | callRefNull => intro _ hx; simp [xFreeL, xFree, isXCall] at hx
  | callRefStop => intro _ hx; simp [xFreeL, xFree, isXCall] at hx
  | tail _ hres =>
    intro _ hx; simp only [xFreeL, xFree, Bool.and_eq_true] at hx
    simp [Silmaril.Wasm.Abstract.CallX.isXCall_of_tailRes hres] at hx
  | tailRes _ hres =>
    intro _ hx; simp only [xFreeL, xFree, Bool.and_eq_true] at hx
    simp [Silmaril.Wasm.Abstract.CallX.isXCall_of_tailRes hres] at hx

theorem closedCallX_le_directAns : (closedCallX : CallRel H) ≤ DirectAns := by
  refine OrderHom.lfp_le _ ?_
  rintro s a args out ⟨fi, fn, ps, rs, f₂, hfi, hc, hty, hb⟩
  refine ⟨evalOX_funcs directAns_keeps hb, fun hs => ?_⟩
  rw [Silmaril.Wasm.Abstract.closedCall_fixpoint]
  exact ⟨fi, fn, ps, rs, f₂, hfi, hc, hty, evalO_of_evalOX_direct hb hs (hs a fi fn hfi hc)⟩

theorem closedCall_le_closedCallX : (closedCall : CallRel H) ≤ closedCallX := by
  refine OrderHom.lfp_le _ ?_
  rintro s a args out ⟨fi, fn, ps, rs, f₂, hfi, hc, hty, hb⟩
  rw [closedCallX_eq_bodyCallX]
  exact ⟨fi, fn, ps, rs, f₂, hfi, hc, hty, EvalOX.of_evalO hb⟩

/-- On direct stores, the extended closure answers every call as `closedCall`. -/
theorem closedCallX_iff {s : Store H} (hs : StoreXFree s) {a : Nat} {args : List Val}
    {out : Store H × Flow} : closedCallX s a args out ↔ closedCall s a args out :=
  ⟨fun h => (closedCallX_le_directAns s a args out h).2 hs,
    fun h => closedCall_le_closedCallX s a args out h⟩

/-- On direct stores, direct code runs in the closed extended semantics as in
the closed native one. -/
theorem evalOX_closed_iff {s : Store H} (hs : StoreXFree s) {f : Frame} {stk : List Val}
    {es : List BExpr} (hx : xFreeL es = true) {r : Store H × Frame × Flow} :
    EvalOX closedCallX s f stk es r ↔ EvalO closedCall s f stk es r :=
  ⟨fun h => evalO_of_evalOX_direct (h.mono closedCallX_le_directAns) hs hx,
    fun h => EvalOX.of_evalO (h.mono closedCall_le_closedCallX)⟩

theorem closedOutcomeX_iff {s : Store H} (hs : StoreXFree s) {a : Nat} {vs : List Val}
    {s' : Store H} {fl : Flow} :
    ClosedOutcomeX s a vs s' fl ↔ Silmaril.Wasm.Abstract.ClosedOutcome s a vs s' fl := by
  constructor
  · rintro ⟨fi, fn, ps, rs, f₂, bfl, hfi, hc, hty, hb, hx⟩
    exact ⟨fi, fn, ps, rs, f₂, bfl, hfi, hc, hty, (evalOX_closed_iff hs (hs a fi fn hfi hc)).1 hb, hx⟩
  · rintro ⟨fi, fn, ps, rs, f₂, bfl, hfi, hc, hty, hb, hx⟩
    exact ⟨fi, fn, ps, rs, f₂, bfl, hfi, hc, hty, (evalOX_closed_iff hs (hs a fi fn hfi hc)).2 hb, hx⟩

end Silmaril.Proofs.Wasm.Abstract.XRecursion
