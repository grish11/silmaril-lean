module

public import Silmaril.Wasm.Abstract.CallXP.Defs

/-!
Proofs for `Silmaril.Wasm.Abstract.CallXP.Thms`: `EvalOXP` is monotone in its oracle (`mono`),
and on code without the extended call forms it is `CallXE.EvalOXE`, with no pending tail call
(`of_evalOXE`, `to_evalOXE`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.CallXP

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Abstract (CallRel)
open Silmaril.Wasm.Abstract.CallX Silmaril.Wasm.Abstract.CallXE Silmaril.Wasm.Abstract.CallXP

variable {H : Type}

/-- `EvalOXP` is monotone in its oracle. -/
theorem mono {C C' : CallRel H} (hC : C ≤ C') {s : Store H} {f : Frame} {stk : List Val}
    {es : List BExpr} {r : Store H × Frame × POut} (h : EvalOXP C s f stk es r) :
    EvalOXP C' s f stk es r := by
  induction h with
  | nil => exact .nil
  | argsAbort _ ho ih => exact .argsAbort ih ho
  | callOk _ hfi hty hcall hvs _ ih₁ ih₂ => exact .callOk ih₁ hfi hty (hC _ _ _ _ hcall) hvs ih₂
  | callTrap _ hfi hty hcall ih => exact .callTrap ih hfi hty (hC _ _ _ _ hcall)
  | callThrow _ hfi hty hcall ih => exact .callThrow ih hfi hty (hC _ _ _ _ hcall)
  | opOk hi _ hflat _ ih₁ ih₂ => exact .opOk hi ih₁ hflat ih₂
  | opStop hi _ hflat hfl ih => exact .opStop hi ih hflat hfl
  | blockOk har _ hvs _ ih₁ ih₂ => exact .blockOk har ih₁ hvs ih₂
  | blockBrk har _ ih => exact .blockBrk har ih
  | blockEsc har _ ho ih => exact .blockEsc har ih ho
  | loopOk har _ _ ih₁ ih₂ => exact .loopOk har ih₁ ih₂
  | loopBack har _ _ ih₁ ih₂ => exact .loopBack har ih₁ ih₂
  | loopBrk har _ ih => exact .loopBrk har ih
  | loopEsc har _ ho ih => exact .loopEsc har ih ho
  | ifOk _ hb har _ hvs _ ih₁ ih₂ ih₃ => exact .ifOk ih₁ hb har ih₂ hvs ih₃
  | ifBrk _ hb har _ ih₁ ih₂ => exact .ifBrk ih₁ hb har ih₂
  | ifEsc _ hb har _ ho ih₁ ih₂ => exact .ifEsc ih₁ hb har ih₂ ho
  | ifAbort _ ho ih => exact .ifAbort ih ho
  | callIndOk _ hres hfi hty hcall hvs _ ih₁ ih₂ =>
    exact .callIndOk ih₁ hres hfi hty (hC _ _ _ _ hcall) hvs ih₂
  | callIndRes _ hres ih => exact .callIndRes ih hres
  | callIndStop _ hres hfi hty hcall hfl ih =>
    exact .callIndStop ih hres hfi hty (hC _ _ _ _ hcall) hfl
  | callRefOk _ hfi hty hcall hvs _ ih₁ ih₂ =>
    exact .callRefOk ih₁ hfi hty (hC _ _ _ _ hcall) hvs ih₂
  | callRefNull _ ih => exact .callRefNull ih
  | callRefStop _ hfi hty hcall hfl ih => exact .callRefStop ih hfi hty (hC _ _ _ _ hcall) hfl
  | tail _ hres hfi hty ih => exact .tail ih hres hfi hty
  | tailRes _ hres ih => exact .tailRes ih hres
  | throw _ ht he hn ih => exact .throw ih ht he hn
  | throwRefNull _ ih => exact .throwRefNull ih
  | throwRefExn _ ih => exact .throwRefExn ih
  | tryOk har _ hvs _ ih₁ ih₂ => exact .tryOk har ih₁ hvs ih₂
  | tryBrk har _ ih => exact .tryBrk har ih
  | tryEsc har _ ho hnt ih => exact .tryEsc har ih ho hnt
  | tryCatch har _ hc ih => exact .tryCatch har ih hc
  | tryRethrow har _ hc ih => exact .tryRethrow har ih hc

/-- `FrameP` is monotone in its oracle. -/
theorem frameP_mono {C C' : CallRel H} (hC : C ≤ C') {x : Store H × POut} {y : Store H × Flow}
    (h : FrameP C x y) : FrameP C' x y := by
  cases h with
  | flow => exact .flow
  | tail hcall hfl => exact .tail (hC _ _ _ _ hcall) hfl

section Free

theorem xFreeL_op {i : Instr} {args es : List BExpr} (h : xFreeL (.op i args :: es) = true) :
    isXCall i = false ∧ xFreeL args = true ∧ xFreeL es = true := by
  simp_all [xFreeL, xFree]

theorem xFreeL_block {bt : BlockType} {body es : List BExpr}
    (h : xFreeL (.block bt body :: es) = true) : xFreeL body = true ∧ xFreeL es = true := by
  simp_all [xFreeL, xFree]

theorem xFreeL_loop {bt : BlockType} {body es : List BExpr}
    (h : xFreeL (.loop bt body :: es) = true) : xFreeL body = true ∧ xFreeL es = true := by
  simp_all [xFreeL, xFree]

theorem xFreeL_tryTable {bt : BlockType} {cs : List Catch} {body es : List BExpr}
    (h : xFreeL (.tryTable bt cs body :: es) = true) : xFreeL body = true ∧ xFreeL es = true := by
  simp_all [xFreeL, xFree]

theorem xFreeL_if {bt : BlockType} {c t el es : List BExpr} (b : Bool)
    (h : xFreeL (.if_ bt c t el :: es) = true) :
    xFreeL c = true ∧ xFreeL (if b then t else el) = true ∧ xFreeL es = true := by
  cases b <;> simp_all [xFreeL, xFree]

theorem tailRes_isXCall {s : Store H} {f : Frame} {i : Instr} {stk : List Val}
    {o : Option (Nat × List Val)} (h : TailRes s f i stk o) : isXCall i = true := by
  cases h <;> rfl

theorem notThrow_of {fl : Flow} (h : ∀ a, fl ≠ .throw a) : POut.NotThrow (.flow fl) := by
  cases fl <;> first | trivial | exact absurd rfl (h _)

end Free

/-- **Legacy coincidence, one way**: on code without the extended call forms, every `EvalOXE`
run is an `EvalOXP` run ending in the same flow. -/
theorem of_evalOXE {C : CallRel H} {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    {s' : Store H} {f' : Frame} {fl : Flow} (h : EvalOXE C s f stk es (s', f', fl)) :
    xFreeL es = true → EvalOXP C s f stk es (s', f', .flow fl) := by
  generalize hr : (s', f', fl) = r at h
  induction h generalizing s' f' fl with
  | nil => intro _; cases hr; exact .nil
  | argsAbort _ hfl ih => intro hx; cases hr; exact .argsAbort (ih rfl (xFreeL_op hx).2.1) hfl
  | callOk _ hfi hty hcall hvs _ ih₁ ih₂ =>
    intro hx; subst hr
    exact .callOk (ih₁ rfl (xFreeL_op hx).2.1) hfi hty hcall hvs (ih₂ rfl (xFreeL_op hx).2.2)
  | callTrap _ hfi hty hcall ih =>
    intro hx; cases hr; exact .callTrap (ih rfl (xFreeL_op hx).2.1) hfi hty hcall
  | callThrow _ hfi hty hcall ih =>
    intro hx; cases hr; exact .callThrow (ih rfl (xFreeL_op hx).2.1) hfi hty hcall
  | opOk hi _ hflat _ ih₁ ih₂ =>
    intro hx; subst hr
    exact .opOk hi (ih₁ rfl (xFreeL_op hx).2.1) hflat (ih₂ rfl (xFreeL_op hx).2.2)
  | opStop hi _ hflat hfl ih =>
    intro hx; cases hr; exact .opStop hi (ih rfl (xFreeL_op hx).2.1) hflat hfl
  | blockOk har _ hvs _ ih₁ ih₂ =>
    intro hx; subst hr
    exact .blockOk har (ih₁ rfl (xFreeL_block hx).1) hvs (ih₂ rfl (xFreeL_block hx).2)
  | blockBrk har _ ih => intro hx; cases hr; exact .blockBrk har (ih rfl (xFreeL_block hx).1)
  | blockEsc har _ hfl ih =>
    intro hx; cases hr; exact .blockEsc har (ih rfl (xFreeL_block hx).1) hfl
  | loopOk har _ _ ih₁ ih₂ =>
    intro hx; subst hr
    exact .loopOk har (ih₁ rfl (xFreeL_loop hx).1) (ih₂ rfl (xFreeL_loop hx).2)
  | loopBack har _ _ ih₁ ih₂ =>
    intro hx; subst hr
    exact .loopBack har (ih₁ rfl (xFreeL_loop hx).1) (ih₂ rfl hx)
  | loopBrk har _ ih => intro hx; cases hr; exact .loopBrk har (ih rfl (xFreeL_loop hx).1)
  | loopEsc har _ hfl ih => intro hx; cases hr; exact .loopEsc har (ih rfl (xFreeL_loop hx).1) hfl
  | @ifOk _ _ _ _ _ _ _ _ _ _ b _ _ _ _ _ _ _ _ _ _ hb har _ hvs _ ih₁ ih₂ ih₃ =>
    intro hx; subst hr
    obtain ⟨h1, h2, h3⟩ := xFreeL_if b hx
    exact .ifOk (ih₁ rfl h1) hb har (ih₂ rfl h2) hvs (ih₃ rfl h3)
  | @ifBrk _ _ _ _ _ _ _ _ _ _ b _ _ _ _ _ _ _ _ _ hb har _ ih₁ ih₂ =>
    intro hx; cases hr
    obtain ⟨h1, h2, -⟩ := xFreeL_if b hx
    exact .ifBrk (ih₁ rfl h1) hb har (ih₂ rfl h2)
  | @ifEsc _ _ _ _ _ _ _ _ _ b _ _ _ _ _ _ _ _ _ hb har _ hfl ih₁ ih₂ =>
    intro hx; cases hr
    obtain ⟨h1, h2, -⟩ := xFreeL_if b hx
    exact .ifEsc (ih₁ rfl h1) hb har (ih₂ rfl h2) hfl
  | ifAbort _ hfl ih => intro hx; cases hr; exact .ifAbort (ih rfl (xFreeL_if true hx).1) hfl
  | callIndOk => intro hx; simp [xFreeL, xFree, isXCall] at hx
  | callIndRes => intro hx; simp [xFreeL, xFree, isXCall] at hx
  | callIndStop => intro hx; simp [xFreeL, xFree, isXCall] at hx
  | callRefOk => intro hx; simp [xFreeL, xFree, isXCall] at hx
  | callRefNull => intro hx; simp [xFreeL, xFree, isXCall] at hx
  | callRefStop => intro hx; simp [xFreeL, xFree, isXCall] at hx
  | tail _ hres =>
    intro hx; have := (xFreeL_op hx).1; rw [tailRes_isXCall hres] at this; cases this
  | tailRes _ hres =>
    intro hx; have := (xFreeL_op hx).1; rw [tailRes_isXCall hres] at this; cases this
  | throw _ ht he hn ih => intro hx; cases hr; exact .throw (ih rfl (xFreeL_op hx).2.1) ht he hn
  | throwRefNull _ ih => intro hx; cases hr; exact .throwRefNull (ih rfl (xFreeL_op hx).2.1)
  | throwRefExn _ ih => intro hx; cases hr; exact .throwRefExn (ih rfl (xFreeL_op hx).2.1)
  | tryOk har _ hvs _ ih₁ ih₂ =>
    intro hx; subst hr
    exact .tryOk har (ih₁ rfl (xFreeL_tryTable hx).1) hvs (ih₂ rfl (xFreeL_tryTable hx).2)
  | tryBrk har _ ih => intro hx; cases hr; exact .tryBrk har (ih rfl (xFreeL_tryTable hx).1)
  | tryEsc har _ hfl hnt ih =>
    intro hx; cases hr
    exact .tryEsc har (ih rfl (xFreeL_tryTable hx).1) hfl (notThrow_of hnt)
  | tryCatch har _ hc ih => intro hx; cases hr; exact .tryCatch har (ih rfl (xFreeL_tryTable hx).1) hc
  | tryRethrow har _ hc ih =>
    intro hx; cases hr; exact .tryRethrow har (ih rfl (xFreeL_tryTable hx).1) hc

/-- **Legacy coincidence, the other way**: on code without the extended call forms, an `EvalOXP`
run never ends in a pending tail call, and is an `EvalOXE` run ending in the same flow. -/
theorem to_evalOXE {C : CallRel H} {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    {r : Store H × Frame × POut} (h : EvalOXP C s f stk es r) :
    xFreeL es = true → ∃ fl, r.2.2 = .flow fl ∧ EvalOXE C s f stk es (r.1, r.2.1, fl) := by
  induction h with
  | nil => exact fun _ => ⟨_, rfl, .nil⟩
  | argsAbort _ ho ih =>
    intro hx; obtain ⟨fl, rfl, d⟩ := ih (xFreeL_op hx).2.1; exact ⟨fl, rfl, .argsAbort d ho⟩
  | callOk _ hfi hty hcall hvs _ ih₁ ih₂ =>
    intro hx
    obtain ⟨_, h1, d1⟩ := ih₁ (xFreeL_op hx).2.1; cases h1
    obtain ⟨fl, h2, d2⟩ := ih₂ (xFreeL_op hx).2.2
    exact ⟨fl, h2, .callOk d1 hfi hty hcall hvs d2⟩
  | callTrap _ hfi hty hcall ih =>
    intro hx; obtain ⟨_, h1, d1⟩ := ih (xFreeL_op hx).2.1; cases h1
    exact ⟨_, rfl, .callTrap d1 hfi hty hcall⟩
  | callThrow _ hfi hty hcall ih =>
    intro hx; obtain ⟨_, h1, d1⟩ := ih (xFreeL_op hx).2.1; cases h1
    exact ⟨_, rfl, .callThrow d1 hfi hty hcall⟩
  | opOk hi _ hflat _ ih₁ ih₂ =>
    intro hx
    obtain ⟨_, h1, d1⟩ := ih₁ (xFreeL_op hx).2.1; cases h1
    obtain ⟨fl, h2, d2⟩ := ih₂ (xFreeL_op hx).2.2
    exact ⟨fl, h2, .opOk hi d1 hflat d2⟩
  | opStop hi _ hflat hfl ih =>
    intro hx; obtain ⟨_, h1, d1⟩ := ih (xFreeL_op hx).2.1; cases h1
    exact ⟨_, rfl, .opStop hi d1 hflat hfl⟩
  | blockOk har _ hvs _ ih₁ ih₂ =>
    intro hx
    obtain ⟨_, h1, d1⟩ := ih₁ (xFreeL_block hx).1; cases h1
    obtain ⟨fl, h2, d2⟩ := ih₂ (xFreeL_block hx).2
    exact ⟨fl, h2, .blockOk har d1 hvs d2⟩
  | blockBrk har _ ih =>
    intro hx; obtain ⟨_, h1, d1⟩ := ih (xFreeL_block hx).1; cases h1
    exact ⟨_, rfl, .blockBrk har d1⟩
  | blockEsc har _ ho ih =>
    intro hx; obtain ⟨fl, rfl, d1⟩ := ih (xFreeL_block hx).1
    exact ⟨fl, rfl, .blockEsc har d1 ho⟩
  | loopOk har _ _ ih₁ ih₂ =>
    intro hx
    obtain ⟨_, h1, d1⟩ := ih₁ (xFreeL_loop hx).1; cases h1
    obtain ⟨fl, h2, d2⟩ := ih₂ (xFreeL_loop hx).2
    exact ⟨fl, h2, .loopOk har d1 d2⟩
  | loopBack har _ _ ih₁ ih₂ =>
    intro hx
    obtain ⟨_, h1, d1⟩ := ih₁ (xFreeL_loop hx).1; cases h1
    obtain ⟨fl, h2, d2⟩ := ih₂ hx
    exact ⟨fl, h2, .loopBack har d1 d2⟩
  | loopBrk har _ ih =>
    intro hx; obtain ⟨_, h1, d1⟩ := ih (xFreeL_loop hx).1; cases h1
    exact ⟨_, rfl, .loopBrk har d1⟩
  | loopEsc har _ ho ih =>
    intro hx; obtain ⟨fl, rfl, d1⟩ := ih (xFreeL_loop hx).1
    exact ⟨fl, rfl, .loopEsc har d1 ho⟩
  | @ifOk _ _ _ _ _ _ _ _ _ _ b _ _ _ _ _ _ _ _ _ _ hb har _ hvs _ ih₁ ih₂ ih₃ =>
    intro hx
    obtain ⟨x1, x2, x3⟩ := xFreeL_if b hx
    obtain ⟨_, h1, d1⟩ := ih₁ x1; cases h1
    obtain ⟨_, h2, d2⟩ := ih₂ x2; cases h2
    obtain ⟨fl, h3, d3⟩ := ih₃ x3
    exact ⟨fl, h3, .ifOk d1 hb har d2 hvs d3⟩
  | @ifBrk _ _ _ _ _ _ _ _ _ _ b _ _ _ _ _ _ _ _ _ hb har _ ih₁ ih₂ =>
    intro hx
    obtain ⟨x1, x2, -⟩ := xFreeL_if b hx
    obtain ⟨_, h1, d1⟩ := ih₁ x1; cases h1
    obtain ⟨_, h2, d2⟩ := ih₂ x2; cases h2
    exact ⟨_, rfl, .ifBrk d1 hb har d2⟩
  | @ifEsc _ _ _ _ _ _ _ _ _ b _ _ _ _ _ _ _ _ _ hb har _ ho ih₁ ih₂ =>
    intro hx
    obtain ⟨x1, x2, -⟩ := xFreeL_if b hx
    obtain ⟨_, h1, d1⟩ := ih₁ x1; cases h1
    obtain ⟨fl, rfl, d2⟩ := ih₂ x2
    exact ⟨fl, rfl, .ifEsc d1 hb har d2 ho⟩
  | ifAbort _ ho ih =>
    intro hx; obtain ⟨fl, rfl, d1⟩ := ih (xFreeL_if true hx).1
    exact ⟨fl, rfl, .ifAbort d1 ho⟩
  | callIndOk => intro hx; simp [xFreeL, xFree, isXCall] at hx
  | callIndRes => intro hx; simp [xFreeL, xFree, isXCall] at hx
  | callIndStop => intro hx; simp [xFreeL, xFree, isXCall] at hx
  | callRefOk => intro hx; simp [xFreeL, xFree, isXCall] at hx
  | callRefNull => intro hx; simp [xFreeL, xFree, isXCall] at hx
  | callRefStop => intro hx; simp [xFreeL, xFree, isXCall] at hx
  | tail _ hres =>
    intro hx; have := (xFreeL_op hx).1; rw [tailRes_isXCall hres] at this; cases this
  | tailRes _ hres =>
    intro hx; have := (xFreeL_op hx).1; rw [tailRes_isXCall hres] at this; cases this
  | throw _ ht he hn ih =>
    intro hx; obtain ⟨_, h1, d1⟩ := ih (xFreeL_op hx).2.1; cases h1
    exact ⟨_, rfl, .throw d1 ht he hn⟩
  | throwRefNull _ ih =>
    intro hx; obtain ⟨_, h1, d1⟩ := ih (xFreeL_op hx).2.1; cases h1
    exact ⟨_, rfl, .throwRefNull d1⟩
  | throwRefExn _ ih =>
    intro hx; obtain ⟨_, h1, d1⟩ := ih (xFreeL_op hx).2.1; cases h1
    exact ⟨_, rfl, .throwRefExn d1⟩
  | tryOk har _ hvs _ ih₁ ih₂ =>
    intro hx
    obtain ⟨_, h1, d1⟩ := ih₁ (xFreeL_tryTable hx).1; cases h1
    obtain ⟨fl, h2, d2⟩ := ih₂ (xFreeL_tryTable hx).2
    exact ⟨fl, h2, .tryOk har d1 hvs d2⟩
  | tryBrk har _ ih =>
    intro hx; obtain ⟨_, h1, d1⟩ := ih (xFreeL_tryTable hx).1; cases h1
    exact ⟨_, rfl, .tryBrk har d1⟩
  | tryEsc har _ ho hnt ih =>
    intro hx; obtain ⟨fl, rfl, d1⟩ := ih (xFreeL_tryTable hx).1
    refine ⟨fl, rfl, .tryEsc har d1 ho fun a h => ?_⟩
    subst h; exact hnt
  | tryCatch har _ hc ih =>
    intro hx; obtain ⟨_, h1, d1⟩ := ih (xFreeL_tryTable hx).1; cases h1
    exact ⟨_, rfl, .tryCatch har d1 hc⟩
  | tryRethrow har _ hc ih =>
    intro hx; obtain ⟨_, h1, d1⟩ := ih (xFreeL_tryTable hx).1; cases h1
    exact ⟨_, rfl, .tryRethrow har d1 hc⟩

end Silmaril.Proofs.Wasm.Abstract.CallXP
