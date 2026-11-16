module

public import Silmaril.Wasm.Abstract.Recursion.Defs

/-!
# Recursion through internal calls, exposed and closed: proofs

Closing the open semantics by least fixpoint gives the recursive big-step
semantics back, and the closed call relation is its callee relation.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.Recursion

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract

variable {H : Type}

theorem funcs_of_func? {s : Store H} {f : Frame} {x : FuncIdx} {a : Nat} {fi : FuncInst H}
    (h : s.func? f x = some (a, fi)) : s.funcs[a]? = some fi := by
  unfold Store.func? at h
  rcases ha : f.module.funcs[x.toNat]? with _ | a'
  · simp [ha] at h
  · rcases hb : s.funcs[a']? with _ | fi'
    · simp [ha, hb] at h
    · simp only [ha, hb, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
        Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact hb

theorem closedCall_eq_bodyCall : (closedCall : CallRel H) = bodyCall closedCall :=
  (OrderHom.map_lfp bodyCallOp).symm

/-- The recursive semantics is the open semantics answered by the closure. -/
theorem evalO_of_eval {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    {r : Store H × Frame × Flow} (h : Eval s f stk es r) : EvalO closedCall s f stk es r := by
  have close : ∀ {s₁ : Store H} {f₁ : Frame} {x : FuncIdx} {a : Nat} {fi : FuncInst H} {fn : Func}
      {ps rs : List Validation.CValType} {args : List Val} {s₂ : Store H} {f₂ : Frame} {fl : Flow},
      s₁.func? f₁ x = some (a, fi) → fi.code = .wasm fn →
      Validation.DefType.funcType? fi.type = some (ps, rs) →
      EvalO closedCall s₁ (Frame.forCall fi.module args fn.locals) [] (liftInstrs fn.body)
        (s₂, f₂, fl) → closedCall s₁ a args (s₂, fl) := by
    intro s₁ f₁ x a fi fn ps rs args s₂ f₂ fl hfi hcode hty hb
    rw [closedCall_eq_bodyCall]
    exact ⟨fi, fn, ps, rs, f₂, funcs_of_func? hfi, hcode, hty, hb⟩
  induction h with
  | nil => exact .nil
  | argsAbort _ hfl ih => exact .argsAbort ih hfl
  | callOk _ hfi hcode hty _ hvs _ ih₁ ih₂ ih₃ =>
    exact .callOk ih₁ hfi hty (close hfi hcode hty ih₂) hvs ih₃
  | callTrap _ hfi hcode hty _ ih₁ ih₂ => exact .callTrap ih₁ hfi hty (close hfi hcode hty ih₂)
  | callThrow _ hfi hcode hty _ ih₁ ih₂ => exact .callThrow ih₁ hfi hty (close hfi hcode hty ih₂)
  | opOk hi _ hflat _ ih₁ ih₂ => exact .opOk hi ih₁ hflat ih₂
  | opStop hi _ hflat hfl ih => exact .opStop hi ih hflat hfl
  | blockOk har _ hvs _ ih₁ ih₂ => exact .blockOk har ih₁ hvs ih₂
  | blockBrk har _ ih => exact .blockBrk har ih
  | blockEsc har _ hfl ih => exact .blockEsc har ih hfl
  | loopOk har _ _ ih₁ ih₂ => exact .loopOk har ih₁ ih₂
  | loopBack har _ _ ih₁ ih₂ => exact .loopBack har ih₁ ih₂
  | loopBrk har _ ih => exact .loopBrk har ih
  | loopEsc har _ hfl ih => exact .loopEsc har ih hfl
  | ifOk _ hb har _ hvs _ ih₁ ih₂ ih₃ => exact .ifOk ih₁ hb har ih₂ hvs ih₃
  | ifBrk _ hb har _ ih₁ ih₂ => exact .ifBrk ih₁ hb har ih₂
  | ifEsc _ hb har _ hfl ih₁ ih₂ => exact .ifEsc ih₁ hb har ih₂ hfl
  | ifAbort _ hfl ih => exact .ifAbort ih hfl

/-- The open semantics answered by the recursive callee relation is the
recursive semantics. -/
theorem eval_of_evalO {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    {r : Store H × Frame × Flow} (h : EvalO evalCall s f stk es r) : Eval s f stk es r := by
  have open_ : ∀ {s₁ : Store H} {f₁ : Frame} {x : FuncIdx} {a : Nat} {fi : FuncInst H}
      {ps rs : List Validation.CValType} {args : List Val} {s₂ : Store H} {fl : Flow},
      s₁.func? f₁ x = some (a, fi) → Validation.DefType.funcType? fi.type = some (ps, rs) →
      evalCall s₁ a args (s₂, fl) →
      ∃ (fn : Func) (f₂ : Frame), fi.code = .wasm fn ∧
        Eval s₁ (Frame.forCall fi.module args fn.locals) [] (liftInstrs fn.body) (s₂, f₂, fl) := by
    intro s₁ f₁ x a fi ps rs args s₂ fl hfi hty ⟨fi', fn, ps', rs', f₂, hfi', hcode, hty', hb⟩
    obtain rfl : fi' = fi := Option.some.inj (hfi'.symm.trans (funcs_of_func? hfi))
    exact ⟨fn, f₂, hcode, hb⟩
  induction h with
  | nil => exact .nil
  | argsAbort _ hfl ih => exact .argsAbort ih hfl
  | callOk _ hfi hty hcall hvs _ ih₁ ih₂ =>
    obtain ⟨fn, f₂, hcode, hb⟩ := open_ hfi hty hcall
    exact .callOk ih₁ hfi hcode hty hb hvs ih₂
  | callTrap _ hfi hty hcall ih =>
    obtain ⟨fn, f₂, hcode, hb⟩ := open_ hfi hty hcall
    exact .callTrap ih hfi hcode hty hb
  | callThrow _ hfi hty hcall ih =>
    obtain ⟨fn, f₂, hcode, hb⟩ := open_ hfi hty hcall
    exact .callThrow ih hfi hcode hty hb
  | opOk hi _ hflat _ ih₁ ih₂ => exact .opOk hi ih₁ hflat ih₂
  | opStop hi _ hflat hfl ih => exact .opStop hi ih hflat hfl
  | blockOk har _ hvs _ ih₁ ih₂ => exact .blockOk har ih₁ hvs ih₂
  | blockBrk har _ ih => exact .blockBrk har ih
  | blockEsc har _ hfl ih => exact .blockEsc har ih hfl
  | loopOk har _ _ ih₁ ih₂ => exact .loopOk har ih₁ ih₂
  | loopBack har _ _ ih₁ ih₂ => exact .loopBack har ih₁ ih₂
  | loopBrk har _ ih => exact .loopBrk har ih
  | loopEsc har _ hfl ih => exact .loopEsc har ih hfl
  | ifOk _ hb har _ hvs _ ih₁ ih₂ ih₃ => exact .ifOk ih₁ hb har ih₂ hvs ih₃
  | ifBrk _ hb har _ ih₁ ih₂ => exact .ifBrk ih₁ hb har ih₂
  | ifEsc _ hb har _ hfl ih₁ ih₂ => exact .ifEsc ih₁ hb har ih₂ hfl
  | ifAbort _ hfl ih => exact .ifAbort ih hfl

theorem closedCall_le : (closedCall : CallRel H) ≤ evalCall := by
  refine OrderHom.lfp_le _ ?_
  rintro s a args out ⟨fi, fn, ps, rs, f₂, h₁, h₂, h₃, h₄⟩
  exact ⟨fi, fn, ps, rs, f₂, h₁, h₂, h₃, eval_of_evalO h₄⟩

theorem le_closedCall : (evalCall : CallRel H) ≤ closedCall := by
  rintro s a args out ⟨fi, fn, ps, rs, f₂, h₁, h₂, h₃, h₄⟩
  rw [closedCall_eq_bodyCall]
  exact ⟨fi, fn, ps, rs, f₂, h₁, h₂, h₃, evalO_of_eval h₄⟩

theorem closedCall_eq : (closedCall : CallRel H) = evalCall :=
  le_antisymm closedCall_le le_closedCall

theorem evalO_closed_iff {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    {r : Store H × Frame × Flow} : EvalO closedCall s f stk es r ↔ Eval s f stk es r :=
  ⟨fun h => eval_of_evalO (h.mono closedCall_le), evalO_of_eval⟩

end Silmaril.Proofs.Wasm.Abstract.Recursion
