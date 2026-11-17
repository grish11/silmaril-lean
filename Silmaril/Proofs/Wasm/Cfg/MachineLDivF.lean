module

public import Silmaril.Proofs.Wasm.Cfg.MachineLDivB

@[expose] public section

/-!
# Machine divergence into callees is native divergence (H2, proofs)

`reach_div`: a native pending call, reached after oracle-answered calls, whose callee diverges at
the frame, is native host-free divergence of the code (`XDivergeP.EvalDivXP`). `calleeDiv_div`:
the machine's diverging-callee divergence from the CFG entry is native divergence of the body.
`tailDiv_tail`: the machine's diverging tail callee is a closed native run of the body to that
pending tail call.
-/

namespace Silmaril.Wasm.Cfg.Proofs.MachineLDivF

open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Machine Silmaril.Wasm.Cfg.MachineL
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Binaryen
open Silmaril.Wasm.Abstract (EvalLXPS SCall ReachLXPS)
open Silmaril.Wasm.Abstract.CallXP (POut EvalOXP)
open Silmaril.Wasm.Abstract.XRecursionP (closedCallXP)
open Silmaril.Wasm.Abstract.XDivergeP (EvalDivXP FunDivXP DivStepXP evalDivXP_iff_step)
open Silmaril.Wasm.Cfg.Proofs.MachineLClosed (AllOk logged_closed closed_logged allOk_append
  allOk_cons allOk_nil)

variable {H : Type}

/-- **A pending call into a diverging callee, after oracle answers, is native divergence.** -/
theorem reach_div {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    {l : List (SCall H)} {z : (Abstract.wasmOShape H).self.Op} (h : ReachLXPS s f stk es l z)
    (hl : AllOk closedCallXP l) (hY : FunDivXP z.2.2 z.1 z.2.1) : EvalDivXP s f stk es := by
  induction h with
  | call hargs hfi hty => exact evalDivXP_iff_step.2 (.callee (logged_closed hargs hl) hfi hty hY)
  | ind hargs hres hfi hty hy =>
    exact evalDivXP_iff_step.2 (.callIndCallee (logged_closed hargs hl) hres hfi hty hy hY)
  | ref hargs hfi hty hy =>
    exact evalDivXP_iff_step.2 (.callRefCallee (logged_closed hargs hl) hfi hty hy hY)
  | args _ ih => exact evalDivXP_iff_step.2 (.args (ih hl hY))
  | callK hargs hfi hty _ ih =>
    obtain ⟨h₁, h₂⟩ := allOk_append.1 hl
    obtain ⟨he, h₃⟩ := allOk_cons.1 h₂
    have hd := logged_closed (EvalLXPS.callRet (es := []) hargs hfi hty .nil)
      (allOk_append.2 ⟨h₁, allOk_cons.2 ⟨he, allOk_nil _⟩⟩)
    exact evalDivXP_iff_step.2 (.cont hd (ih h₃ hY))
  | indK hargs hres hfi hty hy _ ih =>
    obtain ⟨h₁, h₂⟩ := allOk_append.1 hl
    obtain ⟨he, h₃⟩ := allOk_cons.1 h₂
    have hd := logged_closed (EvalLXPS.indRet (es := []) hargs hres hfi hty hy .nil)
      (allOk_append.2 ⟨h₁, allOk_cons.2 ⟨he, allOk_nil _⟩⟩)
    exact evalDivXP_iff_step.2 (.cont hd (ih h₃ hY))
  | refK hargs hfi hty hy _ ih =>
    obtain ⟨h₁, h₂⟩ := allOk_append.1 hl
    obtain ⟨he, h₃⟩ := allOk_cons.1 h₂
    have hd := logged_closed (EvalLXPS.refRet (es := []) hargs hfi hty hy .nil)
      (allOk_append.2 ⟨h₁, allOk_cons.2 ⟨he, allOk_nil _⟩⟩)
    exact evalDivXP_iff_step.2 (.cont hd (ih h₃ hY))
  | opK hi hargs hflat _ ih =>
    obtain ⟨h₁, h₂⟩ := allOk_append.1 hl
    have hd := logged_closed (EvalLXPS.opOk (es := []) hi hargs hflat .nil) (by simpa using h₁)
    exact evalDivXP_iff_step.2 (.cont hd (ih h₂ hY))
  | block har _ ih => exact evalDivXP_iff_step.2 (.block har (ih hl hY))
  | blockK har hbody hvs _ ih =>
    obtain ⟨h₁, h₂⟩ := allOk_append.1 hl
    have hd := logged_closed (EvalLXPS.blockOk (es := []) har hbody hvs .nil) (by simpa using h₁)
    exact evalDivXP_iff_step.2 (.cont hd (ih h₂ hY))
  | loop har _ ih => exact evalDivXP_iff_step.2 (.loop har (ih hl hY))
  | loopK har hbody _ ih =>
    obtain ⟨h₁, h₂⟩ := allOk_append.1 hl
    have hd := logged_closed (EvalLXPS.loopOk (es := []) har hbody .nil) (by simpa using h₁)
    exact evalDivXP_iff_step.2 (.cont hd (ih h₂ hY))
  | loopBack har hbody _ ih =>
    obtain ⟨h₁, h₂⟩ := allOk_append.1 hl
    exact evalDivXP_iff_step.2 (.loopBack har (logged_closed hbody h₁) (ih h₂ hY))
  | cond _ ih => exact evalDivXP_iff_step.2 (.cond (ih hl hY))
  | arm hc hb har _ ih =>
    obtain ⟨h₁, h₂⟩ := allOk_append.1 hl
    exact evalDivXP_iff_step.2 (.arm (logged_closed hc h₁) hb har (ih h₂ hY))
  | ifK hc hb har harm hvs _ ih =>
    obtain ⟨h₁₂, h₃⟩ := allOk_append.1 hl
    have hd := logged_closed (EvalLXPS.ifOk (es := []) hc hb har harm hvs .nil) (by simpa using h₁₂)
    exact evalDivXP_iff_step.2 (.cont hd (ih h₃ hY))
  | handler har _ ih => exact evalDivXP_iff_step.2 (.try_ har (ih hl hY))
  | @tryK _ _ _ _ _ _ _ cs _ _ _ _ _ _ _ _ har hbody hvs _ ih =>
    obtain ⟨h₁, h₂⟩ := allOk_append.1 hl
    have hd := logged_closed (EvalLXPS.tryOk (es := []) (cs := cs) har hbody hvs .nil) (by simpa using h₁)
    exact evalDivXP_iff_step.2 (.cont hd (ih h₂ hY))

/-- Oracle-answered steps are a logged run with oracle-answered entries. -/
theorem stepK_run {body : Expr} {st st' : MState H}
    (h : Relation.ReflTransGen (StepK body) st st') :
    ∃ l, MRunL body st l st' ∧ AllOk closedCallXP l := by
  induction h with
  | refl => exact ⟨[], .refl _, allOk_nil _⟩
  | tail _ hs ih =>
    obtain ⟨l, hr, hl⟩ := ih
    obtain ⟨l', hs, hl'⟩ := hs
    exact ⟨l ++ l', MachineLPend.mrun_snoc hr hs, allOk_append.2 ⟨hl, hl'⟩⟩

/-- **A diverging callee reached from the CFG entry is native divergence of the body.** -/
theorem calleeDiv_div {body : Expr} {s : Store H} {f : Frame}
    (h : CalleeDivK body (initial body s f)) : EvalDivXP s f [] (liftInstrs body) := by
  obtain ⟨st, l, z, hr, hR, hl, hY⟩ := h
  obtain ⟨l₁, hrun, hl₁⟩ := stepK_run hr
  exact reach_div (MachineLPend.pending_iff.2 ⟨st, l₁, l, hrun, hR, rfl⟩)
    (allOk_append.2 ⟨hl₁, hl⟩) hY

/-- **A diverging tail callee reached from the CFG entry**: the body runs, closed, to that pending
tail call. -/
theorem tailDiv_tail {body : Expr} {s : Store H} {f : Frame}
    (h : TailDivK body (initial body s f)) :
    ∃ (s₁ : Store H) (f₂ : Frame) (a' : Nat) (args' : List Val) (n : Nat),
      EvalOXP closedCallXP s f [] (liftInstrs body) (s₁, f₂, .tail a' args' n) ∧
        FunDivXP s₁ a' args' := by
  obtain ⟨st, l, s₁, f₁, a, n, args, hr, hT, hl, hY⟩ := h
  obtain ⟨l₁, hrun, hl₁⟩ := stepK_run hr
  exact ⟨s₁, f₁, a, args, n, logged_closed (MachineLFwd.forward_tail hrun hT)
    (allOk_append.2 ⟨hl₁, hl⟩), hY⟩

/-- **A closed native run of the body to a pending tail call is a machine run to it.** -/
theorem tail_tailL {body : Expr} {s s₁ : Store H} {f f₂ : Frame} {a' n : Nat} {args' : List Val}
    (h : EvalOXP closedCallXP s f [] (liftInstrs body) (s₁, f₂, .tail a' args' n)) :
    ∃ (st : MState H) (l : List (SCall H)), Relation.ReflTransGen (StepK body) (initial body s f) st ∧
      TailL body st l (s₁, f₂, .tail a' args' n) ∧ ∀ e ∈ l, CloseOk closedCallXP e := by
  obtain ⟨L, hL, hok⟩ := closed_logged h
  obtain ⟨st, l₁, l₂, hrun, rfl, hend⟩ := MachineLBwd.backward hL (by simp)
  obtain ⟨h₁, h₂⟩ := allOk_append.1 hok
  rcases hend with ⟨hs, -, hE⟩ | hT
  · obtain ⟨node, stk, ls, s', f'⟩ := st
    cases node <;> simp [Target.IsSink, EndRel] at hs hE
  · exact ⟨st, l₂, MachineLDivB.run_stepK hrun h₁, hT, h₂⟩

end Silmaril.Wasm.Cfg.Proofs.MachineLDivF
