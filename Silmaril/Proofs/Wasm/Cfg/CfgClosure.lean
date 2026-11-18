module

public import Silmaril.Wasm.Cfg.CfgClosure.Defs
public import Silmaril.Wasm.Cfg.CfgSession.Thms
public import Silmaril.Wasm.Cfg.MachineLDiv.Thms
public import Silmaril.Proofs.Wasm.Cfg.CfgClosureAns
public import Silmaril.Proofs.Wasm.Cfg.MachineLDivF

@[expose] public section

/-!
# The self-contained recursive CFG closure (H3, proofs)

* `cfgAns_eq`: the CFG closure's call answers are exactly the `CloseOk closedCallXP` entries:
  `MachineLClose.closeOk_of_session` one way, `CfgClosureAns.session_of_closeOk` the other, with
  `CfgSession.cfgEvFun_eq`.
* `le_funDivXP`: **every post-fixpoint `R ≤ FunDivLG (CloseOk closedCallXP) R` is native frame
  divergence**. Native coinduction on the pair `(E, R ∪ FunDivXP)`, `E` the greatest fixpoint of
  `X ↦ DivStepXP X (R ∪ FunDivXP)`: a member of `R` diverges by infinite local steps
  (`MachineLDiv.infK_div`, native divergence, which is in `E`), by a call into `R` (`reach_divG`,
  `MachineLDivF.reach_div` over any pre-fixpoint of the unfolding), or by a pending tail call into
  `R` (the closed run to it, `frameTail`).
* `cfgFunDiv_eq`: the greatest fixpoint `cfgFunDiv` is `FunDivXP`: `FunDivXP` is a post-fixpoint
  (`MachineLDiv.funDiv_machine`), and every post-fixpoint is below it (`le_funDivXP`).
-/

namespace Silmaril.Wasm.Cfg.Proofs.CfgClosure

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Machine Silmaril.Wasm.Cfg.MachineL
  Silmaril.Wasm.Cfg.CfgSession Silmaril.Wasm.Cfg.CfgClosure Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.Binaryen
open Silmaril.Wasm.Abstract (SCall ReachLXPS)
open Silmaril.Wasm.Interp (Problem)
open Silmaril.Wasm.Abstract.XRecursionP (closedCallXP)
open Silmaril.Wasm.Abstract.XDivergeP (EvalDivXP FunDivXP DivStepXP CallStepXP CallProblem
  divOpXP evalDivXP_iff_step funDivXP_iff_step)
open Silmaril.Wasm.Cfg.Proofs.MachineLClosed (AllOk logged_closed allOk_append allOk_cons
  allOk_nil)

variable {H : Type}

/-! ## Call answers -/

theorem cfgAns_eq : (cfgAns : SCall H → Prop) = CloseOk closedCallXP := by
  funext e
  apply propext
  rcases e with ⟨_ | ⟨g, args, s⟩, b, s₂⟩
  · exact Iff.rfl
  · show (([] : List (Call (Abstract.wasmHostSig H))), End.ret b s₂) ∈ cfgEvFunXPS s (g, args) ↔
      CloseOk closedCallXP (Abstract.SCall.mk g args s b s₂)
    rw [CfgSession.cfgEvFun_eq]
    exact ⟨MachineLClose.closeOk_of_session, CfgClosureAns.session_of_closeOk⟩

/-! ## Callee divergence -/

/-- **A pending call into a callee in `Y`, after oracle answers, is in any pre-fixpoint `X` of
the unfolding** (`MachineLDivF.reach_div` over `X`, `Y`). -/
theorem reach_divG {X : Problem H} {Y : CallProblem H}
    (hX : ∀ s f stk es, DivStepXP X Y s f stk es → X s f stk es)
    {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    {l : List (SCall H)} {z : (Abstract.wasmOShape H).self.Op} (h : ReachLXPS s f stk es l z)
    (hl : AllOk closedCallXP l) (hY : Y z.2.2 z.1 z.2.1) : X s f stk es := by
  induction h with
  | call hargs hfi hty => exact hX _ _ _ _ (.callee (logged_closed hargs hl) hfi hty hY)
  | ind hargs hres hfi hty hy =>
    exact hX _ _ _ _ (.callIndCallee (logged_closed hargs hl) hres hfi hty hy hY)
  | ref hargs hfi hty hy =>
    exact hX _ _ _ _ (.callRefCallee (logged_closed hargs hl) hfi hty hy hY)
  | args _ ih => exact hX _ _ _ _ (.args (ih hl hY))
  | callK hargs hfi hty _ ih =>
    obtain ⟨h₁, h₂⟩ := allOk_append.1 hl
    obtain ⟨he, h₃⟩ := allOk_cons.1 h₂
    have hd := logged_closed (Abstract.EvalLXPS.callRet (es := []) hargs hfi hty .nil)
      (allOk_append.2 ⟨h₁, allOk_cons.2 ⟨he, allOk_nil _⟩⟩)
    exact hX _ _ _ _ (.cont hd (ih h₃ hY))
  | indK hargs hres hfi hty hy _ ih =>
    obtain ⟨h₁, h₂⟩ := allOk_append.1 hl
    obtain ⟨he, h₃⟩ := allOk_cons.1 h₂
    have hd := logged_closed (Abstract.EvalLXPS.indRet (es := []) hargs hres hfi hty hy .nil)
      (allOk_append.2 ⟨h₁, allOk_cons.2 ⟨he, allOk_nil _⟩⟩)
    exact hX _ _ _ _ (.cont hd (ih h₃ hY))
  | refK hargs hfi hty hy _ ih =>
    obtain ⟨h₁, h₂⟩ := allOk_append.1 hl
    obtain ⟨he, h₃⟩ := allOk_cons.1 h₂
    have hd := logged_closed (Abstract.EvalLXPS.refRet (es := []) hargs hfi hty hy .nil)
      (allOk_append.2 ⟨h₁, allOk_cons.2 ⟨he, allOk_nil _⟩⟩)
    exact hX _ _ _ _ (.cont hd (ih h₃ hY))
  | opK hi hargs hflat _ ih =>
    obtain ⟨h₁, h₂⟩ := allOk_append.1 hl
    have hd := logged_closed (Abstract.EvalLXPS.opOk (es := []) hi hargs hflat .nil)
      (by simpa using h₁)
    exact hX _ _ _ _ (.cont hd (ih h₂ hY))
  | block har _ ih => exact hX _ _ _ _ (.block har (ih hl hY))
  | blockK har hbody hvs _ ih =>
    obtain ⟨h₁, h₂⟩ := allOk_append.1 hl
    have hd := logged_closed (Abstract.EvalLXPS.blockOk (es := []) har hbody hvs .nil)
      (by simpa using h₁)
    exact hX _ _ _ _ (.cont hd (ih h₂ hY))
  | loop har _ ih => exact hX _ _ _ _ (.loop har (ih hl hY))
  | loopK har hbody _ ih =>
    obtain ⟨h₁, h₂⟩ := allOk_append.1 hl
    have hd := logged_closed (Abstract.EvalLXPS.loopOk (es := []) har hbody .nil)
      (by simpa using h₁)
    exact hX _ _ _ _ (.cont hd (ih h₂ hY))
  | loopBack har hbody _ ih =>
    obtain ⟨h₁, h₂⟩ := allOk_append.1 hl
    exact hX _ _ _ _ (.loopBack har (logged_closed hbody h₁) (ih h₂ hY))
  | cond _ ih => exact hX _ _ _ _ (.cond (ih hl hY))
  | arm hc hb har _ ih =>
    obtain ⟨h₁, h₂⟩ := allOk_append.1 hl
    exact hX _ _ _ _ (.arm (logged_closed hc h₁) hb har (ih h₂ hY))
  | ifK hc hb har harm hvs _ ih =>
    obtain ⟨h₁₂, h₃⟩ := allOk_append.1 hl
    have hd := logged_closed (Abstract.EvalLXPS.ifOk (es := []) hc hb har harm hvs .nil)
      (by simpa using h₁₂)
    exact hX _ _ _ _ (.cont hd (ih h₃ hY))
  | handler har _ ih => exact hX _ _ _ _ (.try_ har (ih hl hY))
  | @tryK _ _ _ _ _ _ _ cs _ _ _ _ _ _ _ _ har hbody hvs _ ih =>
    obtain ⟨h₁, h₂⟩ := allOk_append.1 hl
    have hd := logged_closed (Abstract.EvalLXPS.tryOk (es := []) (cs := cs) har hbody hvs .nil)
      (by simpa using h₁)
    exact hX _ _ _ _ (.cont hd (ih h₂ hY))

/-- The unfolding of a problem's divergence with callee divergence `Y` fixed. -/
def opE (Y : CallProblem H) : Problem H →o Problem H where
  toFun X := DivStepXP X Y
  monotone' _ _ h _ _ _ _ hd := DivStepXP.mono h le_rfl hd

theorem opE_unfold {Y : CallProblem H} :
    (opE Y).gfp = DivStepXP (opE Y).gfp Y :=
  ((opE Y).map_gfp).symm

theorem evalDivXP_le_opE {Y : CallProblem H} (hY : FunDivXP ≤ Y) :
    (EvalDivXP : Problem H) ≤ (opE Y).gfp :=
  OrderHom.le_gfp _ fun _ _ _ _ h => DivStepXP.mono le_rfl hY (evalDivXP_iff_step.1 h)

/-- **Every post-fixpoint of `FunDivLG (CloseOk closedCallXP)` is native frame divergence.** -/
theorem le_funDivXP {R : CallProblem H}
    (hR : ∀ s a args, R s a args → FunDivLG (CloseOk closedCallXP) R s a args) :
    R ≤ FunDivXP := by
  let Y : CallProblem H := fun s a args => R s a args ∨ FunDivXP s a args
  let E : Problem H := (opE Y).gfp
  have hYF : FunDivXP ≤ Y := fun _ _ _ h => Or.inr h
  have hEv : (EvalDivXP : Problem H) ≤ E := evalDivXP_le_opE hYF
  have hfold : ∀ s f stk es, DivStepXP E Y s f stk es → E s f stk es := fun s f stk es h => by
    show (opE Y).gfp s f stk es
    rw [opE_unfold]
    exact h
  have hpost : ((E, Y) : Problem H × CallProblem H) ≤ divOpXP (E, Y) := by
    refine ⟨fun s f stk es h => ?_, fun s a args h => ?_⟩
    · show DivStepXP E Y s f stk es
      have : (opE Y).gfp s f stk es := h
      rw [opE_unfold] at this
      exact this
    · show CallStepXP E Y s a args
      rcases h with h | h
      · obtain ⟨fi, fn, hfi, hcode, (hI | hC) | hT⟩ := hR s a args h
        · exact .body hfi hcode (hEv _ _ _ _ (MachineL.infK_div hI))
        · obtain ⟨st, l, z, hr, hRe, hl, hz⟩ := hC
          obtain ⟨l₁, hrun, hl₁⟩ := MachineLDivF.stepK_run hr
          exact .body hfi hcode (reach_divG hfold
            (MachineLPend.pending_iff.2 ⟨st, l₁, l, hrun, hRe, rfl⟩)
            (allOk_append.2 ⟨hl₁, hl⟩) (Or.inl hz))
        · obtain ⟨st, l, s₁, f₁, a', n, args', hr, hTl, hl, hz⟩ := hT
          obtain ⟨l₁, hrun, hl₁⟩ := MachineLDivF.stepK_run hr
          exact .frameTail hfi hcode (logged_closed (MachineLFwd.forward_tail hrun hTl)
            (allOk_append.2 ⟨hl₁, hl⟩)) (Or.inl hz)
      · exact CallStepXP.mono hEv hYF (funDivXP_iff_step.1 h)
  have hle := OrderHom.le_gfp divOpXP hpost
  exact fun s a args h => hle.2 s a args (Or.inl h)

/-- **The CFG closure's callee divergence is native frame divergence.** -/
theorem cfgFunDiv_eq : (cfgFunDiv : Store H → Nat → List Val → Prop) = FunDivXP := by
  funext s a args
  apply propext
  constructor
  · rintro ⟨R, hR, h⟩
    rw [cfgAns_eq] at hR
    exact le_funDivXP hR s a args h
  · intro h
    refine ⟨FunDivXP, fun s' a' args' h' => ?_, h⟩
    rw [cfgAns_eq]
    exact MachineL.funDiv_machine h'

/-! ## The triple -/

theorem ldlcfgC_eq : (LDLcfgC : (Abstract.wasmHShape H).self.Op → List (Abstract.HCall H) → Prop) =
    LDLcfg := by
  unfold LDLcfgC LDLcfg
  rw [cfgAns_eq, cfgFunDiv_eq]
  rfl

theorem cfgEvFunDC_eq : (cfgEvFunDXPC : AFun (Abstract.wasmHostSig H) (Store H)
    (Nat × List Val) (List Val ⊕ Nat)) = cfgEvFunDXP := by
  unfold cfgEvFunDXPC cfgEvFunDXP
  rw [ldlcfgC_eq]

theorem cfgSessionTripleC_eq :
    (cfgSessionTripleC : ObsTriple (Abstract.wasmHostSig H) (Store H) (Nat × List Val)
      ((List Val ⊕ Nat) ⊕ PUnit.{1})) = Abstract.sessionTripleXP := by
  rw [← CfgSession.cfgSessionTriple_eq]
  unfold cfgSessionTripleC cfgSessionTriple cfgEvFunDXPSC cfgEvFunDXPS
  rw [cfgEvFunDC_eq]

end Silmaril.Wasm.Cfg.Proofs.CfgClosure
