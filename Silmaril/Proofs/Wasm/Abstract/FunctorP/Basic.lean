module

public import Silmaril.Wasm.Abstract.FunctorP.Defs
public import Silmaril.Proofs.Wasm.Abstract.ExposeP.Frame
public import Silmaril.Proofs.Wasm.Abstract.XDecomp.Pend
public import Silmaril.Wasm.Abstract.ExposePStruct.Thms

/-!
Proofs for `Silmaril.Wasm.Abstract.FunctorP.Thms`, the forward direction: every logged run
(`EvalLXP`) is a path of the exposed body `ExposeP.denListXP` with exactly its log
(`evalLXP_path`), every logged pending observation (`ReachXP`) a pending call of it
(`reachXP_pend`), and the same at the frame (`frameLXP_path`, `frameReachXP_pend`).

Operators that make no call event have *quiet* trees (`Quiet`: a return or silent divergence),
so their paths have an empty log and they have no pending call.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.FunctorP

open Silmaril.Wasm Silmaril.Games Silmaril.Games.Abstract Silmaril.Wasm.Abstract
  Silmaril.Wasm.Abstract.Body Silmaril.Wasm.Abstract.BodyTrace Silmaril.Wasm.Binaryen
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract.StoreBody Silmaril.Wasm.Abstract.StoreCall
  Silmaril.Wasm.Abstract.CallX Silmaril.Wasm.Abstract.CallXP Silmaril.Wasm.Abstract.ExposeE
  Silmaril.Wasm.Abstract.ExposeP Silmaril.Wasm.Abstract.FunctorP
  Silmaril.Elgot.ITree Silmaril.Proofs.Wasm.Abstract.StoreBody
  Silmaril.Proofs.Wasm.Abstract.BodyTrace Silmaril.Proofs.Wasm.Abstract.StoreCall
  Silmaril.Proofs.Wasm.Abstract.CallX Silmaril.Proofs.Wasm.Abstract.ExposeE
  Silmaril.Proofs.Wasm.Abstract.ExposeP
open Silmaril.Wasm.Abstract.CallXT (typeArity tailAnn)
open Silmaril.Wasm.Abstract.CallXE (ehInstr)

variable {H : Type}

/-! ## Block exits -/

theorem blockOutP_eq (np nr : Nat) (stk : List Val) (o : POut) :
    blockOutP np nr stk o = blockFlowP np nr stk o := by
  rcases o with fl | _
  · cases fl with
    | brk k vs => cases k <;> rfl
    | _ => rfl
  · rfl

theorem loopOutP_of_ne {np nr : Nat} {stk : List Val} {f₁ : Frame} {o : POut}
    (hb : ∀ vs, o ≠ .flow (.brk 0 vs)) :
    loopOutP np nr stk f₁ o = .inl ⟨(f₁, blockOutP np nr stk o)⟩ := by
  rcases o with fl | _
  · cases fl with
    | brk k vs =>
      cases k with
      | zero => exact absurd rfl (hb vs)
      | succ k => rfl
    | _ => rfl
  · rfl

theorem blockOutP_trap {np nr : Nat} {stk : List Val} {o : POut} :
    blockOutP np nr stk o = .flow .trap ↔ o = .flow .trap := by
  rw [blockOutP_eq]; exact blockFlowP_trap

/-! ## Quiet trees -/

/-- A tree without events: a return or silent divergence. -/
def Quiet {Y : Type 1} (t : Tree (SigEv (CallSig H)) Y) : Prop :=
  t = diverge ∨ ∃ v, t = ret v

theorem Quiet.path_nil {Y : Type 1} {t : Tree (SigEv (CallSig H)) Y} (hq : Quiet t)
    {cs : List (Call (CallSig H))} {e : PathEnd Y} (h : Path t cs e) : cs = [] := by
  rcases hq with rfl | ⟨v, rfl⟩
  · exact (path_diverge_inv h).1
  · exact (path_ret_inv rfl h).1

theorem Quiet.not_pend {Y : Type 1} {t : Tree (SigEv (CallSig H)) Y} (hq : Quiet t)
    {cs : List (Call (CallSig H))} {m : (CallSig H).Op} : ¬ Pend t cs m := by
  rcases hq with rfl | ⟨v, rfl⟩
  · exact not_pend_diverge
  · exact not_pend_ret

theorem quiet_liftP {x : M (CallSig H) H Res} {s : St H} (h : Quiet (run' x s)) :
    Quiet (run' (liftP x) s) := by
  unfold liftP
  rw [StoreBody.run_bind]
  rcases h with h | ⟨v, h⟩
  · rw [h, diverge_bind]; exact .inl rfl
  · rw [h, show (ret v >>= _ : Tree (SigEv (CallSig H)) _) = _ from pure_bind _ _]
    rcases v with e | ⟨a, s'⟩
    · exact .inr ⟨_, rfl⟩
    · exact .inr ⟨_, rfl⟩

theorem quiet_flatK {i : Instr} {f : Frame} {stk : List Val} {s : Store H} :
    Quiet (run' (flatK i f stk : M (CallSig H) H Res) ⟨s⟩) := by
  rw [show run' (flatK i f stk : M (CallSig H) H Res) ⟨s⟩ = evalTree (evalFlat s f stk i) from
    run_flatK i f stk s]
  rcases evalFlat s f stk i with _ | ⟨s', f', fl⟩
  · exact .inl rfl
  · cases fl <;> exact .inr ⟨_, rfl⟩

theorem quiet_throwEv {x : TagIdx} {f : Frame} {stk : List Val} {s : Store H} :
    Quiet (run' (throwEv x f stk : M (CallSig H) H Res) ⟨s⟩) := by
  rw [throwEv, run_getState_bind]
  split
  · exact .inr ⟨_, run_set_pure _ _ _⟩
  · exact .inl rfl

theorem quiet_throwRefEv {f : Frame} {stk : List Val} {s : Store H} :
    Quiet (run' (throwRefEv f stk : M (CallSig H) H Res) ⟨s⟩) := by
  unfold throwRefEv
  split
  · exact .inr ⟨_, run_trapS _⟩
  · exact .inr ⟨_, rfl⟩
  · exact .inl rfl

theorem quiet_tailPendEv {i : Instr} {f : Frame} {stk : List Val} {s : Store H} :
    Quiet (run' (tailPendEv i f stk : M (CallSig H) H ResP) ⟨s⟩) := by
  rw [tailPendEv, run_getState_bind]
  repeat' split
  all_goals first
    | exact .inl rfl
    | exact .inr ⟨_, rfl⟩
    | exact .inr ⟨_, run_trapS _⟩

theorem quiet_opCXP {i : Instr} (hi : callEvInstr i = false) (f : Frame) (stk : List Val)
    (s : Store H) : Quiet (run' (opCXP i f stk : M (CallSig H) H ResP) ⟨s⟩) := by
  by_cases ht : isXTail i
  · rw [opCXP_tail ht]; exact quiet_tailPendEv
  have hx : isXCall i = false := by
    cases i <;> simp_all [isXCall, isXTail, callEvInstr]
  rw [opCXP_notX hx]
  apply quiet_liftP
  have hc : ∀ x, i ≠ .call x := by
    rintro x rfl; simp [callEvInstr] at hi
  cases hE : ehInstr i
  · rw [opCXE_flat hc hx hE]; exact quiet_flatK
  · have : (∃ x, i = .throw x) ∨ i = .throwRef := by cases i <;> simp_all [ehInstr]
    rcases this with ⟨x, rfl⟩ | rfl
    · exact quiet_throwEv
    · exact quiet_throwRefEv

/-! ## Equations -/

theorem run_denListXP_single (e : BExpr) (f : Frame) (stk : List Val) (s : St H) :
    run' (denListXP [e] f stk : M (CallSig H) H ResP) s = run' (denXP e f stk) s := by
  rw [Silmaril.Wasm.Abstract.ExposePStruct.denListXP_singleton]

theorem run_denListXP_op (i : Instr) (f : Frame) (stk : List Val) (s : St H) :
    run' (denListXP [.op i []] f stk : M (CallSig H) H ResP) s = run' (opCXP i f stk) s := by
  rw [Silmaril.Wasm.Abstract.ExposePStruct.denListXP_singleton, denXP_op,
    Silmaril.Wasm.Abstract.ExposePStruct.denListXP_nil, pure_bind]
  rfl

/-! ## Answers -/

theorem ansOut_path {f : Frame} {stk : List Val} {ps rs : List Validation.CValType}
    {ans : Store H × Flow} {r : Store H × Frame × POut} (hr : ansOut f stk ps rs ans = some r)
    (s : St H) :
    ∃ fl, r = (r.1, f, .flow fl) ∧ Path (run' (callAns f stk ps rs ans) s) [] (endR (r.1, f, fl)) := by
  obtain ⟨s₂, fl⟩ := ans
  cases fl with
  | trap => cases hr; exact ⟨_, rfl, path_callAns_trap _⟩
  | throw t => cases hr; exact ⟨_, rfl, path_callAns_throw _⟩
  | normal ws => cases hr; exact ⟨_, rfl, path_callAns_vals rfl _⟩
  | ret ws => cases hr; exact ⟨_, rfl, path_callAns_vals rfl _⟩
  | brk k ws =>
    cases k with
    | zero => cases hr; exact ⟨_, rfl, path_callAns_vals rfl _⟩
    | succ k => simp [ansOut, Flow.retVals] at hr

theorem path_liftP_ans {x : M (CallSig H) H Res} {f : Frame} {stk : List Val}
    {ps rs : List Validation.CValType} {ans : Store H × Flow} {r : Store H × Frame × POut}
    {s : St H} {cs : List (Call (CallSig H))}
    (hr : ansOut f stk ps rs ans = some r)
    (hx : ∀ e, Path (run' (callAns f stk ps rs ans) s) [] e → Path (run' x s) cs e) :
    Path (run' (liftP x) s) cs (endRP r) := by
  obtain ⟨fl, hr', hp⟩ := ansOut_path hr s
  rw [hr']
  exact path_liftP (hx _ hp)

section
variable {C : CallRel H}

/-- A logged operator head is a path of the operator with exactly its log. -/
theorem headL_path {s₁ : Store H} {f₁ : Frame} {stk₁ : List Val} {i : Instr}
    {cs : List (Call (CallSig H))} {r : Store H × Frame × POut} (h : HeadL C s₁ f₁ stk₁ i cs r) :
    Answered C cs ∧ Path (run' (opCXP i f₁ stk₁ : M (CallSig H) H ResP) ⟨s₁⟩) cs (endRP r) := by
  cases h with
  | quiet hi h =>
    obtain ⟨cs', -, hp⟩ := evalOXP_path h
    rw [run_denListXP_op] at hp
    obtain rfl := (quiet_opCXP hi f₁ stk₁ s₁).path_nil hp
    exact ⟨answered_nil, hp⟩
  | call hfi hty hC hr =>
    refine ⟨answered_single hC, ?_⟩
    exact path_liftP_ans (x := callEv _ f₁ stk₁) hr fun e hp => path_callEv hfi hty _ hp
  | ind hres hfi hty hy hC hr =>
    refine ⟨answered_single hC, ?_⟩
    refine path_liftP_ans (x := indEvT _ _ f₁ stk₁) hr fun e hp => ?_
    rw [indEvT, run_getState_bind, resolveInd_eq hres]
    exact path_callAtT hfi hty hy _ hp
  | indNone hres =>
    refine ⟨answered_nil, ?_⟩
    show Path (run' (liftP (indEvT _ _ f₁ stk₁)) ⟨s₁⟩) [] (endRP (s₁, f₁, .flow .trap))
    refine path_liftP (fl := .trap) (s₁ := s₁) ?_
    rw [indEvT, run_getState_bind, resolveInd_eq hres]
    exact .ret (run_trapS _)
  | ref hstk hfi hty hy hC hr =>
    subst hstk
    refine ⟨answered_single hC, ?_⟩
    refine path_liftP_ans (x := refEvT _ f₁ _) hr fun e hp => ?_
    exact path_callAtT hfi hty hy _ hp
  | refNull hstk =>
    subst hstk
    refine ⟨answered_nil, ?_⟩
    show Path (run' (liftP (refEvT _ f₁ _)) ⟨s₁⟩) [] (endRP (s₁, f₁, .flow .trap))
    exact path_liftP (fl := .trap) (s₁ := s₁) (.ret (run_trapS _))

/-- **Logged runs are paths** of the exposed body, with exactly their log. -/
theorem evalLXP_path {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    {cs : List (Call (CallSig H))} {r : Store H × Frame × POut} (h : EvalLXP C s f stk es cs r) :
    Answered C cs ∧ Path (run' (denListXP es f stk : M (CallSig H) H ResP) ⟨s⟩) cs (endRP r) := by
  induction h with
  | nil => exact ⟨answered_nil, .ret rfl⟩
  | cons _ _ ih₁ ih₂ =>
    obtain ⟨hA₁, hp₁⟩ := ih₁
    obtain ⟨hA₂, hp₂⟩ := ih₂
    rw [run_denListXP_single] at hp₁
    refine ⟨answered_append hA₁ hA₂, ?_⟩
    rw [denListXP_cons]
    exact path_thenKP_normal hp₁ hp₂
  | @stop s f stk e es cs r _ hn ih =>
    obtain ⟨hA, hp⟩ := ih
    rw [run_denListXP_single] at hp
    refine ⟨hA, ?_⟩
    rw [denListXP_cons]
    obtain ⟨s₁, f₁, o⟩ := r
    exact path_thenKP_pass hp hn
  | argsStop _ ho ih =>
    obtain ⟨hA, hp⟩ := ih
    refine ⟨hA, ?_⟩
    rw [run_denListXP_single, denXP_op]
    exact path_thenKP_pass hp ho
  | head _ hh ih =>
    obtain ⟨hA₁, hp₁⟩ := ih
    obtain ⟨hA₂, hp₂⟩ := headL_path hh
    refine ⟨answered_append hA₁ hA₂, ?_⟩
    rw [run_denListXP_single, denXP_op]
    exact path_thenKP_normal hp₁ hp₂
  | @block s s₁ f f₁ stk bt body np nr cs o har _ ih =>
    obtain ⟨hA, hp⟩ := ih
    refine ⟨hA, ?_⟩
    rw [run_denListXP_single, denXP_block]
    simp only [har]
    rw [blockOutP_eq]
    exact path_blockKP hp
  | @loopBack s s₁ f f₁ stk vs bt body np nr cs₁ cs₂ r har _ _ ih₁ ih₂ =>
    obtain ⟨hA₁, hp₁⟩ := ih₁
    obtain ⟨hA₂, hp₂⟩ := ih₂
    refine ⟨answered_append hA₁ hA₂, ?_⟩
    rw [run_denListXP_single] at hp₂ ⊢
    rw [denXP_loop_unfold]
    have h1 : Path (run' (loopBodyXP bt body ⟨(f, stk)⟩) ⟨s⟩) cs₁
        (.val (.ok (.inr ⟨(f₁, vs.take np ++ stk.drop np)⟩, ⟨s₁⟩))) := by
      simp only [loopBodyXP, har]; exact path_bind_pure hp₁ rfl
    exact path_bind_ok h1 hp₂
  | @loopExit s s₁ f f₁ stk bt body np nr cs o har _ hb ih =>
    obtain ⟨hA, hp⟩ := ih
    refine ⟨hA, ?_⟩
    rw [run_denListXP_single, denXP_loop_unfold]
    by_cases ht : o = .flow .trap
    · subst ht
      refine path_bind_err ?_
      simp only [loopBodyXP, har]; exact path_bind_err hp
    · have ht' : blockOutP np nr stk o ≠ .flow .trap := fun h => ht (blockOutP_trap.1 h)
      rw [endRP_ok ht']
      rw [endRP_ok ht] at hp
      have h1 : Path (run' (loopBodyXP bt body ⟨(f, stk)⟩) ⟨s⟩) cs
          (.val (.ok (.inl ⟨(f₁, blockOutP np nr stk o)⟩, ⟨s₁⟩))) := by
        simp only [loopBodyXP, har]
        exact path_bind_pure hp (by rw [loopKP_eq, loopOutP_of_ne hb])
      exact path_bind_pure h1 rfl
  | ifStop _ ho ih =>
    obtain ⟨hA, hp⟩ := ih
    refine ⟨hA, ?_⟩
    rw [run_denListXP_single, denXP_if]
    rename_i o _
    rcases o with fl | _
    · cases fl with
      | normal => exact absurd trivial ho
      | trap => exact path_bind_err hp
      | _ => exact path_bind_pure hp rfl
    · exact path_bind_pure hp rfl
  | @ifArm s s₁ s₂ f f₁ f₂ stk stk₁ cv b bt c t el np nr cs₁ cs₂ o _ hb har _ ih₁ ih₂ =>
    obtain ⟨hA₁, hp₁⟩ := ih₁
    obtain ⟨hA₂, hp₂⟩ := ih₂
    refine ⟨answered_append hA₁ hA₂, ?_⟩
    rw [run_denListXP_single, denXP_if]
    refine path_bind_ok hp₁ ?_
    simp only [hb, har]
    have harm : Path (run' ((if b then denListXP t f₁ (stk₁.take np) else
        denListXP el f₁ (stk₁.take np)) : M (CallSig H) H ResP) ⟨s₁⟩) cs₂
        (endRP (s₂, f₂, o)) := by
      cases b <;> exact hp₂
    rw [blockOutP_eq]
    exact path_blockKP harm
  | @tryT s s₁ f f₁ stk bt cls body np nr cs o o' har _ ht ih =>
    obtain ⟨hA, hp⟩ := ih
    refine ⟨hA, ?_⟩
    rw [run_denListXP_single, denXP_try]
    simp only [har]
    rcases ht with ⟨hnt, rfl⟩ | ⟨a, rfl, ⟨us, l, hc, rfl⟩ | ⟨hc, rfl⟩⟩
    · rw [blockOutP_eq]; exact path_tryKP_ne hp hnt
    · exact path_tryKP_catch hp hc
    · exact path_tryKP_rethrow hp hc

end

end Silmaril.Proofs.Wasm.Abstract.FunctorP
