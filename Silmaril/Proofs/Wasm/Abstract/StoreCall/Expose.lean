module

public import Silmaril.Wasm.Abstract.StoreCall.Defs
public import Silmaril.Proofs.Wasm.Abstract.StoreBody.Basic
public import Silmaril.Proofs.Wasm.Abstract.BodyTrace.Bind
public import Silmaril.Wasm.Abstract.BodyTrace.Thms

/-!
Proofs for `Silmaril.Wasm.Abstract.StoreCall.Thms`: every derivation of
`EvalO C` is a path of the exposed abstract body whose call events are answered
by `C` (`evalO_path`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.StoreCall

open Silmaril.Wasm Silmaril.Games Silmaril.Games.Abstract Silmaril.Wasm.Abstract
  Silmaril.Wasm.Abstract.Body Silmaril.Wasm.Abstract.BodyTrace Silmaril.Wasm.Binaryen
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract.StoreBody Silmaril.Wasm.Abstract.StoreCall
  Silmaril.Elgot.ITree Silmaril.Proofs.Wasm.Abstract.StoreBody Silmaril.Proofs.Wasm.Abstract.BodyTrace

variable {E : Sig.{0}} {H : Type}

theorem path_bind_ok {X Y : Type 1} {x : M E H X} {k : X → M E H Y} {s : St H}
    {cs₁ cs₂ : List (Call E)} {a : X} {s₁ : St H}
    {e : PathEnd (Except PUnit.{2} (Y × St H))}
    (h₁ : Path (run' x s) cs₁ (.val (.ok (a, s₁)))) (h₂ : Path (run' (k a) s₁) cs₂ e) :
    Path (run' (x >>= k) s) (cs₁ ++ cs₂) e := by
  rw [StoreBody.run_bind]; exact path_bind_ret h₁ h₂

theorem path_bind_err {X Y : Type 1} {x : M E H X} {k : X → M E H Y} {s : St H}
    {cs : List (Call E)} (h : Path (run' x s) cs (.val (.error ⟨⟩))) :
    Path (run' (x >>= k) s) cs (.val (.error ⟨⟩)) := by
  rw [StoreBody.run_bind]
  have := path_bind_ret (k := fun r => match r with
    | .ok (a, s') => run' (k a) s'
    | .error e => pure (.error e)) h (.ret rfl)
  rwa [List.append_nil] at this

theorem path_bind_pure {X Y : Type 1} {x : M E H X} {k : X → M E H Y} {s : St H}
    {cs : List (Call E)} {a : X} {b : Y} {s₁ : St H} (h : Path (run' x s) cs (.val (.ok (a, s₁))))
    (hk : k a = pure b) : Path (run' (x >>= k) s) cs (.val (.ok (b, s₁))) := by
  have := path_bind_ok (k := k) h (cs₂ := []) (by rw [hk]; exact .ret rfl)
  rwa [List.append_nil] at this

theorem path_thenK_normal {k : Frame → List Val → M E H Res} {x : M E H Res} {s : St H}
    {cs₁ cs₂ : List (Call E)} {s₁ : Store H} {f₁ : Frame} {stk₁ : List Val}
    {e : PathEnd (Except PUnit.{2} (Res × St H))}
    (h₁ : Path (run' x s) cs₁ (endR (s₁, f₁, .normal stk₁)))
    (h₂ : Path (run' (k f₁ stk₁) ⟨s₁⟩) cs₂ e) :
    Path (run' (x >>= thenK k) s) (cs₁ ++ cs₂) e :=
  path_bind_ok h₁ h₂

theorem path_thenK_pass {k : Frame → List Val → M E H Res} {x : M E H Res} {s : St H}
    {cs : List (Call E)} {s₁ : Store H} {f₁ : Frame} {fl : Flow}
    (h : Path (run' x s) cs (endR (s₁, f₁, fl))) (hfl : ¬ fl.IsNormal) :
    Path (run' (x >>= thenK k) s) cs (endR (s₁, f₁, fl)) := by
  cases fl
  case normal => exact absurd trivial hfl
  case trap => exact path_bind_err h
  all_goals exact path_bind_pure h rfl

/-- The flow after a block's exits. -/
def blockFlow (np nr : Nat) (stk : List Val) : Flow → Flow
  | .normal vs | .brk 0 vs => .normal (vs.take nr ++ stk.drop np)
  | .brk (k + 1) vs => .brk k vs
  | fl => fl

theorem path_blockK {np nr : Nat} {stk : List Val} {x : M E H Res} {s : St H}
    {cs : List (Call E)} {s₁ : Store H} {f₁ : Frame} {fl : Flow}
    (h : Path (run' x s) cs (endR (s₁, f₁, fl))) :
    Path (run' (x >>= blockK np nr stk) s) cs (endR (s₁, f₁, blockFlow np nr stk fl)) := by
  cases fl with
  | trap => exact path_bind_err h
  | brk k vs => cases k <;> exact path_bind_pure h rfl
  | _ => exact path_bind_pure h rfl

theorem path_ret_endR (r : Store H × Frame × Flow) :
    Path (evalTree (E := E) (some r)) [] (endR r) := by
  obtain ⟨s', f', fl⟩ := r
  cases fl <;> exact .ret rfl

theorem run_set_pure {X : Type 1} (r : X) (s₂ : Store H) (s : St H) :
    run' (setState ⟨s₂⟩ >>= fun _ => pure r : M E H X) s = ret (.ok (r, ⟨s₂⟩)) := by
  simp only [setState, run', StateT.run_bind, StateT.run_set, ExceptT.run_bind]
  exact pure_bind _ _

theorem callIdx_none {i : Instr} (hi : ∀ x, i ≠ .call x) : callIdx? i = none := by
  unfold callIdx?
  split
  · rename_i x; exact absurd rfl (hi x)
  · rfl

/-! ## Calls -/

theorem run_callEv {x : FuncIdx} {f : Frame} {stk : List Val} {s : Store H} {a : Nat}
    {fi : FuncInst H} {ps rs : List Validation.CValType} (hfi : s.func? f x = some (a, fi))
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) :
    run' (callEv x f stk : M (CallSig H) H Res) ⟨s⟩ =
      run' (callImport (E := CallSig H) (S := St H) (T := PUnit.{2})
        (a, (stk.take ps.length).reverse, s) >>= fun ans => callAns f stk ps rs ans.down) ⟨s⟩ := by
  simp only [callEv, getState, run', StateT.run_bind, StateT.run_get, ExceptT.run_bind,
    ExceptT.run_pure]
  refine (pure_bind _ _).trans ?_
  simp only [hfi, hty]
  rfl

theorem run_callEv_vis {x : FuncIdx} {f : Frame} {stk : List Val} {s : Store H} {a : Nat}
    {fi : FuncInst H} {ps rs : List Validation.CValType} (hfi : s.func? f x = some (a, fi))
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) :
    run' (callEv x f stk : M (CallSig H) H Res) ⟨s⟩ =
      vis (⟨(a, (stk.take ps.length).reverse, s), rfl⟩ : SigEv (CallSig H) (Store H × Flow))
        (fun n => run' (callAns f stk ps rs n) ⟨s⟩) := by
  rw [run_callEv hfi hty]
  have ht : run' (callImport (E := CallSig H) (S := St H) (T := PUnit.{2})
        (a, (stk.take ps.length).reverse, s) >>= fun ans => callAns f stk ps rs ans.down) ⟨s⟩ =
      vis (⟨(a, (stk.take ps.length).reverse, s), rfl⟩ : SigEv (CallSig H) (Store H × Flow))
        (fun n => run' (callAns f stk ps rs n) ⟨s⟩) := by
    rw [StoreBody.run_bind]
    refine (vis_bind _ _ _).trans ?_
    congr 1
    funext n
    exact pure_bind _ _
  exact ht

/-- A call event answered by `ans`, then the answer's continuation. -/
theorem path_callEv {x : FuncIdx} {f : Frame} {stk : List Val} {s : Store H} {a : Nat}
    {fi : FuncInst H} {ps rs : List Validation.CValType} (hfi : s.func? f x = some (a, fi))
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) (ans : Store H × Flow)
    {cs : List (Call (CallSig H))} {e : PathEnd (Except PUnit.{2} (Res × St H))}
    (h : Path (run' (callAns f stk ps rs ans) ⟨s⟩) cs e) :
    Path (run' (callEv x f stk : M (CallSig H) H Res) ⟨s⟩)
      (⟨(a, (stk.take ps.length).reverse, s), ans⟩ :: cs) e := by
  rw [run_callEv_vis hfi hty]
  exact .vis rfl h

theorem path_callAns_vals {f : Frame} {stk : List Val} {ps rs : List Validation.CValType}
    {s₂ : Store H} {fl : Flow} {vs : List Val} (hvs : fl.retVals = some vs) (s : St H) :
    Path (run' (callAns f stk ps rs (s₂, fl)) s) []
      (endR (s₂, f, .normal (vs.take rs.length ++ stk.drop ps.length))) := by
  cases fl with
  | normal ws => simp only [Flow.retVals, Option.some.injEq] at hvs; subst hvs; exact .ret (run_set_pure _ _ _)
  | ret ws => simp only [Flow.retVals, Option.some.injEq] at hvs; subst hvs; exact .ret (run_set_pure _ _ _)
  | brk k ws =>
    cases k with
    | zero => simp only [Flow.retVals, Option.some.injEq] at hvs; subst hvs; exact .ret (run_set_pure _ _ _)
    | succ k => simp [Flow.retVals] at hvs
  | trap => simp [Flow.retVals] at hvs
  | throw t => simp [Flow.retVals] at hvs

theorem run_trapS {X : Type 1} (s : St H) : run' (trap ⟨⟩ : M E H X) s = ret (.error ⟨⟩) := by
  simp [trap, throw, throwThe, MonadExceptOf.throw, StateT.lift, ExceptT.run,
    ExceptT.mk, Functor.map, ExceptT.map, StateT.run]
  rfl

theorem path_callAns_trap {f : Frame} {stk : List Val} {ps rs : List Validation.CValType}
    {s₂ : Store H} (s : St H) :
    Path (run' (callAns f stk ps rs (s₂, .trap)) s) [] (endR (s₂, f, .trap)) :=
  .ret (run_trapS s)

theorem path_callAns_throw {f : Frame} {stk : List Val} {ps rs : List Validation.CValType}
    {s₂ : Store H} {t : Nat} (s : St H) :
    Path (run' (callAns f stk ps rs (s₂, .throw t)) s) [] (endR (s₂, f, .throw t)) :=
  .ret (run_set_pure _ _ _)

/-! ## Blocks and loops -/

theorem blockFlow_of_vals {np nr : Nat} {stk : List Val} {fl : Flow} {vs : List Val}
    (h : fl.blockVals = some vs) : blockFlow np nr stk fl = .normal (vs.take nr ++ stk.drop np) := by
  cases fl with
  | normal ws => simp only [Flow.blockVals, Option.some.injEq] at h; subst h; rfl
  | brk k ws =>
    cases k with
    | zero => simp only [Flow.blockVals, Option.some.injEq] at h; subst h; rfl
    | succ k => simp [Flow.blockVals] at h
  | _ => simp [Flow.blockVals] at h

theorem blockFlow_esc {np nr : Nat} {stk : List Val} {fl : Flow} (h : fl.Escapes) :
    blockFlow np nr stk fl = fl := by
  cases fl <;> first | rfl | exact absurd h id


theorem denListC_cons {E : Sig.{0}} (cK : FuncIdx → Frame → List Val → M E H Res) (e : BExpr)
    (es : List BExpr) (f : Frame) (stk : List Val) :
    denListC cK (e :: es) f stk = denC cK e f stk >>= thenK (denListC cK es) := by
  rw [denListC.eq_def]

theorem denC_op {E : Sig.{0}} (cK : FuncIdx → Frame → List Val → M E H Res) (i : Instr)
    (args : List BExpr) (f : Frame) (stk : List Val) :
    denC cK (.op i args) f stk = denListC cK args f stk >>= thenK (opC cK i) := by
  rw [denC.eq_def]

theorem denC_block {E : Sig.{0}} (cK : FuncIdx → Frame → List Val → M E H Res) (bt : BlockType)
    (body : List BExpr) (f : Frame) (stk : List Val) :
    denC cK (.block bt body) f stk =
      match arity f bt with
      | some (np, nr) => denListC cK body f (stk.take np) >>= blockK np nr stk
      | none => stuck := by
  rw [denC.eq_def]; rfl

theorem denC_loop {E : Sig.{0}} (cK : FuncIdx → Frame → List Val → M E H Res) (bt : BlockType)
    (body : List BExpr) (f : Frame) (stk : List Val) :
    denC cK (.loop bt body) f stk = Silmaril.Elgot.iter (loopBodyC cK bt body) ⟨(f, stk)⟩ := by
  rw [denC.eq_def]; rfl

theorem denC_if {E : Sig.{0}} (cK : FuncIdx → Frame → List Val → M E H Res) (bt : BlockType)
    (c t el : List BExpr) (f : Frame) (stk : List Val) :
    denC cK (.if_ bt c t el) f stk =
      denListC cK c f stk >>= fun r =>
        match r with
        | ⟨(f₁, .normal (cv :: stk₁))⟩ =>
          match truthy cv, arity f₁ bt with
          | some b, some (np, nr) =>
            (if b then denListC cK t f₁ (stk₁.take np) else denListC cK el f₁ (stk₁.take np)) >>=
              blockK np nr stk₁
          | _, _ => stuck
        | ⟨(_, .normal [])⟩ => stuck
        | r => pure r := by
  rw [denC.eq_def]; rfl

theorem denC_loop_unfold {E : Sig.{0}} (cK : FuncIdx → Frame → List Val → M E H Res)
    (bt : BlockType) (body : List BExpr) (f : Frame) (stk : List Val) :
    (denC cK (.loop bt body) f stk : M E H Res) =
      (loopBodyC cK bt body ⟨(f, stk)⟩ >>= Sum.elim pure
        fun c : ULift.{1} (Frame × List Val) => denC cK (.loop bt body) c.down.1 c.down.2) := by
  rw [denC_loop]
  exact (congrFun (Silmaril.Elgot.LawfulElgotMonad.fixpoint (m := M E H) (loopBodyC cK bt body))
    ⟨(f, stk)⟩).trans rfl

theorem answered_append {C : CallRel H} {a b : List (Call (CallSig H))} (ha : Answered C a)
    (hb : Answered C b) : Answered C (a ++ b) := by
  intro c hc
  rcases List.mem_append.1 hc with h | h
  exacts [ha c h, hb c h]

theorem answered_nil {C : CallRel H} : Answered C [] := fun _ h => by cases h

theorem answered_single {C : CallRel H} {c : Call (CallSig H)}
    (h : C c.1.2.2 c.1.1 c.1.2.1 c.2) : Answered C [c] := by
  intro c' hc; simp only [List.mem_singleton] at hc; subst hc; exact h

theorem path_flatK {i : Instr} {f : Frame} {stk : List Val} {s : Store H}
    {r : Store H × Frame × Flow} (h : evalFlat s f stk i = some r) :
    Path (run' (flatK i f stk : M E H Res) ⟨s⟩) [] (endR r) := by
  have : run' (flatK i f stk : M E H Res) ⟨s⟩ = evalTree (some r) :=
    (run_flatK i f stk s).trans (by rw [h])
  rw [this]; exact path_ret_endR r

/-! ## Exposure: derivations are answered paths -/

/-- **Every `EvalO C` derivation is a path of the exposed abstract body**, with
every call event answered as `C` allows, ending as the derivation does. -/
theorem evalO_path {C : CallRel H} {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    {r : Store H × Frame × Flow} (h : EvalO C s f stk es r) :
    ∃ cs, Answered C cs ∧ Path (run' (denListC callEv es f stk : M (CallSig H) H Res) ⟨s⟩) cs (endR r) := by
  induction h with
  | nil => exact ⟨[], answered_nil, .ret rfl⟩
  | argsAbort _ hfl ih =>
    obtain ⟨cs, hA, hp⟩ := ih
    refine ⟨cs, hA, ?_⟩
    rw [denListC_cons, denC_op]
    exact path_thenK_pass (path_thenK_pass hp hfl) hfl
  | @callOk s s₁ s₂ f f₁ stk stk₁ vs x args es a fi ps rs fl r _ hfi hty hcall hvs _ ih₁ ih₂ =>
    obtain ⟨cs₁, hA₁, hp₁⟩ := ih₁
    obtain ⟨cs₂, hA₂, hp₂⟩ := ih₂
    refine ⟨cs₁ ++ [⟨(a, (stk₁.take ps.length).reverse, s₁), (s₂, fl)⟩] ++ cs₂,
      answered_append (answered_append hA₁ (answered_single hcall)) hA₂, ?_⟩
    rw [denListC_cons, denC_op]
    exact path_thenK_normal (path_thenK_normal hp₁
      (path_callEv hfi hty (s₂, fl) (path_callAns_vals hvs _))) hp₂
  | @callTrap s s₁ s₂ f f₁ stk stk₁ x args es a fi ps rs _ hfi hty hcall ih₁ =>
    obtain ⟨cs₁, hA₁, hp₁⟩ := ih₁
    refine ⟨cs₁ ++ [⟨(a, (stk₁.take ps.length).reverse, s₁), (s₂, .trap)⟩],
      answered_append hA₁ (answered_single hcall), ?_⟩
    rw [denListC_cons, denC_op]
    have := path_thenK_normal hp₁ (path_callEv hfi hty (s₂, .trap) (path_callAns_trap _))
    exact path_thenK_pass this Flow.notNormal_trap
  | @callThrow s s₁ s₂ f f₁ stk stk₁ x args es a fi ps rs t _ hfi hty hcall ih₁ =>
    obtain ⟨cs₁, hA₁, hp₁⟩ := ih₁
    refine ⟨cs₁ ++ [⟨(a, (stk₁.take ps.length).reverse, s₁), (s₂, .throw t)⟩],
      answered_append hA₁ (answered_single hcall), ?_⟩
    rw [denListC_cons, denC_op]
    have := path_thenK_normal hp₁ (path_callEv hfi hty (s₂, .throw t) (path_callAns_throw _))
    exact path_thenK_pass this Flow.notNormal_throw
  | @opOk s s₁ s₂ f f₁ f₂ stk stk₁ stk₂ i args es r hi _ hflat _ ih₁ ih₂ =>
    obtain ⟨cs₁, hA₁, hp₁⟩ := ih₁
    obtain ⟨cs₂, hA₂, hp₂⟩ := ih₂
    refine ⟨cs₁ ++ [] ++ cs₂, answered_append (answered_append hA₁ answered_nil) hA₂, ?_⟩
    rw [denListC_cons, denC_op]
    have hop : opC callEv i f₁ stk₁ = (flatK i f₁ stk₁ : M (CallSig H) H Res) := by
      simp only [opC, callIdx_none hi]
    exact path_thenK_normal (path_thenK_normal hp₁ (hop ▸ path_flatK hflat)) hp₂
  | @opStop s s₁ s₂ f f₁ f₂ stk stk₁ i args es fl hi _ hflat hfl ih₁ =>
    obtain ⟨cs₁, hA₁, hp₁⟩ := ih₁
    refine ⟨cs₁ ++ [], answered_append hA₁ answered_nil, ?_⟩
    rw [denListC_cons, denC_op]
    have hop : opC callEv i f₁ stk₁ = (flatK i f₁ stk₁ : M (CallSig H) H Res) := by
      simp only [opC, callIdx_none hi]
    exact path_thenK_pass (path_thenK_normal hp₁ (hop ▸ path_flatK hflat)) hfl
  | @blockOk s s₁ f f₁ stk vs bt body es np nr fl r har _ hvs _ ih₁ ih₂ =>
    obtain ⟨cs₁, hA₁, hp₁⟩ := ih₁
    obtain ⟨cs₂, hA₂, hp₂⟩ := ih₂
    refine ⟨cs₁ ++ cs₂, answered_append hA₁ hA₂, ?_⟩
    rw [denListC_cons, denC_block]
    simp only [har]
    have hb := path_blockK (np := np) (nr := nr) (stk := stk) hp₁
    rw [blockFlow_of_vals hvs] at hb
    exact path_thenK_normal hb hp₂
  | @blockBrk s s₁ f f₁ stk vs bt body es np nr k har _ ih =>
    obtain ⟨cs, hA, hp⟩ := ih
    refine ⟨cs, hA, ?_⟩
    rw [denListC_cons, denC_block]
    simp only [har]
    exact path_thenK_pass (path_blockK (np := np) (nr := nr) (stk := stk) hp) Flow.notNormal_brk
  | @blockEsc s s₁ f f₁ stk bt body es np nr fl har _ hfl ih =>
    obtain ⟨cs, hA, hp⟩ := ih
    refine ⟨cs, hA, ?_⟩
    rw [denListC_cons, denC_block]
    simp only [har]
    have hb := path_blockK (np := np) (nr := nr) (stk := stk) hp
    rw [blockFlow_esc hfl] at hb
    exact path_thenK_pass hb (Flow.not_normal_of_escapes hfl)
  | @loopOk s s₁ f f₁ stk vs bt body es np nr r har _ _ ih₁ ih₂ =>
    obtain ⟨cs₁, hA₁, hp₁⟩ := ih₁
    obtain ⟨cs₂, hA₂, hp₂⟩ := ih₂
    refine ⟨cs₁ ++ cs₂, answered_append hA₁ hA₂, ?_⟩
    rw [denListC_cons, denC_loop_unfold]
    have h1 : Path (run' (loopBodyC callEv bt body ⟨(f, stk)⟩) ⟨s⟩) cs₁
        (.val (.ok (.inl ⟨(f₁, .normal (vs.take nr ++ stk.drop np))⟩, ⟨s₁⟩))) := by
      simp only [loopBodyC, har]; exact path_bind_pure hp₁ rfl
    exact path_thenK_normal (path_bind_pure h1 rfl) hp₂
  | @loopBack s s₁ f f₁ stk vs bt body es np nr r har _ _ ih₁ ih₂ =>
    obtain ⟨cs₁, hA₁, hp₁⟩ := ih₁
    obtain ⟨cs₂, hA₂, hp₂⟩ := ih₂
    refine ⟨cs₁ ++ cs₂, answered_append hA₁ hA₂, ?_⟩
    rw [denListC_cons, denC_loop_unfold, bind_assoc]
    have h1 : Path (run' (loopBodyC callEv bt body ⟨(f, stk)⟩) ⟨s⟩) cs₁
        (.val (.ok (.inr ⟨(f₁, vs.take np ++ stk.drop np)⟩, ⟨s₁⟩))) := by
      simp only [loopBodyC, har]; exact path_bind_pure hp₁ rfl
    rw [denListC_cons] at hp₂
    exact path_bind_ok h1 hp₂
  | @loopBrk s s₁ f f₁ stk vs bt body es np nr k har _ ih =>
    obtain ⟨cs, hA, hp⟩ := ih
    refine ⟨cs, hA, ?_⟩
    rw [denListC_cons, denC_loop_unfold]
    have h1 : Path (run' (loopBodyC callEv bt body ⟨(f, stk)⟩) ⟨s⟩) cs
        (.val (.ok (.inl ⟨(f₁, .brk k vs)⟩, ⟨s₁⟩))) := by
      simp only [loopBodyC, har]; exact path_bind_pure hp rfl
    exact path_thenK_pass (path_bind_pure h1 rfl) Flow.notNormal_brk
  | @loopEsc s s₁ f f₁ stk bt body es np nr fl har _ hfl ih =>
    obtain ⟨cs, hA, hp⟩ := ih
    refine ⟨cs, hA, ?_⟩
    rw [denListC_cons, denC_loop_unfold]
    refine path_thenK_pass ?_ (Flow.not_normal_of_escapes hfl)
    cases fl
    case trap =>
      refine path_bind_err ?_
      simp only [loopBodyC, har]; exact path_bind_err hp
    all_goals first
      | exact absurd hfl id
      | (refine path_bind_pure (a := .inl ⟨(f₁, _)⟩) ?_ rfl
         simp only [loopBodyC, har]; exact path_bind_pure hp rfl)
  | @ifOk s s₁ s₂ f f₁ f₂ stk stk₁ vs cv b bt c t el es np nr fl r _ hb har _ hvs _ ih₁ ih₂ ih₃ =>
    obtain ⟨cs₁, hA₁, hp₁⟩ := ih₁
    obtain ⟨cs₂, hA₂, hp₂⟩ := ih₂
    obtain ⟨cs₃, hA₃, hp₃⟩ := ih₃
    refine ⟨cs₁ ++ (cs₂ ++ cs₃), answered_append hA₁ (answered_append hA₂ hA₃), ?_⟩
    rw [denListC_cons, denC_if, bind_assoc]
    refine path_bind_ok hp₁ ?_
    simp only [hb, har]
    have harm : Path (run' ((if b then denListC callEv t f₁ (stk₁.take np) else
        denListC callEv el f₁ (stk₁.take np)) : M (CallSig H) H Res) ⟨s₁⟩) cs₂ (endR (s₂, f₂, fl)) := by
      cases b <;> exact hp₂
    have hbk := path_blockK (np := np) (nr := nr) (stk := stk₁) harm
    rw [blockFlow_of_vals hvs] at hbk
    exact path_thenK_normal hbk hp₃
  | @ifBrk s s₁ s₂ f f₁ f₂ stk stk₁ vs cv b bt c t el es np nr k _ hb har _ ih₁ ih₂ =>
    obtain ⟨cs₁, hA₁, hp₁⟩ := ih₁
    obtain ⟨cs₂, hA₂, hp₂⟩ := ih₂
    refine ⟨cs₁ ++ cs₂, answered_append hA₁ hA₂, ?_⟩
    rw [denListC_cons, denC_if, bind_assoc]
    refine path_bind_ok hp₁ ?_
    simp only [hb, har]
    have harm : Path (run' ((if b then denListC callEv t f₁ (stk₁.take np) else
        denListC callEv el f₁ (stk₁.take np)) : M (CallSig H) H Res) ⟨s₁⟩) cs₂
        (endR (s₂, f₂, .brk (k + 1) vs)) := by
      cases b <;> exact hp₂
    exact path_thenK_pass (path_blockK (np := np) (nr := nr) (stk := stk₁) harm) Flow.notNormal_brk
  | @ifEsc s s₁ s₂ f f₁ f₂ stk stk₁ cv b bt c t el es np nr fl _ hb har _ hfl ih₁ ih₂ =>
    obtain ⟨cs₁, hA₁, hp₁⟩ := ih₁
    obtain ⟨cs₂, hA₂, hp₂⟩ := ih₂
    refine ⟨cs₁ ++ cs₂, answered_append hA₁ hA₂, ?_⟩
    rw [denListC_cons, denC_if, bind_assoc]
    refine path_bind_ok hp₁ ?_
    simp only [hb, har]
    have harm : Path (run' ((if b then denListC callEv t f₁ (stk₁.take np) else
        denListC callEv el f₁ (stk₁.take np)) : M (CallSig H) H Res) ⟨s₁⟩) cs₂ (endR (s₂, f₂, fl)) := by
      cases b <;> exact hp₂
    have hbk := path_blockK (np := np) (nr := nr) (stk := stk₁) harm
    rw [blockFlow_esc hfl] at hbk
    exact path_thenK_pass hbk (Flow.not_normal_of_escapes hfl)
  | @ifAbort s s₁ f f₁ stk bt c t el es fl _ hfl ih =>
    obtain ⟨cs, hA, hp⟩ := ih
    refine ⟨cs, hA, ?_⟩
    rw [denListC_cons, denC_if]
    refine path_thenK_pass ?_ hfl
    cases fl
    case normal => exact absurd trivial hfl
    case trap => exact path_bind_err hp
    all_goals exact path_bind_pure hp rfl

end Silmaril.Proofs.Wasm.Abstract.StoreCall
