module

public import Silmaril.Wasm.Abstract.CallX.Defs
public import Silmaril.Wasm.Abstract.CallRes.Thms
public import Silmaril.Proofs.Wasm.Abstract.StoreCall.Expose

/-!
Proofs for `Silmaril.Wasm.Abstract.CallX.Thms`: every `EvalOX C` derivation is
a path of the exposed body `denListX` with every call event answered by `C`
(`evalOX_path`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.CallX

open Silmaril.Wasm Silmaril.Games Silmaril.Games.Abstract Silmaril.Wasm.Abstract
  Silmaril.Wasm.Abstract.Body Silmaril.Wasm.Abstract.BodyTrace Silmaril.Wasm.Binaryen
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract.StoreBody Silmaril.Wasm.Abstract.StoreCall
  Silmaril.Wasm.Abstract.CallX Silmaril.Elgot.ITree Silmaril.Proofs.Wasm.Abstract.StoreBody
  Silmaril.Proofs.Wasm.Abstract.StoreCall

variable {H : Type}

/-! ## Resolution is a function -/

theorem addr_val_inj {ad₁ ad₂ : AddrType} {i₁ : BitVec ad₁.intType.width}
    {i₂ : BitVec ad₂.intType.width} {s₁ s₂ : List Val}
    (h : (Val.num ⟨.int ad₁.intType, i₁⟩ :: s₁) = .num ⟨.int ad₂.intType, i₂⟩ :: s₂) :
    ∃ e : ad₁ = ad₂, e ▸ i₁ = i₂ ∧ s₁ = s₂ := by
  cases ad₁ <;> cases ad₂
  all_goals simp only [AddrType.intType, List.cons.injEq, Val.num.injEq] at h
  all_goals first
    | (obtain ⟨h1, h2⟩ := h; cases h1; exact ⟨rfl, rfl, h2⟩)
    | (obtain ⟨h1, -⟩ := h; cases h1)

theorem indResS_unique {s : Store H} {f : Frame} {x : TableIdx} {y : TypeIdx} {stk : List Val}
    {p₁ p₂ : Option Nat × List Val} (h₁ : IndResS s f x y stk p₁) (h₂ : IndResS s f x y stk p₂) :
    p₁ = p₂ := by
  obtain ⟨ad₁, i₁, e₁, r₁⟩ := h₁
  obtain ⟨ad₂, i₂, e₂, r₂⟩ := h₂
  obtain ⟨rfl, hi, hs⟩ := addr_val_inj (e₁.symm.trans e₂)
  subst hi
  exact Prod.ext (CallRes.indRes_unique r₁ r₂) hs

theorem tailRes_unique {s : Store H} {f : Frame} {i : Instr} {stk : List Val}
    {o₁ o₂ : Option (Nat × List Val)} (h₁ : TailRes s f i stk o₁) (h₂ : TailRes s f i stk o₂) :
    o₁ = o₂ := by
  cases h₁ with
  | direct hfi =>
    cases h₂ with
    | direct hfi' => rw [hfi] at hfi'; cases hfi'; rfl
  | @indirect x y ad i fa stk' hres =>
    generalize hS : (Val.num ⟨.int ad.intType, i⟩ :: stk') = S at h₂
    cases h₂ with
    | indirect hres' =>
      obtain ⟨rfl, hi, rfl⟩ := addr_val_inj hS
      subst hi
      cases CallRes.indRes_unique hres hres'; rfl
    | indirectTrap hres' =>
      obtain ⟨rfl, hi, rfl⟩ := addr_val_inj hS
      subst hi
      cases CallRes.indRes_unique hres hres'
  | @indirectTrap x y ad i stk' hres =>
    generalize hS : (Val.num ⟨.int ad.intType, i⟩ :: stk') = S at h₂
    cases h₂ with
    | indirect hres' =>
      obtain ⟨rfl, hi, rfl⟩ := addr_val_inj hS
      subst hi
      cases CallRes.indRes_unique hres hres'
    | indirectTrap => rfl
  | ref => cases h₂; rfl
  | refNull => cases h₂; rfl

theorem resolveInd_eq {s : Store H} {f : Frame} {x : TableIdx} {y : TypeIdx} {stk : List Val}
    {p : Option Nat × List Val} (h : IndResS s f x y stk p) : resolveInd s f x y stk = some p := by
  have hex : ∃ p, IndResS s f x y stk p := ⟨p, h⟩
  rw [resolveInd, dite_eq_left_of_eq_true (eq_true hex)]
  exact congrArg some (indResS_unique (Classical.choose_spec hex) h)

theorem resolveTail_eq {s : Store H} {f : Frame} {i : Instr} {stk : List Val}
    {o : Option (Nat × List Val)} (h : TailRes s f i stk o) : resolveTail s f i stk = some o := by
  have hex : ∃ o, TailRes s f i stk o := ⟨o, h⟩
  rw [resolveTail, dite_eq_left_of_eq_true (eq_true hex)]
  exact congrArg some (tailRes_unique (Classical.choose_spec hex) h)

/-! ## Call events at an address -/

theorem run_getState_bind {X : Type 1} (k : St H → M (CallSig H) H X) (s : St H) :
    run' (getState >>= k : M (CallSig H) H X) s = run' (k s) s := by
  simp only [getState, run', StateT.run_bind, StateT.run_get, ExceptT.run_bind, ExceptT.run_pure]
  exact pure_bind _ _

theorem run_callAt_vis {fa : Nat} {f : Frame} {stk : List Val} {s : Store H} {fi : FuncInst H}
    {ps rs : List Validation.CValType} (hfi : s.funcs[fa]? = some fi)
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) :
    run' (callAt fa f stk) ⟨s⟩ =
      vis (⟨(fa, (stk.take ps.length).reverse, s), rfl⟩ : SigEv (CallSig H) (Store H × Flow))
        (fun n => run' (callAns f stk ps rs n) ⟨s⟩) := by
  rw [callAt, run_getState_bind]
  simp only [hfi, hty]
  have ht : run' (callImport (E := CallSig H) (S := St H) (T := PUnit.{2})
        (fa, (stk.take ps.length).reverse, s) >>= fun ans => callAns f stk ps rs ans.down) ⟨s⟩ =
      vis (⟨(fa, (stk.take ps.length).reverse, s), rfl⟩ : SigEv (CallSig H) (Store H × Flow))
        (fun n => run' (callAns f stk ps rs n) ⟨s⟩) := by
    rw [StoreBody.run_bind]
    refine (vis_bind _ _ _).trans ?_
    congr 1
    funext n
    exact pure_bind _ _
  exact ht

theorem run_tailAt_vis {fa : Nat} {f : Frame} {stk : List Val} {s : Store H} {fi : FuncInst H}
    {ps rs : List Validation.CValType} (hfi : s.funcs[fa]? = some fi)
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) :
    run' (tailAt fa f stk) ⟨s⟩ =
      vis (⟨(fa, (stk.take ps.length).reverse, s), rfl⟩ : SigEv (CallSig H) (Store H × Flow))
        (fun n => run' (tailAns f rs n) ⟨s⟩) := by
  rw [tailAt, run_getState_bind]
  simp only [hfi, hty]
  have ht : run' (callImport (E := CallSig H) (S := St H) (T := PUnit.{2})
        (fa, (stk.take ps.length).reverse, s) >>= fun ans => tailAns f rs ans.down) ⟨s⟩ =
      vis (⟨(fa, (stk.take ps.length).reverse, s), rfl⟩ : SigEv (CallSig H) (Store H × Flow))
        (fun n => run' (tailAns f rs n) ⟨s⟩) := by
    rw [StoreBody.run_bind]
    refine (vis_bind _ _ _).trans ?_
    congr 1
    funext n
    exact pure_bind _ _
  exact ht

theorem path_callAt {fa : Nat} {f : Frame} {stk : List Val} {s : Store H} {fi : FuncInst H}
    {ps rs : List Validation.CValType} (hfi : s.funcs[fa]? = some fi)
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) (ans : Store H × Flow)
    {cs : List (Call (CallSig H))} {e : PathEnd (Except PUnit.{2} (Res × St H))}
    (h : Path (run' (callAns f stk ps rs ans) ⟨s⟩) cs e) :
    Path (run' (callAt fa f stk) ⟨s⟩) (⟨(fa, (stk.take ps.length).reverse, s), ans⟩ :: cs) e := by
  rw [run_callAt_vis hfi hty]; exact .vis rfl h

theorem path_tailAt {fa : Nat} {f : Frame} {stk : List Val} {s : Store H} {fi : FuncInst H}
    {ps rs : List Validation.CValType} (hfi : s.funcs[fa]? = some fi)
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) (ans : Store H × Flow)
    {cs : List (Call (CallSig H))} {e : PathEnd (Except PUnit.{2} (Res × St H))}
    (h : Path (run' (tailAns f rs ans) ⟨s⟩) cs e) :
    Path (run' (tailAt fa f stk) ⟨s⟩) (⟨(fa, (stk.take ps.length).reverse, s), ans⟩ :: cs) e := by
  rw [run_tailAt_vis hfi hty]; exact .vis rfl h

theorem path_tailAns {f : Frame} {rs : List Validation.CValType} {s₂ : Store H} {fl : Flow}
    (hfl : (∃ vs, fl.retVals = some vs) ∨ fl.Abrupt) (s : St H) :
    Path (run' (tailAns f rs (s₂, fl)) s) [] (endR (s₂, f, tailFlow rs.length fl)) := by
  rcases hfl with ⟨vs, hvs⟩ | hab
  · cases fl with
    | normal ws => simp only [Flow.retVals, Option.some.injEq] at hvs; subst hvs; exact .ret (run_set_pure _ _ _)
    | ret ws => simp only [Flow.retVals, Option.some.injEq] at hvs; subst hvs; exact .ret (run_set_pure _ _ _)
    | brk k ws =>
      cases k with
      | zero => simp only [Flow.retVals, Option.some.injEq] at hvs; subst hvs; exact .ret (run_set_pure _ _ _)
      | succ k => simp [Flow.retVals] at hvs
    | trap => simp [Flow.retVals] at hvs
    | throw t => simp [Flow.retVals] at hvs
  · cases fl with
    | trap => exact .ret (run_trapS s)
    | throw t => exact .ret (run_set_pure _ _ _)
    | _ => exact absurd hab id


/-! ## Equations of the exposed body -/

theorem denListX_cons (e : BExpr) (es : List BExpr) (f : Frame) (stk : List Val) :
    (denListX (H := H) (e :: es) f stk) = denX e f stk >>= thenK (denListX es) := by
  rw [denListX.eq_def]

theorem denX_op (i : Instr) (args : List BExpr) (f : Frame) (stk : List Val) :
    (denX (H := H) (.op i args) f stk) = denListX args f stk >>= thenK (opCX i) := by
  rw [denX.eq_def]

theorem denX_block (bt : BlockType) (body : List BExpr) (f : Frame) (stk : List Val) :
    (denX (H := H) (.block bt body) f stk) =
      match arity f bt with
      | some (np, nr) => denListX body f (stk.take np) >>= blockK np nr stk
      | none => stuck := by
  rw [denX.eq_def]; rfl

theorem denX_loop (bt : BlockType) (body : List BExpr) (f : Frame) (stk : List Val) :
    (denX (H := H) (.loop bt body) f stk) = Silmaril.Elgot.iter (loopBodyX bt body) ⟨(f, stk)⟩ := by
  rw [denX.eq_def]; rfl

theorem denX_if (bt : BlockType) (c t el : List BExpr) (f : Frame) (stk : List Val) :
    (denX (H := H) (.if_ bt c t el) f stk) =
      denListX c f stk >>= fun r =>
        match r with
        | ⟨(f₁, .normal (cv :: stk₁))⟩ =>
          match truthy cv, arity f₁ bt with
          | some b, some (np, nr) =>
            (if b then denListX t f₁ (stk₁.take np) else denListX el f₁ (stk₁.take np)) >>=
              blockK np nr stk₁
          | _, _ => stuck
        | ⟨(_, .normal [])⟩ => stuck
        | r => pure r := by
  rw [denX.eq_def]; rfl

theorem denX_loop_unfold (bt : BlockType) (body : List BExpr) (f : Frame) (stk : List Val) :
    (denX (H := H) (.loop bt body) f stk) =
      (loopBodyX bt body ⟨(f, stk)⟩ >>= Sum.elim pure
        fun c : ULift.{1} (Frame × List Val) => denX (.loop bt body) c.down.1 c.down.2) := by
  rw [denX_loop]
  exact (congrFun (Silmaril.Elgot.LawfulElgotMonad.fixpoint (m := M (CallSig H) H)
    (loopBodyX bt body)) ⟨(f, stk)⟩).trans rfl

theorem notX_of_flat {s : Store H} {f : Frame} {stk : List Val} {i : Instr}
    {r : Store H × Frame × Flow} (h : evalFlat s f stk i = some r) : isXCall i = false := by
  cases i <;> simp_all [isXCall, evalFlat]

theorem opCX_flat {i : Instr} (hi : ∀ x, i ≠ .call x) (hx : isXCall i = false) :
    opCX (H := H) i = flatK i := by
  funext f stk
  unfold opCX
  split <;> simp_all [isXCall]

/-- The tail call forms. -/
def isXTail : Instr → Prop
  | .returnCall _ | .returnCallIndirect _ _ | .returnCallRef _ => True
  | _ => False

theorem isXTail_of_tailRes {s : Store H} {f : Frame} {i : Instr} {stk : List Val}
    {o : Option (Nat × List Val)} (h : TailRes s f i stk o) : isXTail i := by
  cases h <;> trivial

theorem opCX_tail {i : Instr} (h : isXTail i) : opCX (H := H) i = tailEv i := by
  funext f stk
  cases i <;> first | exact absurd h id | rfl

/-- **Every `EvalOX C` derivation is a path of the exposed abstract body**, with
every call event answered as `C` allows, ending as the derivation does. -/
theorem evalOX_path {C : CallRel H} {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    {r : Store H × Frame × Flow} (h : EvalOX C s f stk es r) :
    ∃ cs, Answered C cs ∧ Path (run' (denListX es f stk : M (CallSig H) H Res) ⟨s⟩) cs (endR r) := by
  induction h with
  | nil => exact ⟨[], answered_nil, .ret rfl⟩
  | argsAbort _ hfl ih =>
    obtain ⟨cs, hA, hp⟩ := ih
    refine ⟨cs, hA, ?_⟩
    rw [denListX_cons, denX_op]
    exact path_thenK_pass (path_thenK_pass hp hfl) hfl
  | @callOk s s₁ s₂ f f₁ stk stk₁ vs x args es a fi ps rs fl r _ hfi hty hcall hvs _ ih₁ ih₂ =>
    obtain ⟨cs₁, hA₁, hp₁⟩ := ih₁
    obtain ⟨cs₂, hA₂, hp₂⟩ := ih₂
    refine ⟨cs₁ ++ [⟨(a, (stk₁.take ps.length).reverse, s₁), (s₂, fl)⟩] ++ cs₂,
      answered_append (answered_append hA₁ (answered_single hcall)) hA₂, ?_⟩
    rw [denListX_cons, denX_op]
    exact path_thenK_normal (path_thenK_normal hp₁
      (path_callEv hfi hty (s₂, fl) (path_callAns_vals hvs _))) hp₂
  | @callTrap s s₁ s₂ f f₁ stk stk₁ x args es a fi ps rs _ hfi hty hcall ih₁ =>
    obtain ⟨cs₁, hA₁, hp₁⟩ := ih₁
    refine ⟨cs₁ ++ [⟨(a, (stk₁.take ps.length).reverse, s₁), (s₂, .trap)⟩],
      answered_append hA₁ (answered_single hcall), ?_⟩
    rw [denListX_cons, denX_op]
    have := path_thenK_normal hp₁ (path_callEv hfi hty (s₂, .trap) (path_callAns_trap _))
    exact path_thenK_pass this Flow.notNormal_trap
  | @callThrow s s₁ s₂ f f₁ stk stk₁ x args es a fi ps rs t _ hfi hty hcall ih₁ =>
    obtain ⟨cs₁, hA₁, hp₁⟩ := ih₁
    refine ⟨cs₁ ++ [⟨(a, (stk₁.take ps.length).reverse, s₁), (s₂, .throw t)⟩],
      answered_append hA₁ (answered_single hcall), ?_⟩
    rw [denListX_cons, denX_op]
    have := path_thenK_normal hp₁ (path_callEv hfi hty (s₂, .throw t) (path_callAns_throw _))
    exact path_thenK_pass this Flow.notNormal_throw
  | @opOk s s₁ s₂ f f₁ f₂ stk stk₁ stk₂ i args es r hi _ hflat _ ih₁ ih₂ =>
    obtain ⟨cs₁, hA₁, hp₁⟩ := ih₁
    obtain ⟨cs₂, hA₂, hp₂⟩ := ih₂
    refine ⟨cs₁ ++ [] ++ cs₂, answered_append (answered_append hA₁ answered_nil) hA₂, ?_⟩
    rw [denListX_cons, denX_op]
    have hop : opCX i f₁ stk₁ = (flatK i f₁ stk₁ : M (CallSig H) H Res) :=
      congrFun (congrFun (opCX_flat hi (notX_of_flat hflat)) f₁) stk₁
    exact path_thenK_normal (path_thenK_normal hp₁ (hop ▸ path_flatK hflat)) hp₂
  | @opStop s s₁ s₂ f f₁ f₂ stk stk₁ i args es fl hi _ hflat hfl ih₁ =>
    obtain ⟨cs₁, hA₁, hp₁⟩ := ih₁
    refine ⟨cs₁ ++ [], answered_append hA₁ answered_nil, ?_⟩
    rw [denListX_cons, denX_op]
    have hop : opCX i f₁ stk₁ = (flatK i f₁ stk₁ : M (CallSig H) H Res) :=
      congrFun (congrFun (opCX_flat hi (notX_of_flat hflat)) f₁) stk₁
    exact path_thenK_pass (path_thenK_normal hp₁ (hop ▸ path_flatK hflat)) hfl
  | @blockOk s s₁ f f₁ stk vs bt body es np nr fl r har _ hvs _ ih₁ ih₂ =>
    obtain ⟨cs₁, hA₁, hp₁⟩ := ih₁
    obtain ⟨cs₂, hA₂, hp₂⟩ := ih₂
    refine ⟨cs₁ ++ cs₂, answered_append hA₁ hA₂, ?_⟩
    rw [denListX_cons, denX_block]
    simp only [har]
    have hb := path_blockK (np := np) (nr := nr) (stk := stk) hp₁
    rw [blockFlow_of_vals hvs] at hb
    exact path_thenK_normal hb hp₂
  | @blockBrk s s₁ f f₁ stk vs bt body es np nr k har _ ih =>
    obtain ⟨cs, hA, hp⟩ := ih
    refine ⟨cs, hA, ?_⟩
    rw [denListX_cons, denX_block]
    simp only [har]
    exact path_thenK_pass (path_blockK (np := np) (nr := nr) (stk := stk) hp) Flow.notNormal_brk
  | @blockEsc s s₁ f f₁ stk bt body es np nr fl har _ hfl ih =>
    obtain ⟨cs, hA, hp⟩ := ih
    refine ⟨cs, hA, ?_⟩
    rw [denListX_cons, denX_block]
    simp only [har]
    have hb := path_blockK (np := np) (nr := nr) (stk := stk) hp
    rw [blockFlow_esc hfl] at hb
    exact path_thenK_pass hb (Flow.not_normal_of_escapes hfl)
  | @loopOk s s₁ f f₁ stk vs bt body es np nr r har _ _ ih₁ ih₂ =>
    obtain ⟨cs₁, hA₁, hp₁⟩ := ih₁
    obtain ⟨cs₂, hA₂, hp₂⟩ := ih₂
    refine ⟨cs₁ ++ cs₂, answered_append hA₁ hA₂, ?_⟩
    rw [denListX_cons, denX_loop_unfold]
    have h1 : Path (run' (loopBodyX bt body ⟨(f, stk)⟩) ⟨s⟩) cs₁
        (.val (.ok (.inl ⟨(f₁, .normal (vs.take nr ++ stk.drop np))⟩, ⟨s₁⟩))) := by
      simp only [loopBodyX, har]; exact path_bind_pure hp₁ rfl
    exact path_thenK_normal (path_bind_pure h1 rfl) hp₂
  | @loopBack s s₁ f f₁ stk vs bt body es np nr r har _ _ ih₁ ih₂ =>
    obtain ⟨cs₁, hA₁, hp₁⟩ := ih₁
    obtain ⟨cs₂, hA₂, hp₂⟩ := ih₂
    refine ⟨cs₁ ++ cs₂, answered_append hA₁ hA₂, ?_⟩
    rw [denListX_cons, denX_loop_unfold, bind_assoc]
    have h1 : Path (run' (loopBodyX bt body ⟨(f, stk)⟩) ⟨s⟩) cs₁
        (.val (.ok (.inr ⟨(f₁, vs.take np ++ stk.drop np)⟩, ⟨s₁⟩))) := by
      simp only [loopBodyX, har]; exact path_bind_pure hp₁ rfl
    rw [denListX_cons] at hp₂
    exact path_bind_ok h1 hp₂
  | @loopBrk s s₁ f f₁ stk vs bt body es np nr k har _ ih =>
    obtain ⟨cs, hA, hp⟩ := ih
    refine ⟨cs, hA, ?_⟩
    rw [denListX_cons, denX_loop_unfold]
    have h1 : Path (run' (loopBodyX bt body ⟨(f, stk)⟩) ⟨s⟩) cs
        (.val (.ok (.inl ⟨(f₁, .brk k vs)⟩, ⟨s₁⟩))) := by
      simp only [loopBodyX, har]; exact path_bind_pure hp rfl
    exact path_thenK_pass (path_bind_pure h1 rfl) Flow.notNormal_brk
  | @loopEsc s s₁ f f₁ stk bt body es np nr fl har _ hfl ih =>
    obtain ⟨cs, hA, hp⟩ := ih
    refine ⟨cs, hA, ?_⟩
    rw [denListX_cons, denX_loop_unfold]
    refine path_thenK_pass ?_ (Flow.not_normal_of_escapes hfl)
    cases fl
    case trap =>
      refine path_bind_err ?_
      simp only [loopBodyX, har]; exact path_bind_err hp
    all_goals first
      | exact absurd hfl id
      | (refine path_bind_pure (a := .inl ⟨(f₁, _)⟩) ?_ rfl
         simp only [loopBodyX, har]; exact path_bind_pure hp rfl)
  | @ifOk s s₁ s₂ f f₁ f₂ stk stk₁ vs cv b bt c t el es np nr fl r _ hb har _ hvs _ ih₁ ih₂ ih₃ =>
    obtain ⟨cs₁, hA₁, hp₁⟩ := ih₁
    obtain ⟨cs₂, hA₂, hp₂⟩ := ih₂
    obtain ⟨cs₃, hA₃, hp₃⟩ := ih₃
    refine ⟨cs₁ ++ (cs₂ ++ cs₃), answered_append hA₁ (answered_append hA₂ hA₃), ?_⟩
    rw [denListX_cons, denX_if, bind_assoc]
    refine path_bind_ok hp₁ ?_
    simp only [hb, har]
    have harm : Path (run' ((if b then denListX t f₁ (stk₁.take np) else
        denListX el f₁ (stk₁.take np)) : M (CallSig H) H Res) ⟨s₁⟩) cs₂ (endR (s₂, f₂, fl)) := by
      cases b <;> exact hp₂
    have hbk := path_blockK (np := np) (nr := nr) (stk := stk₁) harm
    rw [blockFlow_of_vals hvs] at hbk
    exact path_thenK_normal hbk hp₃
  | @ifBrk s s₁ s₂ f f₁ f₂ stk stk₁ vs cv b bt c t el es np nr k _ hb har _ ih₁ ih₂ =>
    obtain ⟨cs₁, hA₁, hp₁⟩ := ih₁
    obtain ⟨cs₂, hA₂, hp₂⟩ := ih₂
    refine ⟨cs₁ ++ cs₂, answered_append hA₁ hA₂, ?_⟩
    rw [denListX_cons, denX_if, bind_assoc]
    refine path_bind_ok hp₁ ?_
    simp only [hb, har]
    have harm : Path (run' ((if b then denListX t f₁ (stk₁.take np) else
        denListX el f₁ (stk₁.take np)) : M (CallSig H) H Res) ⟨s₁⟩) cs₂
        (endR (s₂, f₂, .brk (k + 1) vs)) := by
      cases b <;> exact hp₂
    exact path_thenK_pass (path_blockK (np := np) (nr := nr) (stk := stk₁) harm) Flow.notNormal_brk
  | @ifEsc s s₁ s₂ f f₁ f₂ stk stk₁ cv b bt c t el es np nr fl _ hb har _ hfl ih₁ ih₂ =>
    obtain ⟨cs₁, hA₁, hp₁⟩ := ih₁
    obtain ⟨cs₂, hA₂, hp₂⟩ := ih₂
    refine ⟨cs₁ ++ cs₂, answered_append hA₁ hA₂, ?_⟩
    rw [denListX_cons, denX_if, bind_assoc]
    refine path_bind_ok hp₁ ?_
    simp only [hb, har]
    have harm : Path (run' ((if b then denListX t f₁ (stk₁.take np) else
        denListX el f₁ (stk₁.take np)) : M (CallSig H) H Res) ⟨s₁⟩) cs₂ (endR (s₂, f₂, fl)) := by
      cases b <;> exact hp₂
    have hbk := path_blockK (np := np) (nr := nr) (stk := stk₁) harm
    rw [blockFlow_esc hfl] at hbk
    exact path_thenK_pass hbk (Flow.not_normal_of_escapes hfl)
  | @callIndOk s s₁ s₂ f f₁ stk stk₁ vs x y args es ad i fa fi ps rs fl r _ hres hfi hty hcall hvs _ ih₁ ih₂ =>
    obtain ⟨cs₁, hA₁, hp₁⟩ := ih₁
    obtain ⟨cs₂, hA₂, hp₂⟩ := ih₂
    refine ⟨cs₁ ++ [⟨(fa, (stk₁.take ps.length).reverse, s₁), (s₂, fl)⟩] ++ cs₂,
      answered_append (answered_append hA₁ (answered_single hcall)) hA₂, ?_⟩
    rw [denListX_cons, denX_op]
    refine path_thenK_normal (path_thenK_normal hp₁ ?_) hp₂
    show Path (run' (indEv x y f₁ _) ⟨s₁⟩) _ _
    rw [indEv, run_getState_bind]
    simp only [resolveInd_eq (p := (some fa, stk₁)) ⟨ad, i, rfl, hres⟩]
    exact path_callAt hfi hty (s₂, fl) (path_callAns_vals hvs _)
  | @callIndRes s s₁ f f₁ stk stk₁ x y args es ad i _ hres ih =>
    obtain ⟨cs₁, hA₁, hp₁⟩ := ih
    refine ⟨cs₁ ++ [], answered_append hA₁ answered_nil, ?_⟩
    rw [denListX_cons, denX_op]
    refine path_thenK_pass (path_thenK_normal hp₁ ?_) Flow.notNormal_trap
    show Path (run' (indEv x y f₁ _) ⟨s₁⟩) _ _
    rw [indEv, run_getState_bind]
    simp only [resolveInd_eq (p := (none, stk₁)) ⟨ad, i, rfl, hres⟩]
    exact .ret (run_trapS _)
  | @callIndStop s s₁ s₂ f f₁ stk stk₁ x y args es ad i fa fi ps rs fl _ hres hfi hty hcall hfl ih =>
    obtain ⟨cs₁, hA₁, hp₁⟩ := ih
    refine ⟨cs₁ ++ [⟨(fa, (stk₁.take ps.length).reverse, s₁), (s₂, fl)⟩],
      answered_append hA₁ (answered_single hcall), ?_⟩
    rw [denListX_cons, denX_op]
    have hab : ¬ fl.IsNormal := by cases fl <;> simp_all [Flow.Abrupt, Flow.IsNormal]
    refine path_thenK_pass (path_thenK_normal hp₁ ?_) hab
    show Path (run' (indEv x y f₁ _) ⟨s₁⟩) _ _
    rw [indEv, run_getState_bind]
    simp only [resolveInd_eq (p := (some fa, stk₁)) ⟨ad, i, rfl, hres⟩]
    refine path_callAt hfi hty (s₂, fl) ?_
    cases fl with
    | trap => exact path_callAns_trap _
    | throw t => exact path_callAns_throw _
    | _ => exact absurd hfl id
  | @callRefOk s s₁ s₂ f f₁ stk stk₁ vs y args es fa fi ps rs fl r _ hfi hty hcall hvs _ ih₁ ih₂ =>
    obtain ⟨cs₁, hA₁, hp₁⟩ := ih₁
    obtain ⟨cs₂, hA₂, hp₂⟩ := ih₂
    refine ⟨cs₁ ++ [⟨(fa, (stk₁.take ps.length).reverse, s₁), (s₂, fl)⟩] ++ cs₂,
      answered_append (answered_append hA₁ (answered_single hcall)) hA₂, ?_⟩
    rw [denListX_cons, denX_op]
    exact path_thenK_normal (path_thenK_normal hp₁
      (path_callAt hfi hty (s₂, fl) (path_callAns_vals hvs _))) hp₂
  | @callRefNull s s₁ f f₁ stk stk₁ y args es _ ih =>
    obtain ⟨cs₁, hA₁, hp₁⟩ := ih
    refine ⟨cs₁ ++ [], answered_append hA₁ answered_nil, ?_⟩
    rw [denListX_cons, denX_op]
    exact path_thenK_pass (path_thenK_normal hp₁ (.ret (run_trapS _))) Flow.notNormal_trap
  | @callRefStop s s₁ s₂ f f₁ stk stk₁ y args es fa fi ps rs fl _ hfi hty hcall hfl ih =>
    obtain ⟨cs₁, hA₁, hp₁⟩ := ih
    refine ⟨cs₁ ++ [⟨(fa, (stk₁.take ps.length).reverse, s₁), (s₂, fl)⟩],
      answered_append hA₁ (answered_single hcall), ?_⟩
    rw [denListX_cons, denX_op]
    have hab : ¬ fl.IsNormal := by cases fl <;> simp_all [Flow.Abrupt, Flow.IsNormal]
    refine path_thenK_pass (path_thenK_normal hp₁ (path_callAt hfi hty (s₂, fl) ?_)) hab
    cases fl with
    | trap => exact path_callAns_trap _
    | throw t => exact path_callAns_throw _
    | _ => exact absurd hfl id
  | @tail s s₁ s₂ f f₁ stk stk₁ i args es fa fi ps rs fl _ hres hfi hty hcall hfl ih =>
    obtain ⟨cs₁, hA₁, hp₁⟩ := ih
    refine ⟨cs₁ ++ [⟨(fa, ((stk₁.drop (tailPop i)).take ps.length).reverse, s₁), (s₂, fl)⟩],
      answered_append hA₁ (answered_single hcall), ?_⟩
    rw [denListX_cons, denX_op]
    have hab : ¬ (tailFlow rs.length fl).IsNormal := by
      rcases hfl with ⟨vs, hvs⟩ | hfl
      · cases fl with
        | brk k vs' => cases k <;> simp_all [tailFlow, Flow.IsNormal, Flow.retVals]
        | _ => simp_all [tailFlow, Flow.IsNormal, Flow.retVals]
      · cases fl <;> simp_all [Flow.Abrupt, tailFlow, Flow.IsNormal]
    refine path_thenK_pass (path_thenK_normal hp₁ ?_) hab
    rw [opCX_tail (isXTail_of_tailRes hres)]
    show Path (run' (tailEv i f₁ _) ⟨s₁⟩) _ _
    rw [tailEv, run_getState_bind]
    simp only [resolveTail_eq hres]
    exact path_tailAt hfi hty (s₂, fl) (path_tailAns hfl _)
  | @tailRes s s₁ f f₁ stk stk₁ i args es _ hres ih =>
    obtain ⟨cs₁, hA₁, hp₁⟩ := ih
    refine ⟨cs₁ ++ [], answered_append hA₁ answered_nil, ?_⟩
    rw [denListX_cons, denX_op]
    refine path_thenK_pass (path_thenK_normal hp₁ ?_) Flow.notNormal_trap
    rw [opCX_tail (isXTail_of_tailRes hres)]
    show Path (run' (tailEv i f₁ _) ⟨s₁⟩) _ _
    rw [tailEv, run_getState_bind]
    simp only [resolveTail_eq hres]
    exact .ret (run_trapS _)
  | @ifAbort s s₁ f f₁ stk bt c t el es fl _ hfl ih =>
    obtain ⟨cs, hA, hp⟩ := ih
    refine ⟨cs, hA, ?_⟩
    rw [denListX_cons, denX_if]
    refine path_thenK_pass ?_ hfl
    cases fl
    case normal => exact absurd trivial hfl
    case trap => exact path_bind_err hp
    all_goals exact path_bind_pure hp rfl

/-! ## The direct part of the exposed body is `StoreCall`'s -/

theorem opCX_eq_opC {i : Instr} (hx : isXCall i = false) : opCX (H := H) i = opC callEv i := by
  funext f stk
  unfold opCX opC
  split <;> simp_all [isXCall, callIdx?]

mutual

theorem denX_eq_denC : ∀ (e : BExpr), xFree e = true →
    (denX (H := H) e : Frame → List Val → M (CallSig H) H Res) = denC callEv e
  | .op i args, h => by
    simp only [xFree, Bool.and_eq_true, Bool.not_eq_true'] at h
    funext f stk
    rw [denX_op, denC_op, denListX_eq_denC args h.2, opCX_eq_opC h.1]
  | .block bt body, h => by
    simp only [xFree] at h
    funext f stk
    rw [denX_block, denC_block, denListX_eq_denC body h]
    cases arity f bt <;> rfl
  | .loop bt body, h => by
    simp only [xFree] at h
    funext f stk
    rw [denX_loop, denC_loop]
    congr 1
    funext c
    simp only [loopBodyX, loopBodyC, denListX_eq_denC body h]
    cases arity c.down.1 bt <;> rfl
  | .if_ bt c t el, h => by
    simp only [xFree, Bool.and_eq_true] at h
    funext f stk
    rw [denX_if, denC_if, denListX_eq_denC c h.1.1, denListX_eq_denC t h.1.2,
      denListX_eq_denC el h.2]
    congr 1
  | .tryTable bt cs body, _ => by
    funext f stk
    rw [denX.eq_def, denC.eq_def]

theorem denListX_eq_denC : ∀ (es : List BExpr), xFreeL es = true →
    (denListX (H := H) es : Frame → List Val → M (CallSig H) H Res) = denListC callEv es
  | [], _ => by funext f stk; rw [denListX.eq_def, denListC.eq_def]
  | e :: es, h => by
    simp only [xFreeL, Bool.and_eq_true] at h
    funext f stk
    rw [denListX_cons, denListC_cons, denX_eq_denC e h.1, denListX_eq_denC es h.2]

end

end Silmaril.Proofs.Wasm.Abstract.CallX
