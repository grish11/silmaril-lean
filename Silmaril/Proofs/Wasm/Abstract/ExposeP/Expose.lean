module

public import Silmaril.Wasm.Abstract.ExposeP.Defs
public import Silmaril.Proofs.Wasm.Abstract.ExposeE.Expose

/-!
Proofs for `Silmaril.Wasm.Abstract.ExposeP.Thms`: every `EvalOXP C` derivation is a path of the
exposed body `denListXP` with every call event answered by `C` (`evalOXP_path`).

The cases are `ExposeE`'s, read for body results `ResP`: a flow result is `ofRes` of `ExposeE`'s
(`liftP`), and a pending tail call is a value that every continuation passes.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.ExposeP

open Silmaril.Wasm Silmaril.Games Silmaril.Games.Abstract Silmaril.Wasm.Abstract
  Silmaril.Wasm.Abstract.Body Silmaril.Wasm.Abstract.BodyTrace Silmaril.Wasm.Binaryen
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract.StoreBody Silmaril.Wasm.Abstract.StoreCall
  Silmaril.Wasm.Abstract.CallX Silmaril.Wasm.Abstract.CallXP Silmaril.Wasm.Abstract.ExposeE
  Silmaril.Wasm.Abstract.ExposeP
  Silmaril.Elgot.ITree Silmaril.Proofs.Wasm.Abstract.StoreBody
  Silmaril.Proofs.Wasm.Abstract.StoreCall Silmaril.Proofs.Wasm.Abstract.CallX
  Silmaril.Proofs.Wasm.Abstract.ExposeE
open Silmaril.Wasm.Abstract.CallXT (typeArity tailAnn)

variable {H : Type}

/-! ## Body results -/

theorem notNormal_flowP {fl : Flow} (h : ¬ fl.IsNormal) : ¬ (POut.flow fl).IsNormal := h

theorem notNormal_tailP {a n : Nat} {args : List Val} : ¬ (POut.tail a args n).IsNormal :=
  fun h => h

theorem notNormal_of_escapesP {o : POut} (h : o.Escapes) : ¬ o.IsNormal := by
  cases o with
  | flow fl => exact Flow.not_normal_of_escapes h
  | tail => exact id

/-- The body result after a block's exits. -/
def blockFlowP (np nr : Nat) (stk : List Val) : POut → POut
  | .flow fl => .flow (blockFlow np nr stk fl)
  | o => o

theorem blockFlowP_esc {np nr : Nat} {stk : List Val} {o : POut} (h : o.Escapes) :
    blockFlowP np nr stk o = o := by
  cases o with
  | flow fl => exact congrArg POut.flow (blockFlow_esc h)
  | tail => rfl

/-! ## Paths through the continuations -/

section
variable {s : St H} {cs : List (Call (CallSig H))}

theorem path_liftP {x : M (CallSig H) H Res} {s₁ : Store H} {f₁ : Frame} {fl : Flow}
    (h : Path (run' x s) cs (endR (s₁, f₁, fl))) :
    Path (run' (liftP x) s) cs (endRP (s₁, f₁, .flow fl)) := by
  cases fl
  case trap => exact path_bind_err h
  all_goals exact path_bind_pure h rfl

theorem path_thenKP_normal {k : Frame → List Val → M (CallSig H) H ResP}
    {x : M (CallSig H) H ResP} {cs₂ : List (Call (CallSig H))} {s₁ : Store H} {f₁ : Frame}
    {stk₁ : List Val} {e : PathEnd (Except PUnit.{2} (ResP × St H))}
    (h₁ : Path (run' x s) cs (endRP (s₁, f₁, .flow (.normal stk₁))))
    (h₂ : Path (run' (k f₁ stk₁) ⟨s₁⟩) cs₂ e) :
    Path (run' (x >>= thenKP k) s) (cs ++ cs₂) e :=
  path_bind_ok h₁ h₂

theorem path_thenKP_pass {k : Frame → List Val → M (CallSig H) H ResP}
    {x : M (CallSig H) H ResP} {s₁ : Store H} {f₁ : Frame} {o : POut}
    (h : Path (run' x s) cs (endRP (s₁, f₁, o))) (ho : ¬ o.IsNormal) :
    Path (run' (x >>= thenKP k) s) cs (endRP (s₁, f₁, o)) := by
  cases o with
  | flow fl =>
    cases fl
    case normal => exact absurd trivial ho
    case trap => exact path_bind_err h
    all_goals exact path_bind_pure h rfl
  | tail => exact path_bind_pure h rfl

theorem path_blockKP {np nr : Nat} {stk : List Val} {x : M (CallSig H) H ResP} {s₁ : Store H}
    {f₁ : Frame} {o : POut} (h : Path (run' x s) cs (endRP (s₁, f₁, o))) :
    Path (run' (x >>= blockKP np nr stk) s) cs (endRP (s₁, f₁, blockFlowP np nr stk o)) := by
  cases o with
  | flow fl =>
    cases fl with
    | trap => exact path_bind_err h
    | brk k vs => cases k <;> exact path_bind_pure h rfl
    | _ => exact path_bind_pure h rfl
  | tail => exact path_bind_pure h rfl

theorem tryKP_ne {np nr : Nat} {stk : List Val} {cs : List Catch} {f : Frame} {o : POut}
    (h : o.NotThrow) :
    (tryKP (H := H) np nr stk cs ⟨(f, o)⟩) = blockKP np nr stk ⟨(f, o)⟩ := by
  cases o with
  | flow fl => cases fl <;> first | rfl | exact absurd h id
  | tail => rfl

theorem path_tryKP_ne {np nr : Nat} {stk : List Val} {cs' : List Catch}
    {x : M (CallSig H) H ResP} {s₁ : Store H} {f₁ : Frame} {o : POut}
    (h : Path (run' x s) cs (endRP (s₁, f₁, o))) (hnt : o.NotThrow) :
    Path (run' (x >>= tryKP np nr stk cs') s) cs (endRP (s₁, f₁, blockFlowP np nr stk o)) := by
  cases o with
  | flow fl =>
    cases fl with
    | trap => exact path_bind_err h
    | throw a => exact absurd hnt id
    | brk k vs => cases k <;> exact path_bind_pure h rfl
    | _ => exact path_bind_pure h rfl
  | tail => exact path_bind_pure h rfl

theorem run_tryKP_throw {np nr : Nat} {stk : List Val} {cs' : List Catch} {f₁ : Frame} {a : Nat}
    (s₁ : Store H) :
    run' (tryKP np nr stk cs' ⟨(f₁, .flow (.throw a))⟩ : M (CallSig H) H ResP) ⟨s₁⟩ =
      run' (match resolveCatch s₁ f₁ a cs' with
        | some (some (us, l)) => pure ⟨(f₁, .flow (.brk l.toNat (us.reverse ++ stk.drop np)))⟩
        | some none => pure ⟨(f₁, .flow (.throw a))⟩
        | none => stuck : M (CallSig H) H ResP) ⟨s₁⟩ :=
  run_getState_bind _ _

theorem path_tryKP_catch {np nr : Nat} {stk : List Val} {cs' : List Catch}
    {x : M (CallSig H) H ResP} {s₁ : Store H} {f₁ : Frame} {a : Nat} {us : List Val}
    {l : LabelIdx} (h : Path (run' x s) cs (endRP (s₁, f₁, .flow (.throw a))))
    (hc : Cfg.Region.Catches s₁ f₁ a cs' (some (us, l))) :
    Path (run' (x >>= tryKP np nr stk cs') s) cs
      (endRP (s₁, f₁, .flow (.brk l.toNat (us.reverse ++ stk.drop np)))) := by
  have h₂ : Path (run' (tryKP np nr stk cs' ⟨(f₁, .flow (.throw a))⟩ : M (CallSig H) H ResP)
      ⟨s₁⟩) [] (endRP (s₁, f₁, .flow (.brk l.toNat (us.reverse ++ stk.drop np)))) := by
    rw [run_tryKP_throw, resolveCatch_eq hc]
    exact .ret rfl
  have := path_bind_ok h h₂
  rwa [List.append_nil] at this

theorem path_tryKP_rethrow {np nr : Nat} {stk : List Val} {cs' : List Catch}
    {x : M (CallSig H) H ResP} {s₁ : Store H} {f₁ : Frame} {a : Nat}
    (h : Path (run' x s) cs (endRP (s₁, f₁, .flow (.throw a))))
    (hc : Cfg.Region.Catches s₁ f₁ a cs' none) :
    Path (run' (x >>= tryKP np nr stk cs') s) cs (endRP (s₁, f₁, .flow (.throw a))) := by
  have h₂ : Path (run' (tryKP np nr stk cs' ⟨(f₁, .flow (.throw a))⟩ : M (CallSig H) H ResP)
      ⟨s₁⟩) [] (endRP (s₁, f₁, .flow (.throw a))) := by
    rw [run_tryKP_throw, resolveCatch_eq hc]
    exact .ret rfl
  have := path_bind_ok h h₂
  rwa [List.append_nil] at this

end

/-! ## Equations of the exposed body -/

theorem denListXP_cons (e : BExpr) (es : List BExpr) (f : Frame) (stk : List Val) :
    (denListXP (H := H) (e :: es) f stk) = denXP e f stk >>= thenKP (denListXP es) := by
  rw [denListXP.eq_def]

theorem denXP_op (i : Instr) (args : List BExpr) (f : Frame) (stk : List Val) :
    (denXP (H := H) (.op i args) f stk) = denListXP args f stk >>= thenKP (opCXP i) := by
  rw [denXP.eq_def]

theorem denXP_block (bt : BlockType) (body : List BExpr) (f : Frame) (stk : List Val) :
    (denXP (H := H) (.block bt body) f stk) =
      match arity f bt with
      | some (np, nr) => denListXP body f (stk.take np) >>= blockKP np nr stk
      | none => stuck := by
  rw [denXP.eq_def]; rfl

theorem denXP_loop (bt : BlockType) (body : List BExpr) (f : Frame) (stk : List Val) :
    (denXP (H := H) (.loop bt body) f stk) =
      Silmaril.Elgot.iter (loopBodyXP bt body) ⟨(f, stk)⟩ := by
  rw [denXP.eq_def]; rfl

theorem denXP_if (bt : BlockType) (c t el : List BExpr) (f : Frame) (stk : List Val) :
    (denXP (H := H) (.if_ bt c t el) f stk) =
      denListXP c f stk >>= fun r =>
        match r with
        | ⟨(f₁, .flow (.normal (cv :: stk₁)))⟩ =>
          match truthy cv, arity f₁ bt with
          | some b, some (np, nr) =>
            (if b then denListXP t f₁ (stk₁.take np) else denListXP el f₁ (stk₁.take np)) >>=
              blockKP np nr stk₁
          | _, _ => stuck
        | ⟨(_, .flow (.normal []))⟩ => stuck
        | r => pure r := by
  rw [denXP.eq_def]; rfl

theorem denXP_try (bt : BlockType) (cs : List Catch) (body : List BExpr) (f : Frame)
    (stk : List Val) :
    (denXP (H := H) (.tryTable bt cs body) f stk) =
      match arity f bt with
      | some (np, nr) => denListXP body f (stk.take np) >>= tryKP np nr stk cs
      | none => stuck := by
  rw [denXP.eq_def]; rfl

theorem denXP_loop_unfold (bt : BlockType) (body : List BExpr) (f : Frame) (stk : List Val) :
    (denXP (H := H) (.loop bt body) f stk) =
      (loopBodyXP bt body ⟨(f, stk)⟩ >>= Sum.elim pure
        fun c : ULift.{1} (Frame × List Val) => denXP (.loop bt body) c.down.1 c.down.2) := by
  rw [denXP_loop]
  exact (congrFun (Silmaril.Elgot.LawfulElgotMonad.fixpoint (m := M (CallSig H) H)
    (loopBodyXP bt body)) ⟨(f, stk)⟩).trans rfl

/-! ## Operators -/

theorem opCXP_notX {i : Instr} (hx : isXCall i = false) (f : Frame) (stk : List Val) :
    opCXP (H := H) i f stk = liftP (opCXE i f stk) := by
  cases i <;> first | rfl | exact absurd hx (by simp [isXCall])

theorem opCXP_tail {i : Instr} (h : isXTail i) : opCXP (H := H) i = tailPendEv i := by
  funext f stk
  cases i <;> first | exact absurd h id | rfl

theorem calleeTyped_of {s : Store H} {f : Frame} {y : TypeIdx} {fa : Nat} {fi : FuncInst H}
    {ps rs : List Validation.CValType} (hfi : s.funcs[fa]? = some fi)
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    (hy : typeArity f.module y = some (ps.length, rs.length)) : calleeTyped s f y fa := by
  intro fi' ps' rs' h₁ h₂
  rw [hfi] at h₁; cases h₁
  rw [hty] at h₂; cases h₂
  exact hy

theorem tailTyped_of {i : Instr} {f : Frame} {ps rs : List Validation.CValType}
    (hy : ∀ y, tailAnn i = some y → typeArity f.module y = some (ps.length, rs.length)) :
    tailTyped i f ps rs := hy

theorem path_callAtT {y : TypeIdx} {fa : Nat} {f : Frame} {stk : List Val} {s : Store H}
    {fi : FuncInst H} {ps rs : List Validation.CValType} (hfi : s.funcs[fa]? = some fi)
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    (hy : typeArity f.module y = some (ps.length, rs.length)) (ans : Store H × Flow)
    {cs : List (Call (CallSig H))} {e : PathEnd (Except PUnit.{2} (Res × St H))}
    (h : Path (run' (callAns f stk ps rs ans) ⟨s⟩) cs e) :
    Path (run' (callAtT y fa f stk) ⟨s⟩) (⟨(fa, (stk.take ps.length).reverse, s), ans⟩ :: cs) e := by
  rw [callAtT, run_getState_bind]
  rw [ite_eq_left (calleeTyped_of hfi hty hy)]
  exact path_callAt hfi hty ans h

theorem path_callAns_abrupt {f : Frame} {stk : List Val} {ps rs : List Validation.CValType}
    {s₂ : Store H} {fl : Flow} (hfl : fl.Abrupt) (s : St H) :
    Path (run' (callAns f stk ps rs (s₂, fl)) s) [] (endR (s₂, f, fl)) := by
  cases fl with
  | trap => exact path_callAns_trap _
  | throw t => exact path_callAns_throw _
  | _ => exact absurd hfl id

theorem abrupt_notNormal {fl : Flow} (h : fl.Abrupt) : ¬ fl.IsNormal := by
  cases fl <;> simp_all [Flow.Abrupt, Flow.IsNormal]

/-- **Every `EvalOXP C` derivation is a path of the exposed abstract body**, with every call
event answered as `C` allows, ending as the derivation does (a pending tail call as a value). -/
theorem evalOXP_path {C : CallRel H} {s : Store H} {f : Frame} {stk : List Val}
    {es : List BExpr} {r : Store H × Frame × POut} (h : EvalOXP C s f stk es r) :
    ∃ cs, Answered C cs ∧
      Path (run' (denListXP es f stk : M (CallSig H) H ResP) ⟨s⟩) cs (endRP r) := by
  induction h with
  | nil => exact ⟨[], answered_nil, .ret rfl⟩
  | argsAbort _ hfl ih =>
    obtain ⟨cs, hA, hp⟩ := ih
    refine ⟨cs, hA, ?_⟩
    rw [denListXP_cons, denXP_op]
    exact path_thenKP_pass (path_thenKP_pass hp hfl) hfl
  | @callOk s s₁ s₂ f f₁ stk stk₁ vs x args es a fi ps rs fl r _ hfi hty hcall hvs _ ih₁ ih₂ =>
    obtain ⟨cs₁, hA₁, hp₁⟩ := ih₁
    obtain ⟨cs₂, hA₂, hp₂⟩ := ih₂
    refine ⟨cs₁ ++ [⟨(a, (stk₁.take ps.length).reverse, s₁), (s₂, fl)⟩] ++ cs₂,
      answered_append (answered_append hA₁ (answered_single hcall)) hA₂, ?_⟩
    rw [denListXP_cons, denXP_op]
    refine path_thenKP_normal (path_thenKP_normal hp₁ ?_) hp₂
    rw [opCXP_notX rfl]
    exact path_liftP (path_callEv hfi hty (s₂, fl) (path_callAns_vals hvs _))
  | @callTrap s s₁ s₂ f f₁ stk stk₁ x args es a fi ps rs _ hfi hty hcall ih₁ =>
    obtain ⟨cs₁, hA₁, hp₁⟩ := ih₁
    refine ⟨cs₁ ++ [⟨(a, (stk₁.take ps.length).reverse, s₁), (s₂, .trap)⟩],
      answered_append hA₁ (answered_single hcall), ?_⟩
    rw [denListXP_cons, denXP_op]
    refine path_thenKP_pass (path_thenKP_normal hp₁ ?_) (notNormal_flowP Flow.notNormal_trap)
    rw [opCXP_notX rfl]
    exact path_liftP (path_callEv hfi hty (s₂, .trap) (path_callAns_trap _))
  | @callThrow s s₁ s₂ f f₁ stk stk₁ x args es a fi ps rs t _ hfi hty hcall ih₁ =>
    obtain ⟨cs₁, hA₁, hp₁⟩ := ih₁
    refine ⟨cs₁ ++ [⟨(a, (stk₁.take ps.length).reverse, s₁), (s₂, .throw t)⟩],
      answered_append hA₁ (answered_single hcall), ?_⟩
    rw [denListXP_cons, denXP_op]
    refine path_thenKP_pass (path_thenKP_normal hp₁ ?_) (notNormal_flowP Flow.notNormal_throw)
    rw [opCXP_notX rfl]
    exact path_liftP (path_callEv hfi hty (s₂, .throw t) (path_callAns_throw _))
  | @opOk s s₁ s₂ f f₁ f₂ stk stk₁ stk₂ i args es r hi _ hflat _ ih₁ ih₂ =>
    obtain ⟨cs₁, hA₁, hp₁⟩ := ih₁
    obtain ⟨cs₂, hA₂, hp₂⟩ := ih₂
    refine ⟨cs₁ ++ [] ++ cs₂, answered_append (answered_append hA₁ answered_nil) hA₂, ?_⟩
    rw [denListXP_cons, denXP_op]
    refine path_thenKP_normal (path_thenKP_normal hp₁ ?_) hp₂
    rw [opCXP_notX (notX_of_flat hflat),
      opCXE_flat hi (notX_of_flat hflat) (notEH_of_flat hflat)]
    exact path_liftP (path_flatK hflat)
  | @opStop s s₁ s₂ f f₁ f₂ stk stk₁ i args es fl hi _ hflat hfl ih₁ =>
    obtain ⟨cs₁, hA₁, hp₁⟩ := ih₁
    refine ⟨cs₁ ++ [], answered_append hA₁ answered_nil, ?_⟩
    rw [denListXP_cons, denXP_op]
    refine path_thenKP_pass (path_thenKP_normal hp₁ ?_) (notNormal_flowP hfl)
    rw [opCXP_notX (notX_of_flat hflat),
      opCXE_flat hi (notX_of_flat hflat) (notEH_of_flat hflat)]
    exact path_liftP (path_flatK hflat)
  | @blockOk s s₁ f f₁ stk vs bt body es np nr fl r har _ hvs _ ih₁ ih₂ =>
    obtain ⟨cs₁, hA₁, hp₁⟩ := ih₁
    obtain ⟨cs₂, hA₂, hp₂⟩ := ih₂
    refine ⟨cs₁ ++ cs₂, answered_append hA₁ hA₂, ?_⟩
    rw [denListXP_cons, denXP_block]
    simp only [har]
    have hb := path_blockKP (np := np) (nr := nr) (stk := stk) hp₁
    simp only [blockFlowP, blockFlow_of_vals hvs] at hb
    exact path_thenKP_normal hb hp₂
  | @blockBrk s s₁ f f₁ stk vs bt body es np nr k har _ ih =>
    obtain ⟨cs, hA, hp⟩ := ih
    refine ⟨cs, hA, ?_⟩
    rw [denListXP_cons, denXP_block]
    simp only [har]
    exact path_thenKP_pass (path_blockKP (np := np) (nr := nr) (stk := stk) hp)
      (notNormal_flowP Flow.notNormal_brk)
  | @blockEsc s s₁ f f₁ stk bt body es np nr o har _ ho ih =>
    obtain ⟨cs, hA, hp⟩ := ih
    refine ⟨cs, hA, ?_⟩
    rw [denListXP_cons, denXP_block]
    simp only [har]
    have hb := path_blockKP (np := np) (nr := nr) (stk := stk) hp
    rw [blockFlowP_esc ho] at hb
    exact path_thenKP_pass hb (notNormal_of_escapesP ho)
  | @loopOk s s₁ f f₁ stk vs bt body es np nr r har _ _ ih₁ ih₂ =>
    obtain ⟨cs₁, hA₁, hp₁⟩ := ih₁
    obtain ⟨cs₂, hA₂, hp₂⟩ := ih₂
    refine ⟨cs₁ ++ cs₂, answered_append hA₁ hA₂, ?_⟩
    rw [denListXP_cons, denXP_loop_unfold]
    have h1 : Path (run' (loopBodyXP bt body ⟨(f, stk)⟩) ⟨s⟩) cs₁
        (.val (.ok (.inl ⟨(f₁, .flow (.normal (vs.take nr ++ stk.drop np)))⟩, ⟨s₁⟩))) := by
      simp only [loopBodyXP, har]; exact path_bind_pure hp₁ rfl
    exact path_thenKP_normal (path_bind_pure h1 rfl) hp₂
  | @loopBack s s₁ f f₁ stk vs bt body es np nr r har _ _ ih₁ ih₂ =>
    obtain ⟨cs₁, hA₁, hp₁⟩ := ih₁
    obtain ⟨cs₂, hA₂, hp₂⟩ := ih₂
    refine ⟨cs₁ ++ cs₂, answered_append hA₁ hA₂, ?_⟩
    rw [denListXP_cons, denXP_loop_unfold, bind_assoc]
    have h1 : Path (run' (loopBodyXP bt body ⟨(f, stk)⟩) ⟨s⟩) cs₁
        (.val (.ok (.inr ⟨(f₁, vs.take np ++ stk.drop np)⟩, ⟨s₁⟩))) := by
      simp only [loopBodyXP, har]; exact path_bind_pure hp₁ rfl
    rw [denListXP_cons] at hp₂
    exact path_bind_ok h1 hp₂
  | @loopBrk s s₁ f f₁ stk vs bt body es np nr k har _ ih =>
    obtain ⟨cs, hA, hp⟩ := ih
    refine ⟨cs, hA, ?_⟩
    rw [denListXP_cons, denXP_loop_unfold]
    have h1 : Path (run' (loopBodyXP bt body ⟨(f, stk)⟩) ⟨s⟩) cs
        (.val (.ok (.inl ⟨(f₁, .flow (.brk k vs))⟩, ⟨s₁⟩))) := by
      simp only [loopBodyXP, har]; exact path_bind_pure hp rfl
    exact path_thenKP_pass (path_bind_pure h1 rfl) (notNormal_flowP Flow.notNormal_brk)
  | @loopEsc s s₁ f f₁ stk bt body es np nr o har _ ho ih =>
    obtain ⟨cs, hA, hp⟩ := ih
    refine ⟨cs, hA, ?_⟩
    rw [denListXP_cons, denXP_loop_unfold]
    refine path_thenKP_pass ?_ (notNormal_of_escapesP ho)
    cases o with
    | flow fl =>
      cases fl
      case trap =>
        refine path_bind_err ?_
        simp only [loopBodyXP, har]; exact path_bind_err hp
      all_goals first
        | exact absurd ho id
        | (refine path_bind_pure (a := .inl ⟨(f₁, _)⟩) ?_ rfl
           simp only [loopBodyXP, har]; exact path_bind_pure hp rfl)
    | tail =>
      refine path_bind_pure (a := .inl ⟨(f₁, _)⟩) ?_ rfl
      simp only [loopBodyXP, har]; exact path_bind_pure hp rfl
  | @ifOk s s₁ s₂ f f₁ f₂ stk stk₁ vs cv b bt c t el es np nr fl r _ hb har _ hvs _ ih₁ ih₂ ih₃ =>
    obtain ⟨cs₁, hA₁, hp₁⟩ := ih₁
    obtain ⟨cs₂, hA₂, hp₂⟩ := ih₂
    obtain ⟨cs₃, hA₃, hp₃⟩ := ih₃
    refine ⟨cs₁ ++ (cs₂ ++ cs₃), answered_append hA₁ (answered_append hA₂ hA₃), ?_⟩
    rw [denListXP_cons, denXP_if, bind_assoc]
    refine path_bind_ok hp₁ ?_
    simp only [hb, har]
    have harm : Path (run' ((if b then denListXP t f₁ (stk₁.take np) else
        denListXP el f₁ (stk₁.take np)) : M (CallSig H) H ResP) ⟨s₁⟩) cs₂
        (endRP (s₂, f₂, .flow fl)) := by
      cases b <;> exact hp₂
    have hbk := path_blockKP (np := np) (nr := nr) (stk := stk₁) harm
    simp only [blockFlowP, blockFlow_of_vals hvs] at hbk
    exact path_thenKP_normal hbk hp₃
  | @ifBrk s s₁ s₂ f f₁ f₂ stk stk₁ vs cv b bt c t el es np nr k _ hb har _ ih₁ ih₂ =>
    obtain ⟨cs₁, hA₁, hp₁⟩ := ih₁
    obtain ⟨cs₂, hA₂, hp₂⟩ := ih₂
    refine ⟨cs₁ ++ cs₂, answered_append hA₁ hA₂, ?_⟩
    rw [denListXP_cons, denXP_if, bind_assoc]
    refine path_bind_ok hp₁ ?_
    simp only [hb, har]
    have harm : Path (run' ((if b then denListXP t f₁ (stk₁.take np) else
        denListXP el f₁ (stk₁.take np)) : M (CallSig H) H ResP) ⟨s₁⟩) cs₂
        (endRP (s₂, f₂, .flow (.brk (k + 1) vs))) := by
      cases b <;> exact hp₂
    exact path_thenKP_pass (path_blockKP (np := np) (nr := nr) (stk := stk₁) harm)
      (notNormal_flowP Flow.notNormal_brk)
  | @ifEsc s s₁ s₂ f f₁ f₂ stk stk₁ cv b bt c t el es np nr o _ hb har _ ho ih₁ ih₂ =>
    obtain ⟨cs₁, hA₁, hp₁⟩ := ih₁
    obtain ⟨cs₂, hA₂, hp₂⟩ := ih₂
    refine ⟨cs₁ ++ cs₂, answered_append hA₁ hA₂, ?_⟩
    rw [denListXP_cons, denXP_if, bind_assoc]
    refine path_bind_ok hp₁ ?_
    simp only [hb, har]
    have harm : Path (run' ((if b then denListXP t f₁ (stk₁.take np) else
        denListXP el f₁ (stk₁.take np)) : M (CallSig H) H ResP) ⟨s₁⟩) cs₂
        (endRP (s₂, f₂, o)) := by
      cases b <;> exact hp₂
    have hbk := path_blockKP (np := np) (nr := nr) (stk := stk₁) harm
    rw [blockFlowP_esc ho] at hbk
    exact path_thenKP_pass hbk (notNormal_of_escapesP ho)
  | @ifAbort s s₁ f f₁ stk bt c t el es o _ ho ih =>
    obtain ⟨cs, hA, hp⟩ := ih
    refine ⟨cs, hA, ?_⟩
    rw [denListXP_cons, denXP_if]
    refine path_thenKP_pass ?_ ho
    cases o with
    | flow fl =>
      cases fl
      case normal => exact absurd trivial ho
      case trap => exact path_bind_err hp
      all_goals exact path_bind_pure hp rfl
    | tail => exact path_bind_pure hp rfl
  | @callIndOk s s₁ s₂ f f₁ stk stk₁ vs x y args es ad i fa fi ps rs fl r _ hres hfi hty hy hcall
      hvs _ ih₁ ih₂ =>
    obtain ⟨cs₁, hA₁, hp₁⟩ := ih₁
    obtain ⟨cs₂, hA₂, hp₂⟩ := ih₂
    refine ⟨cs₁ ++ [⟨(fa, (stk₁.take ps.length).reverse, s₁), (s₂, fl)⟩] ++ cs₂,
      answered_append (answered_append hA₁ (answered_single hcall)) hA₂, ?_⟩
    rw [denListXP_cons, denXP_op]
    refine path_thenKP_normal (path_thenKP_normal hp₁ (path_liftP ?_)) hp₂
    show Path (run' (indEvT x y f₁ _) ⟨s₁⟩) _ _
    rw [indEvT, run_getState_bind]
    simp only [resolveInd_eq (p := (some fa, stk₁)) ⟨ad, i, rfl, hres⟩]
    exact path_callAtT hfi hty hy (s₂, fl) (path_callAns_vals hvs _)
  | @callIndRes s s₁ f f₁ stk stk₁ x y args es ad i _ hres ih =>
    obtain ⟨cs₁, hA₁, hp₁⟩ := ih
    refine ⟨cs₁ ++ [], answered_append hA₁ answered_nil, ?_⟩
    rw [denListXP_cons, denXP_op]
    refine path_thenKP_pass (path_thenKP_normal hp₁ (path_liftP ?_))
      (notNormal_flowP Flow.notNormal_trap)
    show Path (run' (indEvT x y f₁ _) ⟨s₁⟩) _ _
    rw [indEvT, run_getState_bind]
    simp only [resolveInd_eq (p := (none, stk₁)) ⟨ad, i, rfl, hres⟩]
    exact .ret (run_trapS _)
  | @callIndStop s s₁ s₂ f f₁ stk stk₁ x y args es ad i fa fi ps rs fl _ hres hfi hty hy hcall
      hfl ih =>
    obtain ⟨cs₁, hA₁, hp₁⟩ := ih
    refine ⟨cs₁ ++ [⟨(fa, (stk₁.take ps.length).reverse, s₁), (s₂, fl)⟩],
      answered_append hA₁ (answered_single hcall), ?_⟩
    rw [denListXP_cons, denXP_op]
    refine path_thenKP_pass (path_thenKP_normal hp₁ (path_liftP ?_))
      (notNormal_flowP (abrupt_notNormal hfl))
    show Path (run' (indEvT x y f₁ _) ⟨s₁⟩) _ _
    rw [indEvT, run_getState_bind]
    simp only [resolveInd_eq (p := (some fa, stk₁)) ⟨ad, i, rfl, hres⟩]
    exact path_callAtT hfi hty hy (s₂, fl) (path_callAns_abrupt hfl _)
  | @callRefOk s s₁ s₂ f f₁ stk stk₁ vs y args es fa fi ps rs fl r _ hfi hty hy hcall hvs _
      ih₁ ih₂ =>
    obtain ⟨cs₁, hA₁, hp₁⟩ := ih₁
    obtain ⟨cs₂, hA₂, hp₂⟩ := ih₂
    refine ⟨cs₁ ++ [⟨(fa, (stk₁.take ps.length).reverse, s₁), (s₂, fl)⟩] ++ cs₂,
      answered_append (answered_append hA₁ (answered_single hcall)) hA₂, ?_⟩
    rw [denListXP_cons, denXP_op]
    exact path_thenKP_normal (path_thenKP_normal hp₁
      (path_liftP (path_callAtT hfi hty hy (s₂, fl) (path_callAns_vals hvs _)))) hp₂
  | @callRefNull s s₁ f f₁ stk stk₁ y args es _ ih =>
    obtain ⟨cs₁, hA₁, hp₁⟩ := ih
    refine ⟨cs₁ ++ [], answered_append hA₁ answered_nil, ?_⟩
    rw [denListXP_cons, denXP_op]
    exact path_thenKP_pass (path_thenKP_normal hp₁ (path_liftP (.ret (run_trapS _))))
      (notNormal_flowP Flow.notNormal_trap)
  | @callRefStop s s₁ s₂ f f₁ stk stk₁ y args es fa fi ps rs fl _ hfi hty hy hcall hfl ih =>
    obtain ⟨cs₁, hA₁, hp₁⟩ := ih
    refine ⟨cs₁ ++ [⟨(fa, (stk₁.take ps.length).reverse, s₁), (s₂, fl)⟩],
      answered_append hA₁ (answered_single hcall), ?_⟩
    rw [denListXP_cons, denXP_op]
    exact path_thenKP_pass (path_thenKP_normal hp₁
      (path_liftP (path_callAtT hfi hty hy (s₂, fl) (path_callAns_abrupt hfl _))))
      (notNormal_flowP (abrupt_notNormal hfl))
  | @tail s s₁ f f₁ stk stk₁ i args es fa fi ps rs _ hres hfi hty hy ih =>
    obtain ⟨cs₁, hA₁, hp₁⟩ := ih
    refine ⟨cs₁ ++ [], answered_append hA₁ answered_nil, ?_⟩
    rw [denListXP_cons, denXP_op]
    refine path_thenKP_pass (path_thenKP_normal hp₁ ?_) notNormal_tailP
    rw [opCXP_tail (isXTail_of_tailRes hres), tailPendEv, run_getState_bind]
    simp only [resolveTail_eq hres, hfi, hty]
    rw [ite_eq_left (tailTyped_of hy)]
    exact .ret rfl
  | @tailRes s s₁ f f₁ stk stk₁ i args es _ hres ih =>
    obtain ⟨cs₁, hA₁, hp₁⟩ := ih
    refine ⟨cs₁ ++ [], answered_append hA₁ answered_nil, ?_⟩
    rw [denListXP_cons, denXP_op]
    refine path_thenKP_pass (path_thenKP_normal hp₁ ?_) (notNormal_flowP Flow.notNormal_trap)
    rw [opCXP_tail (isXTail_of_tailRes hres), tailPendEv, run_getState_bind]
    simp only [resolveTail_eq hres]
    exact .ret (run_trapS _)
  | @throw s s₁ f f₁ stk stk₁ x args es ta ti ts _ ht he hn ih =>
    obtain ⟨cs₁, hA₁, hp₁⟩ := ih
    refine ⟨cs₁ ++ [], answered_append hA₁ answered_nil, ?_⟩
    rw [denListXP_cons, denXP_op]
    refine path_thenKP_pass (path_thenKP_normal hp₁ ?_) (notNormal_flowP Flow.notNormal_throw)
    rw [opCXP_notX rfl]
    refine path_liftP ?_
    show Path (run' (throwEv x f₁ _) ⟨s₁⟩) _ _
    rw [throwEv, run_getState_bind]
    simp only [resolveThrow_eq (p := (ta, ts.length)) ⟨ti, ts, ht, he, rfl, hn⟩]
    exact .ret (run_set_pure _ _ _)
  | @throwRefNull s s₁ f f₁ stk stk₁ args es _ ih =>
    obtain ⟨cs₁, hA₁, hp₁⟩ := ih
    refine ⟨cs₁ ++ [], answered_append hA₁ answered_nil, ?_⟩
    rw [denListXP_cons, denXP_op]
    refine path_thenKP_pass (path_thenKP_normal hp₁ ?_) (notNormal_flowP Flow.notNormal_trap)
    rw [opCXP_notX rfl]
    exact path_liftP (.ret (run_trapS _))
  | @throwRefExn s s₁ f f₁ stk stk₁ a args es _ ih =>
    obtain ⟨cs₁, hA₁, hp₁⟩ := ih
    refine ⟨cs₁ ++ [], answered_append hA₁ answered_nil, ?_⟩
    rw [denListXP_cons, denXP_op]
    refine path_thenKP_pass (path_thenKP_normal hp₁ ?_) (notNormal_flowP Flow.notNormal_throw)
    rw [opCXP_notX rfl]
    exact path_liftP (.ret rfl)
  | @tryOk s s₁ f f₁ stk vs bt cs body es np nr fl r har _ hvs _ ih₁ ih₂ =>
    obtain ⟨cs₁, hA₁, hp₁⟩ := ih₁
    obtain ⟨cs₂, hA₂, hp₂⟩ := ih₂
    refine ⟨cs₁ ++ cs₂, answered_append hA₁ hA₂, ?_⟩
    rw [denListXP_cons, denXP_try]
    simp only [har]
    have hnt : POut.NotThrow (.flow fl) := by
      cases fl <;> trivial
    have hb := path_tryKP_ne (np := np) (nr := nr) (stk := stk) (cs' := cs) hp₁ hnt
    simp only [blockFlowP, blockFlow_of_vals hvs] at hb
    exact path_thenKP_normal hb hp₂
  | @tryBrk s s₁ f f₁ stk vs bt cs body es np nr k har _ ih =>
    obtain ⟨cl, hA, hp⟩ := ih
    refine ⟨cl, hA, ?_⟩
    rw [denListXP_cons, denXP_try]
    simp only [har]
    exact path_thenKP_pass (path_tryKP_ne (np := np) (nr := nr) (stk := stk) (cs' := cs) hp
      trivial) (notNormal_flowP Flow.notNormal_brk)
  | @tryEsc s s₁ f f₁ stk bt cs body es np nr o har _ ho hnt ih =>
    obtain ⟨cl, hA, hp⟩ := ih
    refine ⟨cl, hA, ?_⟩
    rw [denListXP_cons, denXP_try]
    simp only [har]
    have hb := path_tryKP_ne (np := np) (nr := nr) (stk := stk) (cs' := cs) hp hnt
    rw [blockFlowP_esc ho] at hb
    exact path_thenKP_pass hb (notNormal_of_escapesP ho)
  | @tryCatch s s₁ f f₁ stk us bt cs body es np nr a l har _ hc ih =>
    obtain ⟨cl, hA, hp⟩ := ih
    refine ⟨cl, hA, ?_⟩
    rw [denListXP_cons, denXP_try]
    simp only [har]
    exact path_thenKP_pass (path_tryKP_catch hp hc) (notNormal_flowP Flow.notNormal_brk)
  | @tryRethrow s s₁ f f₁ stk bt cs body es np nr a har _ hc ih =>
    obtain ⟨cl, hA, hp⟩ := ih
    refine ⟨cl, hA, ?_⟩
    rw [denListXP_cons, denXP_try]
    simp only [har]
    exact path_thenKP_pass (path_tryKP_rethrow hp hc) (notNormal_flowP Flow.notNormal_throw)

end Silmaril.Proofs.Wasm.Abstract.ExposeP
