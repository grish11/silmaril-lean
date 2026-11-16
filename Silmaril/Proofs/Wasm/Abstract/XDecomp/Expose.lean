module

public import Silmaril.Wasm.Abstract.XDecomp.Defs
public import Silmaril.Wasm.Abstract.XRecursion.Thms
public import Silmaril.Proofs.Wasm.Abstract.CallX.Expose
public import Silmaril.Proofs.Wasm.Abstract.StoreCall.Descent

/-!
Proofs for `Silmaril.Wasm.Abstract.XDecomp.Thms`: descents through every call
form are pending call events of the exposed body `CallX.denListX`, after call
events answered by `closedCallX` (`reachX_pend`). The proof is
`StoreCall.reach_pend`'s, with the indirect, reference and tail calls made by
`indEv`, `refEv` and `tailEv` after their resolutions.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.XDecomp

open Silmaril.Wasm Silmaril.Games Silmaril.Games.Abstract Silmaril.Wasm.Abstract
  Silmaril.Wasm.Abstract.Body Silmaril.Wasm.Abstract.BodyTrace Silmaril.Wasm.Binaryen
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract.StoreBody Silmaril.Wasm.Abstract.StoreCall
  Silmaril.Elgot.ITree Silmaril.Proofs.Wasm.Abstract.StoreBody Silmaril.Proofs.Wasm.Abstract.BodyTrace
  Silmaril.Proofs.Wasm.Abstract.StoreCall
open Silmaril.Wasm.Abstract.CallX Silmaril.Wasm.Abstract.XRecursion Silmaril.Wasm.Abstract.XDecomp
open Silmaril.Proofs.Wasm.Abstract.CallX

variable {H : Type}

theorem pend_callAt {fa : Nat} {f : Frame} {stk : List Val} {s : Store H} {fi : FuncInst H}
    {ps rs : List Validation.CValType} (hfi : s.funcs[fa]? = some fi)
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) :
    Pend (run' (callAt fa f stk) ⟨s⟩) [] (fa, (stk.take ps.length).reverse, s) := by
  rw [run_callAt_vis hfi hty]; exact .here rfl

theorem pend_tailAt {fa : Nat} {f : Frame} {stk : List Val} {s : Store H} {fi : FuncInst H}
    {ps rs : List Validation.CValType} (hfi : s.funcs[fa]? = some fi)
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) :
    Pend (run' (tailAt fa f stk) ⟨s⟩) [] (fa, (stk.take ps.length).reverse, s) := by
  rw [run_tailAt_vis hfi hty]; exact .here rfl

theorem run_indEv_some {x : TableIdx} {y : TypeIdx} {f : Frame} {stk stk₁ : List Val}
    {s : Store H} {fa : Nat} (h : IndResS s f x y stk (some fa, stk₁)) :
    run' (indEv x y f stk) ⟨s⟩ = run' (callAt fa f stk₁) ⟨s⟩ := by
  rw [indEv, run_getState_bind]
  simp only [resolveInd_eq h]

theorem run_tailEv_some {i : Instr} {f : Frame} {stk stk₁ : List Val} {s : Store H} {fa : Nat}
    (h : TailRes s f i stk (some (fa, stk₁))) :
    run' (tailEv i f stk) ⟨s⟩ = run' (tailAt fa f stk₁) ⟨s⟩ := by
  rw [tailEv, run_getState_bind]
  simp only [resolveTail_eq h]

theorem path_closedX {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    {r : Store H × Frame × Flow} (h : EvalOX closedCallX s f stk es r) :
    ∃ cs, Answered closedCallX cs ∧
      Path (run' (denListX es f stk : M (CallSig H) H Res) ⟨s⟩) cs (endR r) :=
  Silmaril.Proofs.Wasm.Abstract.CallX.evalOX_path h

theorem closedCallX_of_body {s₁ s₂ : Store H} {fa : Nat} {fi : FuncInst H} {fn : Func}
    {ps rs : List Validation.CValType} {f₂ : Frame} {fl : Flow} {args : List Val}
    (hfi : s₁.funcs[fa]? = some fi) (hcode : fi.code = .wasm fn)
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    (hbody : EvalOX closedCallX s₁ (Frame.forCall fi.module args fn.locals) [] (liftInstrs fn.body)
      (s₂, f₂, fl)) : closedCallX s₁ fa args (s₂, fl) := by
  rw [closedCallX_fixpoint]
  exact ⟨fi, fn, ps, rs, f₂, hfi, hcode, hty, hbody⟩

/-- **Descents through every call form are pending call events** of the exposed
body, after call events answered by `closedCallX`. -/
theorem reachX_pend {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    {y : (wasmOShape H).self.Op} (h : ReachX s f stk es y) :
    ∃ cs, Answered closedCallX cs ∧
      Pend (run' (denListX es f stk : M (CallSig H) H Res) ⟨s⟩) cs (callOp y) := by
  induction h with
  | @here s s₁ f f₁ stk stk₁ x args es a fi ps rs hargs hfi hty =>
    obtain ⟨cs, hA, hp⟩ := path_closedX hargs
    refine ⟨cs ++ [], answered_append hA answered_nil, ?_⟩
    rw [denListX_cons, denX_op]
    exact pendR_bind_left (pendR_thenK hp (pend_callEv hfi hty))
  | args _ ih =>
    obtain ⟨cs, hA, hp⟩ := ih
    refine ⟨cs, hA, ?_⟩
    rw [denListX_cons, denX_op]
    exact pendR_bind_left (pendR_bind_left hp)
  | @callK s s₁ s₂ f f₁ f₂ stk stk₁ vs x args es a fi fn ps rs fl y hargs hfi hcode hty hbody hvs _ ih =>
    obtain ⟨cs₁, hA₁, hp₁⟩ := path_closedX hargs
    obtain ⟨cs₂, hA₂, hp₂⟩ := ih
    refine ⟨cs₁ ++ [⟨(a, (stk₁.take ps.length).reverse, s₁), (s₂, fl)⟩] ++ cs₂,
      answered_append (answered_append hA₁
        (answered_single (closedCallX_of_body (funcs_of_func? hfi) hcode hty hbody))) hA₂, ?_⟩
    rw [denListX_cons, denX_op]
    exact pendR_thenK (path_thenK_normal hp₁
      (path_callEv hfi hty (s₂, fl) (path_callAns_vals hvs _))) hp₂
  | @opK s s₁ s₂ f f₁ f₂ stk stk₁ stk₂ i args es y hi hargs hflat _ ih =>
    obtain ⟨cs₁, hA₁, hp₁⟩ := path_closedX hargs
    obtain ⟨cs₂, hA₂, hp₂⟩ := ih
    refine ⟨cs₁ ++ [] ++ cs₂, answered_append (answered_append hA₁ answered_nil) hA₂, ?_⟩
    rw [denListX_cons, denX_op]
    have hop : opCX i f₁ stk₁ = (flatK i f₁ stk₁ : M (CallSig H) H Res) := by
      rw [opCX_flat hi (notX_of_flat hflat)]
    exact pendR_thenK (path_thenK_normal hp₁ (hop ▸ path_flatK hflat)) hp₂
  | @block s f stk bt body es np nr y har _ ih =>
    obtain ⟨cs, hA, hp⟩ := ih
    refine ⟨cs, hA, ?_⟩
    rw [denListX_cons, denX_block]
    simp only [har]
    exact pendR_bind_left (pendR_bind_left hp)
  | @blockK s s₁ f f₁ stk vs bt body es np nr fl y har hbody hvs _ ih =>
    obtain ⟨cs₁, hA₁, hp₁⟩ := path_closedX hbody
    obtain ⟨cs₂, hA₂, hp₂⟩ := ih
    refine ⟨cs₁ ++ cs₂, answered_append hA₁ hA₂, ?_⟩
    rw [denListX_cons, denX_block]
    simp only [har]
    have hb := path_blockK (np := np) (nr := nr) (stk := stk) hp₁
    rw [blockFlow_of_vals hvs] at hb
    exact pendR_thenK hb hp₂
  | @loop s f stk bt body es np nr y har _ ih =>
    obtain ⟨cs, hA, hp⟩ := ih
    refine ⟨cs, hA, ?_⟩
    rw [denListX_cons, denX_loop_unfold]
    refine pendR_bind_left (pendR_bind_left ?_)
    simp only [loopBodyX, har]
    exact pendR_bind_left hp
  | @loopK s s₁ f f₁ stk vs bt body es np nr y har hbody _ ih =>
    obtain ⟨cs₁, hA₁, hp₁⟩ := path_closedX hbody
    obtain ⟨cs₂, hA₂, hp₂⟩ := ih
    refine ⟨cs₁ ++ cs₂, answered_append hA₁ hA₂, ?_⟩
    rw [denListX_cons, denX_loop_unfold]
    have h1 : Path (run' (loopBodyX bt body ⟨(f, stk)⟩) ⟨s⟩) cs₁
        (.val (.ok (.inl ⟨(f₁, .normal (vs.take nr ++ stk.drop np))⟩, ⟨s₁⟩))) := by
      simp only [loopBodyX, har]; exact path_bind_pure hp₁ rfl
    exact pendR_thenK (path_bind_pure h1 rfl) hp₂
  | @loopBack s s₁ f f₁ stk vs bt body es np nr y har hbody _ ih =>
    obtain ⟨cs₁, hA₁, hp₁⟩ := path_closedX hbody
    obtain ⟨cs₂, hA₂, hp₂⟩ := ih
    refine ⟨cs₁ ++ cs₂, answered_append hA₁ hA₂, ?_⟩
    rw [denListX_cons, denX_loop_unfold, bind_assoc]
    have h1 : Path (run' (loopBodyX bt body ⟨(f, stk)⟩) ⟨s⟩) cs₁
        (.val (.ok (.inr ⟨(f₁, vs.take np ++ stk.drop np)⟩, ⟨s₁⟩))) := by
      simp only [loopBodyX, har]; exact path_bind_pure hp₁ rfl
    rw [denListX_cons] at hp₂
    exact pendR_bind_ok h1 hp₂
  | cond _ ih =>
    obtain ⟨cs, hA, hp⟩ := ih
    refine ⟨cs, hA, ?_⟩
    rw [denListX_cons, denX_if]
    exact pendR_bind_left (pendR_bind_left hp)
  | @arm s s₁ f f₁ stk stk₁ cv b bt c t el es np nr y hc hb har _ ih =>
    obtain ⟨cs₁, hA₁, hp₁⟩ := path_closedX hc
    obtain ⟨cs₂, hA₂, hp₂⟩ := ih
    refine ⟨cs₁ ++ cs₂, answered_append hA₁ hA₂, ?_⟩
    rw [denListX_cons, denX_if, bind_assoc]
    refine pendR_bind_ok hp₁ ?_
    simp only [hb, har]
    refine pendR_bind_left (pendR_bind_left ?_)
    cases b <;> exact hp₂
  | @ifK s s₁ s₂ f f₁ f₂ stk stk₁ vs cv b bt c t el es np nr fl y hc hb har harm hvs _ ih =>
    obtain ⟨cs₁, hA₁, hp₁⟩ := path_closedX hc
    obtain ⟨cs₂, hA₂, hp₂⟩ := path_closedX harm
    obtain ⟨cs₃, hA₃, hp₃⟩ := ih
    refine ⟨cs₁ ++ (cs₂ ++ cs₃), answered_append hA₁ (answered_append hA₂ hA₃), ?_⟩
    rw [denListX_cons, denX_if, bind_assoc]
    refine pendR_bind_ok hp₁ ?_
    simp only [hb, har]
    have harm' : Path (run' ((if b then denListX t f₁ (stk₁.take np) else
        denListX el f₁ (stk₁.take np)) : M (CallSig H) H Res) ⟨s₁⟩) cs₂ (endR (s₂, f₂, fl)) := by
      cases b <;> exact hp₂
    have hbk := path_blockK (np := np) (nr := nr) (stk := stk₁) harm'
    rw [blockFlow_of_vals hvs] at hbk
    exact pendR_thenK hbk hp₃
  | @hereInd s s₁ f f₁ stk stk₁ x y args es ad i fa fi ps rs hargs hres hfi hty =>
    obtain ⟨cs, hA, hp⟩ := path_closedX hargs
    refine ⟨cs ++ [], answered_append hA answered_nil, ?_⟩
    rw [denListX_cons, denX_op]
    refine pendR_bind_left (pendR_thenK hp ?_)
    show Pend (run' (indEv x y f₁ _) ⟨s₁⟩) [] _
    rw [run_indEv_some ⟨ad, i, rfl, hres⟩]
    exact pend_callAt hfi hty
  | @callIndK s s₁ s₂ f f₁ f₂ stk stk₁ vs x y' args es ad i fa fi fn ps rs fl y hargs hres hfi hcode
      hty hbody hvs _ ih =>
    obtain ⟨cs₁, hA₁, hp₁⟩ := path_closedX hargs
    obtain ⟨cs₂, hA₂, hp₂⟩ := ih
    refine ⟨cs₁ ++ [⟨(fa, (stk₁.take ps.length).reverse, s₁), (s₂, fl)⟩] ++ cs₂,
      answered_append (answered_append hA₁
        (answered_single (closedCallX_of_body hfi hcode hty hbody))) hA₂, ?_⟩
    rw [denListX_cons, denX_op]
    refine pendR_thenK (path_thenK_normal hp₁ ?_) hp₂
    show Path (run' (indEv x y' f₁ _) ⟨s₁⟩) _ _
    rw [run_indEv_some ⟨ad, i, rfl, hres⟩]
    exact path_callAt hfi hty (s₂, fl) (path_callAns_vals hvs _)
  | @hereRef s s₁ f f₁ stk stk₁ y args es fa fi ps rs hargs hfi hty =>
    obtain ⟨cs, hA, hp⟩ := path_closedX hargs
    refine ⟨cs ++ [], answered_append hA answered_nil, ?_⟩
    rw [denListX_cons, denX_op]
    exact pendR_bind_left (pendR_thenK hp (pend_callAt hfi hty))
  | @callRefK s s₁ s₂ f f₁ f₂ stk stk₁ vs y' args es fa fi fn ps rs fl y hargs hfi hcode hty hbody
      hvs _ ih =>
    obtain ⟨cs₁, hA₁, hp₁⟩ := path_closedX hargs
    obtain ⟨cs₂, hA₂, hp₂⟩ := ih
    refine ⟨cs₁ ++ [⟨(fa, (stk₁.take ps.length).reverse, s₁), (s₂, fl)⟩] ++ cs₂,
      answered_append (answered_append hA₁
        (answered_single (closedCallX_of_body hfi hcode hty hbody))) hA₂, ?_⟩
    rw [denListX_cons, denX_op]
    exact pendR_thenK (path_thenK_normal hp₁
      (path_callAt hfi hty (s₂, fl) (path_callAns_vals hvs _))) hp₂
  | @hereTail s s₁ f f₁ stk stk₁ i args es fa fi ps rs hargs hres hfi hty =>
    obtain ⟨cs, hA, hp⟩ := path_closedX hargs
    refine ⟨cs ++ [], answered_append hA answered_nil, ?_⟩
    rw [denListX_cons, denX_op, opCX_tail (isXTail_of_tailRes hres)]
    refine pendR_bind_left (pendR_thenK hp ?_)
    rw [run_tailEv_some hres]
    exact pend_tailAt hfi hty

end Silmaril.Proofs.Wasm.Abstract.XDecomp
