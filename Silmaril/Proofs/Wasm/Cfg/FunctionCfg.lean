module

public import Silmaril.Wasm.Cfg.BridgeCfg.Thms
public import Silmaril.Wasm.Interp.XProgress.Thms
public import Silmaril.Wasm.Abstract.XRecursion.Thms
public import Silmaril.Proofs.Wasm.Cfg.BridgeBwdTree

@[expose] public section

/-!
# A defined function's CFG execution against its Core invocation (proofs)

For a typed invocation of a Wasm function in a `tExt`-checked store of Wasm functions, the
block-CFG machine on the function's body, in the function's call frame, with calls answered by
the typed closed extended oracle `CX closedCallX`, is the closed Core invocation in both
directions: `machine_core` (machine runs to sinks are invocation results) and `core_machine`
(stopping Core runs of the invocation are machine runs to sinks).
-/

namespace Silmaril.Wasm.Cfg.Proofs.FunctionCfg

open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Bridge Silmaril.Wasm.Cfg.Machine
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Binaryen Silmaril.Wasm.Interp
open Silmaril.Wasm.Abstract.XRecursion (closedCallX closedCallX_fixpoint)

variable {H : Type}

/-- The typed closed extended oracle. -/
abbrev Q : Abstract.CallRel H := CX (closedCallX : Abstract.CallRel H)

theorem args_length {s : Store H} {a : Nat} {vs : List Val} {fi : FuncInst H}
    {ps rs : List Validation.CValType} (hok : InvokeOk s a vs) (hfi : s.funcs[a]? = some fi)
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) : vs.length = ps.length := by
  obtain ⟨fi', ps', rs', hfi', he', hvs⟩ := hok
  rw [hfi] at hfi'; cases hfi'
  have hty' : Validation.DefType.funcType? fi.type = some (ps'.toList, rs'.toList) := by
    unfold Validation.DefType.funcType?; rw [Validation.Expand.iff.mp he']
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hty.symm.trans hty'))
  exact hvs.length_eq

/-- **Machine runs are invocation results**: a run of the machine on the body, in the call
frame, to a sink is a native body run whose flow is a closed outcome of the invocation, and
Core runs the invocation to the corresponding values or trap. -/
theorem machine_core {o : SingleThreaded.GrowOracle} {s : Store H} {a : Nat} {vs : List Val}
    {fi : FuncInst H} {fn : Func} {ps rs : List Validation.CValType} (hs : StoreOk s)
    (hok : InvokeOk s a vs) (hS : StoreChkE tExt s.funcs) (hW : WasmFuncsT s)
    (hfi : s.funcs[a]? = some fi) (hcode : fi.code = .wasm fn)
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) {st' : MState H}
    (hrun : Relation.ReflTransGen (MStepC (SingleThreaded.profile o) noHostX Q fn.body)
      (initial fn.body s (Frame.forCall fi.module vs fn.locals)) st')
    (hsink : st'.node.IsSink) :
    ∃ out s₂ f₂ r, EndsC Q st' s₂ f₂ out ∧ ResOut Q s₂ f₂ out r ∧
      Abstract.CallX.EvalOX Q s (Frame.forCall fi.module vs fn.locals) [] (liftInstrs fn.body) r ∧
      closedCallX s a vs (r.1, r.2.2) ∧
      (∀ ws, r.2.2.retVals = some ws → Steps (SingleThreaded.profile o) noHostX (invoke s a vs)
        ⟨r.1, {}, vals (ws.take rs.length).reverse⟩) ∧
      (r.2.2 = .trap → Steps (SingleThreaded.profile o) noHostX (invoke s a vs) ⟨r.1, {}, [.trap]⟩) := by
  have hE := entry_of_invokeOk (P := SingleThreaded.profile o) hs hok
  have ht := callee_typedT hS hE hfi hcode hty (args_length hok hfi hty)
  rw [← lowerList_liftInstrs fn.body] at hrun
  obtain ⟨out, s₂, f₂, r, hE', hr, hres⟩ := machine_native_typed
    (oracleSoundT_typedClosed (P := SingleThreaded.profile o)) keepsTy_CX ht hrun hsink
  have hcl : closedCallX s a vs (r.1, r.2.2) := by
    rw [closedCallX_fixpoint]
    exact ⟨fi, fn, ps, rs, r.2.1, hfi, hcode, hty, hr.mono (fun _ _ _ _ h => h.2)⟩
  obtain ⟨hv, htr⟩ := (XProgress.invoke_closedX_adequacy hs hok hS hW hfi hty).2.2 r.1 r.2.2 hcl
  exact ⟨out, s₂, f₂, r, hE', hres, hr, hcl, hv, htr⟩

/-- **Stopping invocations are machine runs**: a Core run of the invocation to a normal form is
terminal (values or a trap) and a closed outcome of the invocation, whose native body run is a
machine run on the body, in the call frame, from the CFG entry to a sink ending as that run. -/
theorem core_machine {o : SingleThreaded.GrowOracle} {s : Store H} {a : Nat} {vs : List Val}
    {fi : FuncInst H} {fn : Func} {ps rs : List Validation.CValType} (hs : StoreOk s)
    (hok : InvokeOk s a vs) (hS : StoreChkE tExt s.funcs) (hW : WasmFuncsT s)
    (hfi : s.funcs[a]? = some fi) (hcode : fi.code = .wasm fn)
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) {c' : Config H}
    (hrun : Steps (SingleThreaded.profile o) noHostX (invoke s a vs) c')
    (hnf : ∀ x, ¬ Step (SingleThreaded.profile o) noHostX c' x) :
    c'.Terminal ∧ ∃ (s₂ : Store H) (fl : Flow), closedCallX s a vs (s₂, fl) ∧
      ((∃ ws, fl.retVals = some ws ∧ c' = ⟨s₂, {}, vals (ws.take rs.length).reverse⟩) ∨
        (fl = .trap ∧ c' = ⟨s₂, {}, [.trap]⟩)) ∧
      ∃ (f₂ : Frame) (st' : MState H) (out : Region.Out) (s₃ : Store H) (f₃ : Frame),
        Abstract.CallX.EvalOX Q s (Frame.forCall fi.module vs fn.locals) [] (liftInstrs fn.body)
          (s₂, f₂, fl) ∧
        Relation.ReflTransGen (MStepC (SingleThreaded.profile o) noHostX Q fn.body)
          (initial fn.body s (Frame.forCall fi.module vs fn.locals)) st' ∧
        EndsC Q st' s₃ f₃ out ∧ ResOut Q s₃ f₃ out (s₂, f₂, fl) := by
  obtain ⟨hterm, s₂, fl, hcl, hc'⟩ :=
    (XProgress.invoke_closedX_adequacy hs hok hS hW hfi hty).2.1 c' hrun hnf
  refine ⟨hterm, s₂, fl, hcl, hc', ?_⟩
  have hn := args_length hok hfi hty
  have hE := entry_of_invokeOk (P := SingleThreaded.profile o) hs hok
  have ht := callee_typedT hS hE hfi hcode hty hn
  have hcl' := hcl
  rw [closedCallX_fixpoint] at hcl'
  obtain ⟨fi', fn', ps', rs', f₂, hfi', hcode', hty', hev⟩ := hcl'
  rw [hfi] at hfi'; cases hfi'
  rw [hcode] at hcode'; cases hcode'
  rw [hty] at hty'; obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hty')
  have hC := oracleSoundT_typedClosed (P := SingleThreaded.profile o) (H := H)
  have hevT := evalOXT_restrictT (P := SingleThreaded.profile o) hC keepsTy_closedCallX hev ht
  obtain ⟨ob, hb, -⟩ := endsAt_eq (hS a fi fn ps rs hfi hcode hty)
  have hlen : (Frame.forCall fi.module vs fn.locals).locals.length =
      ps.length + fn.locals.length := forCall_length _ _ hn
  have hchk : chkE tExt s.funcs (Frame.forCall fi.module vs fn.locals).module
      (Frame.forCall fi.module vs fn.locals).locals.length rs.length [rs.length] (some 0)
      (liftInstrs fn.body) = some ob := by rw [hlen]; exact hb
  obtain ⟨s₃, f₃, out, hres, hm⟩ := native_machine hC (SingleThreaded.profile o) noHostX hevT hS hchk
  rcases hm with ⟨k, us, hk, rfl⟩ | ⟨st', hrun', hE'⟩
  · exfalso
    obtain ⟨vs', junk, he, -⟩ := Proofs.Bridge.resOut_br_inv hres
    simp only [Prod.mk.injEq] at he
    obtain ⟨-, -, rfl⟩ := he
    obtain ⟨hok', -⟩ := Proofs.Bridge.arityG hC hevT hS hchk
    obtain ⟨m, hm, -⟩ := hok'
    rcases k with _ | k
    · exact hk rfl
    · simp at hm
  · rw [lowerList_liftInstrs] at hrun'
    exact ⟨f₂, st', out, s₃, f₃, hevT.forget, hrun', hE', hres⟩

end Silmaril.Wasm.Cfg.Proofs.FunctionCfg
