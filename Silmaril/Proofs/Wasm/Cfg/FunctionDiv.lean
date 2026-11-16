module

public import Silmaril.Wasm.Cfg.FunctionCfg.Defs
public import Silmaril.Wasm.Cfg.MachineClosedX.Thms
public import Silmaril.Proofs.Wasm.Cfg.Restrict
public import Silmaril.Proofs.Wasm.Cfg.MachineTailDiv
public import Silmaril.Proofs.Wasm.Cfg.CallTransport
public import Silmaril.Proofs.Wasm.Cfg.CallClosedX
public import Silmaril.Wasm.Abstract.XRecursion.Thms
public import Silmaril.Proofs.Wasm.Cfg.FunctionCfg

@[expose] public section

/-!
# Function-level divergence of the CFG machine (proofs): soundness

On a `tExt`-checked store with no host, the store's function list never changes along a run
(`Proofs.Region.mdivT_funcs`, from `steps_funcs_closed` and `closedCallX_funcs`), so every call
the machine with `CX closedCallX` makes is from a `tExt`-checked store: the machine is the one
with `closedXOk`, which is Core-sound (`callSoundA_closedXOk`). The callees `calleeDivX o` names
diverge from every caller frame and annotation (`div_call_transport`). So machine frame
divergence `MDivT` on the body, in the call frame, is Core 3.0 divergence of the function's
frame, which the invocation reaches in one step (`call_ref-func`).
-/

namespace Silmaril.Wasm.Cfg.Proofs.FunctionDiv

open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Machine Silmaril.Wasm.Cfg.Function
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Binaryen Silmaril.Wasm.Interp
  Silmaril.Wasm.Validation
open Silmaril.Wasm.Abstract.XRecursion (closedCallX closedCallX_funcs)

variable {H : Type}

/-- On a store with a `tExt`-checked function list `F`, the typed closed extended oracle answers
as `closedXOk` and keeps `F`. -/
theorem cx_closedXOk {F : List (FuncInst H)} (hF : StoreChkE tExt F) :
    ∀ s a us out, s.funcs = F → CX (closedCallX : Abstract.CallRel H) s a us out →
      closedXOk s a us out ∧ out.1.funcs = F :=
  fun _ _ _ _ hs h => ⟨⟨hs ▸ hF, h⟩, (closedCallX_funcs h.2).trans hs⟩

/-- **The callees `calleeDivX` names diverge from every frame and annotation.** -/
theorem divCallSound_calleeDivX (o : SingleThreaded.GrowOracle) :
    Region.DivCallSound (SingleThreaded.profile o) noHostX (calleeDivX (H := H) o) := by
  intro s f a fi ps rs us c hc hfi hty hn hd
  obtain ⟨-, -, -, hW, hdiv⟩ := hd
  have hw : Proofs.Region.WasmFuncs s := by
    intro g hg
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hg
    obtain ⟨fn, -, -, hcode, -⟩ := hW i _ (List.getElem?_eq_getElem hi)
    exact ⟨fn, hcode⟩
  have he := Proofs.Region.expand_of_funcType hty
  have hinv : invoke s a us = ⟨s, {}, vals us ++ [.ref (.func a), .callRefType fi.type]⟩ := by
    simp [invoke, hfi]
  rw [hinv] at hdiv
  exact Proofs.Region.div_call_transport (cr := .callRefType fi.type) hw trivial hfi he (by simp [Ty.length_ofList, hn]) hdiv f hc

/-- **Soundness of function-level divergence**: on the stated fragment, machine frame divergence
`MDivT` with `CX closedCallX` and `calleeDivX o`, on the body in the call frame, is Core 3.0
divergence of the invocation. -/
theorem invoke_diverges_of_mdivT {o : SingleThreaded.GrowOracle} {s : Store H} {a : Nat}
    {vs : List Val} {fi : FuncInst H} {fn : Func} {ps rs : List CValType}
    (hok : InvokeOk s a vs) (hS : StoreChkE tExt s.funcs) (hfi : s.funcs[a]? = some fi)
    (hcode : fi.code = .wasm fn) (hty : DefType.funcType? fi.type = some (ps, rs))
    (h : MDivT (SingleThreaded.profile o) noHostX (CX (closedCallX : Abstract.CallRel H))
      (calleeDivX o) fn.body (initial fn.body s (Frame.forCall fi.module vs fn.locals))) :
    Diverges (SingleThreaded.profile o) noHostX (invoke s a vs) := by
  have h' := Proofs.Region.mdivT_funcs (cx_closedXOk hS) h rfl
  have hdiv := Proofs.MachineTailDiv.mdivT_frame_initial
    (Proofs.Region.callSoundA_closedXOk (SingleThreaded.profile o)) (divCallSound_calleeDivX o) h'
    (Ty.ofList rs).length {}
  have he := Proofs.Region.expand_of_funcType hty
  have hn : vs.length = (Ty.ofList ps).length := by
    rw [Ty.length_ofList]; exact Proofs.FunctionCfg.args_length hok hfi hty
  have hstep : Step (SingleThreaded.profile o) noHostX (invoke s a vs)
      ⟨s, {}, [.frame (Ty.ofList rs).length (Frame.forCall fi.module vs fn.locals)
        [.label (Ty.ofList rs).length [] (expression fn.body)]]⟩ := by
    have := Step.callRefFunc (P := SingleThreaded.profile o) (host := noHostX) (s := s) (f := {})
      (c := .callRefType fi.type) trivial hfi he hn hcode
    simpa [invoke, hfi] using this
  exact InfiniteTrace.fold hstep hdiv

end Silmaril.Wasm.Cfg.Proofs.FunctionDiv
