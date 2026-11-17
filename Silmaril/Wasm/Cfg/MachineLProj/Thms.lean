module

public import Silmaril.Wasm.Cfg.BridgeCfg.Thms
public import Silmaril.Wasm.Cfg.MachineL.Thms
public import Silmaril.Wasm.Abstract.CallXP.Thms
public import Silmaril.Wasm.Abstract.CallXE.Thms
import Silmaril.Proofs.Wasm.Cfg.MachineLProj

@[expose] public section

/-!
# Run-level projection of the logged machine to `MStepC` (H1)

The logged machine `MStepL` (`MachineL`) runs straight-line code by `EvalLXPS`, with open logged
calls and native stack conventions. `MStepC` (`Machine`) runs it by Core region steps, with calls
answered by an oracle and Core's stack conventions. This header projects **whole runs**:

* **`project_sink_closedX`**: a logged run from the CFG entry to a sink (`exit`, `trap`, `raise`)
  is a run of `MStepC` (any profile, no host) from the CFG entry to a sink. Both machines end
  with the same native result: `EndRel` for the logged sink, and `ResOut`/`EndsC` for `MStepC`'s
  sink, so the store and frame are the same unless the end completes a pending tail call.

**This is a run-level corollary, not the stepwise (stuttering) projection.** It composes existing
results: `forward_sink`, `closed_iff_logged`, `CallXP.evalOXP_iff_evalOXE`,
`CallXE.evalOXE_iff_evalOX` and `Bridge.native_machine_closedX`. Its hypotheses are the fragment
those results share. They are stated, and none is claimed to be removable here:

* **The oracle.** Every logged entry is answered by `Machine.closedXOk` (`CloseOk closedXOk`).
  This is the typed closed extended oracle: `StoreChkE tExt` and `Interp.CX closedCallX`, a typed
  entry answered by the closed native semantics. **Host entries are never `CloseOk`**, so a log
  with a host call does not project: `MStepC` has no host answers to forget them into.
* **Call forms.** `xFreeL`: direct `call` only, with no `call_indirect`, `call_ref` or tail calls.
  On such code `EvalOXP` is `EvalOXE`, with no pending tail calls.
* **No exceptions.** `ehFreeL`: no `throw`, `throw_ref` or `try_table`. On such code `EvalOXE` is
  `EvalOX`.
* **Typing.** `Interp.TypedT` for the `tExt` checker, as `native_machine_closedX` needs.

On untyped code the two machines' stack conventions differ (`ExampleLogged`). The stepwise typed
projection, its exception bridge, and the discharge of `CloseOk` by the canonical host-closing
correspondence remain open (`docs/projects/wasm-cfg.md`).
-/

namespace Silmaril.Wasm.Cfg.MachineL

open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Machine Silmaril.Wasm.Cfg.Bridge
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Binaryen

variable {H : Type}

/-- **A logged run to a sink is an `MStepC` run to a sink with the same native result**: logs
answered by the typed closed extended oracle, typed code, direct calls only, no exceptions. -/
theorem project_sink_closedX (P : Numerics.Profile) {body : Expr} {s : Store H} {f : Frame}
    {l : List (Abstract.SCall H)} {st : MState H} (h : MRunL body (initial body s f) l st)
    (hs : st.node.IsSink) (hl : ∀ e ∈ l, CloseOk closedXOk e)
    (ht : Interp.TypedT s f [] (liftInstrs body))
    (hx : Abstract.CallX.xFreeL (liftInstrs body) = true)
    (he : Abstract.CallXE.ehFreeL (liftInstrs body) = true) :
    ∃ (s₂ : Store H) (f₂ : Frame) (fl : Flow) (s' : Store H) (f' : Frame) (o : Region.Out)
      (st' : MState H), EndRel st (s₂, f₂, .flow fl) ∧ ResOut closedXOk s' f' o (s₂, f₂, fl) ∧
      Relation.ReflTransGen (MStepC P Interp.noHostX closedXOk body) (initial body s f) st' ∧
      EndsC closedXOk st' s' f' o :=
  Proofs.MachineLProj.project_sink_closedX P h hs hl ht hx he

end Silmaril.Wasm.Cfg.MachineL
