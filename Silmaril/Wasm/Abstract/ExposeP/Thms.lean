module

public import Silmaril.Wasm.Abstract.ExposeP.Defs
public import Silmaril.Wasm.Abstract.BodyTrace.Defs
import Silmaril.Proofs.Wasm.Abstract.ExposeP.Expose

/-!
# The exposed body of the relation with pending tail calls: theorems

`denListXP` (Defs) is the exposed `BodyM` body of `CallXP.EvalOXP`.

* **A tail call is a pending result.** `return_call`, `return_call_indirect` and
  `return_call_ref` resolve and type their callee and return `⟨(f, .tail fa args n)⟩`: no call
  event is made in the body. The pending call passes every label (`blockKP`, `loopKP`, `if`) and
  every handler (`tryKP` resolves only a thrown exception), as Core 3.0's
  `return_call_ref-label` and `return_call_ref-handler`.
* **The frame makes it.** `frameXP` runs a callee body and, on a pending tail call, makes its call
  event only then, ending as the callee does (`frameAns`), as `return_call_ref-frame-addr`.

Exactness:

* `evalOXP_path`: every `EvalOXP C` derivation is a path of `denListXP` with every call event
  answered by `C`, ending as the derivation does.
-/

public section

namespace Silmaril.Wasm.Abstract.ExposeP

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Abstract (CallRel)
open Silmaril.Wasm.Abstract.StoreBody Silmaril.Wasm.Abstract.StoreCall
open Silmaril.Wasm.Abstract.CallX Silmaril.Wasm.Abstract.CallXP
open Silmaril.Wasm.Abstract.BodyTrace (Path PathEnd)
open Silmaril.Games.Abstract (Call)

variable {H : Type}

/-- **Exposure of the relation with pending tail calls.** Every `EvalOXP C` derivation is a path
of the exposed body with every call event answered by `C`, ending in its result (a pending tail
call as a value). -/
theorem evalOXP_path {C : CallRel H} {s : Store H} {f : Frame} {stk : List Val}
    {es : List BExpr} {r : Store H × Frame × POut} (h : EvalOXP C s f stk es r) :
    ∃ cs, Answered C cs ∧
      Path (((denListXP es f stk : M (CallSig H) H ResP).run ⟨s⟩).run) cs (endRP r) :=
  Silmaril.Proofs.Wasm.Abstract.ExposeP.evalOXP_path h

end Silmaril.Wasm.Abstract.ExposeP
