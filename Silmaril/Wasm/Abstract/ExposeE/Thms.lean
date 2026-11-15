module

public import Silmaril.Wasm.Abstract.ExposeE.Defs
public import Silmaril.Wasm.Abstract.BodyTrace.Defs
import Silmaril.Proofs.Wasm.Abstract.ExposeE.Answer

/-!
# The exposed body of the relation with exceptions: theorems

`denListXE` (Defs) is the exposed `BodyM` body of `CallXE.EvalOXE`: `CallX`'s exposed body
`denListX` (every call form a call event of `StoreCall.CallSig`), with the exception forms.

* **Exceptions are values.** A thrown exception is a result `⟨(f, .throw a)⟩` of the body,
  `a` its address in the store, not an effect of the monad; it passes through sequencing,
  blocks, loops and conditionals as every non-normal flow does. `throw x` allocates it with
  its tag's fields (`resolveThrow`, `throwEv`); `throw_ref` traps on null and rethrows a
  reference (`throwRefEv`).
* **Handlers.** `try_table bt cs body` runs its body as a block; a thrown exception is resolved
  by the first-match handler resolution `Cfg.Region.Catches` (`resolveCatch`, `tryK`): a match
  is a branch from outside the block with the clause's values, no match rethrows.

Exactness:

* `evalOXE_path`: every `EvalOXE C` derivation is a path of `denListXE` with every call event
  answered by `C`, ending as the derivation does;
* `path_evalOXE`: conversely, every finished answered path is an `EvalOXE C` derivation;
* so `evalOXE_iff` (non-trap outcomes) and `evalOXE_trap_iff` (traps);
* `denListXE_eq_denListX`: on exception-free code (`ehFreeL`) the body is `CallX`'s.

**Caveat: tail calls inside handlers.** This exposure is exact for `CallXE.EvalOXE`, whose `tail`
rule answers a tail call where it is made, so under a `try_table` a tail callee's exception is
caught. Core 3.0 leaves the handler first (`return_call_ref-handler`). The faithful semantics is
`Silmaril.Wasm.Abstract.CallXP` (pending tail calls, answered when the frame is left), which agrees
with `EvalOXE` on code without the extended call forms (`CallXP.evalOXP_iff_evalOXE`). This
exposure is not the general functor's denotation; a pending-tail exposure is to follow.

**Status: legacy, restricted scope.** The canonical F5 semantics is `Abstract.CallXP` (pending
tail calls answered only at the frame, faithful under handlers), with closure
`Abstract.XRecursionP.closedCallXP`, Core adequacy `Interp.PendSim` and exact BodyM denotation
`Abstract.ExposeP`. The statements here are for code without the extended call forms (`xFreeL`),
where `CallXP.evalOXP_iff_evalOXE` makes them coincide with the canonical ones; they are not the
factory default for code with tail calls.
-/

public section

namespace Silmaril.Wasm.Abstract.ExposeE

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Abstract (CallRel)
open Silmaril.Wasm.Abstract.StoreBody Silmaril.Wasm.Abstract.StoreCall
open Silmaril.Wasm.Abstract.CallX Silmaril.Wasm.Abstract.CallXE
open Silmaril.Wasm.Abstract.BodyTrace (Path PathEnd)
open Silmaril.Games.Abstract (Call)

variable {H : Type}

/-- **Exposure of the relation with exceptions.** Every `EvalOXE C` derivation is a path of
the exposed body with every call event answered by `C`. -/
theorem evalOXE_path {C : CallRel H} {s : Store H} {f : Frame} {stk : List Val}
    {es : List BExpr} {r : Store H × Frame × Flow} (h : EvalOXE C s f stk es r) :
    ∃ cs, Answered C cs ∧
      Path (((denListXE es f stk : M (CallSig H) H Res).run ⟨s⟩).run) cs (endR r) :=
  Silmaril.Proofs.Wasm.Abstract.ExposeE.evalOXE_path h

/-- **On exception-free code the exposed body is `CallX`'s.** -/
theorem denListXE_eq_denListX {es : List BExpr} (h : ehFreeL es = true) :
    (denListXE (H := H) es : Frame → List Val → M (CallSig H) H Res) = denListX es :=
  Silmaril.Proofs.Wasm.Abstract.ExposeE.denListXE_eq_denListX es h

/-- **The converse.** Every finished path of the exposed body whose call events are answered
by `C` is an `EvalOXE C` derivation, ending as the path does. -/
theorem path_evalOXE {C : CallRel H} {s : Store H} {f : Frame} {stk : List Val}
    {es : List BExpr} {cs : List (Call (CallSig H))}
    {e : PathEnd (Except PUnit.{2} (Res × St H))} (hA : Answered C cs)
    (h : Path (((denListXE es f stk : M (CallSig H) H Res).run ⟨s⟩).run) cs e) (he : e ≠ .div) :
    ∃ r, EvalOXE C s f stk es r ∧ endR r = e :=
  Silmaril.Proofs.Wasm.Abstract.ExposeE.list_ansXE es s f stk cs e hA h he

/-- **Exposure is exact (values).** An `EvalOXE C` outcome that is not a trap (exceptions
included) is exactly a finished answered path of the exposed body with that store, frame and
flow. -/
theorem evalOXE_iff {C : CallRel H} {s : Store H} {f : Frame} {stk : List Val}
    {es : List BExpr} {s' : Store H} {f' : Frame} {fl : Flow} (hfl : fl ≠ .trap) :
    EvalOXE C s f stk es (s', f', fl) ↔
      ∃ cs, Answered C cs ∧ Path (((denListXE es f stk : M (CallSig H) H Res).run ⟨s⟩).run) cs
        (.val (.ok (⟨(f', fl)⟩, ⟨s'⟩))) :=
  Silmaril.Proofs.Wasm.Abstract.ExposeE.evalOXE_iff hfl

/-- **Exposure is exact (traps).** `EvalOXE C` traps exactly when the exposed body has a
finished answered path to the trap. -/
theorem evalOXE_trap_iff {C : CallRel H} {s : Store H} {f : Frame} {stk : List Val}
    {es : List BExpr} :
    (∃ s' f', EvalOXE C s f stk es (s', f', .trap)) ↔
      ∃ cs, Answered C cs ∧ Path (((denListXE es f stk : M (CallSig H) H Res).run ⟨s⟩).run) cs
        (.val (.error ⟨⟩)) :=
  Silmaril.Proofs.Wasm.Abstract.ExposeE.evalOXE_trap_iff

end Silmaril.Wasm.Abstract.ExposeE
