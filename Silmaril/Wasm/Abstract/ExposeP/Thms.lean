module

public import Silmaril.Wasm.Abstract.ExposeP.Defs
public import Silmaril.Wasm.Abstract.BodyTrace.Defs
import Silmaril.Proofs.Wasm.Abstract.ExposeP.Frame
import Silmaril.Proofs.Wasm.Abstract.ExposeP.Legacy

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
  answered by `C`, ending in its result (`endRP`: a pending tail call is a returned value);
* `path_evalOXP`: conversely, every finished answered path is an `EvalOXP C` derivation;
* so `evalOXP_iff` (non-trap results, pending tail calls included) and `evalOXP_trap_iff`;
* the frame: `bodyCallXP_path`, `path_bodyCallXP`, and so `bodyCallXP_iff` and
  `bodyCallXP_trap_iff`: `CallXP.bodyCallXP C` is exactly the finished answered paths of
  `frameXP`, whose events are the body's and then the pending tail call's, made at the frame;
* `denListXP_eq_liftP`: on code without the extended call forms (`CallX.xFreeL`) the body is
  `ExposeE.denListXE`'s, its flows read as body results (`liftP`), as
  `CallXP.evalOXP_iff_evalOXE` says of the relations.

A trap is the trap effect of the monad, so it forgets its store (`endRP`, `endF`), as in
`ExposeE.evalOXE_trap_iff`.
-/

public section

namespace Silmaril.Wasm.Abstract.ExposeP

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Abstract (CallRel)
open Silmaril.Wasm.Abstract.StoreBody Silmaril.Wasm.Abstract.StoreCall
open Silmaril.Wasm.Abstract.CallX Silmaril.Wasm.Abstract.CallXP Silmaril.Wasm.Abstract.ExposeE
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

/-- **The converse.** Every finished path of the exposed body whose call events are answered
by `C` is an `EvalOXP C` derivation, ending as the path does. -/
theorem path_evalOXP {C : CallRel H} {s : Store H} {f : Frame} {stk : List Val}
    {es : List BExpr} {cs : List (Call (CallSig H))}
    {e : PathEnd (Except PUnit.{2} (ResP × St H))} (hA : Answered C cs)
    (h : Path (((denListXP es f stk : M (CallSig H) H ResP).run ⟨s⟩).run) cs e) (he : e ≠ .div) :
    ∃ r, EvalOXP C s f stk es r ∧ endRP r = e :=
  Silmaril.Proofs.Wasm.Abstract.ExposeP.list_ansXP es s f stk cs e hA h he

/-- **Exposure is exact (values).** An `EvalOXP C` result that is not a trap (a flow, exceptions
included, or a pending tail call) is exactly a finished answered path of the exposed body with
that store, frame and result. -/
theorem evalOXP_iff {C : CallRel H} {s : Store H} {f : Frame} {stk : List Val}
    {es : List BExpr} {s' : Store H} {f' : Frame} {o : POut} (ho : o ≠ .flow .trap) :
    EvalOXP C s f stk es (s', f', o) ↔
      ∃ cs, Answered C cs ∧ Path (((denListXP es f stk : M (CallSig H) H ResP).run ⟨s⟩).run) cs
        (.val (.ok (⟨(f', o)⟩, ⟨s'⟩))) :=
  Silmaril.Proofs.Wasm.Abstract.ExposeP.evalOXP_iff ho

/-- **Exposure is exact (traps).** `EvalOXP C` traps exactly when the exposed body has a
finished answered path to the trap. -/
theorem evalOXP_trap_iff {C : CallRel H} {s : Store H} {f : Frame} {stk : List Val}
    {es : List BExpr} :
    (∃ s' f', EvalOXP C s f stk es (s', f', .flow .trap)) ↔
      ∃ cs, Answered C cs ∧ Path (((denListXP es f stk : M (CallSig H) H ResP).run ⟨s⟩).run) cs
        (.val (.error ⟨⟩)) :=
  Silmaril.Proofs.Wasm.Abstract.ExposeP.evalOXP_trap_iff

/-- **The frame, exposed.** Every `bodyCallXP C` outcome is a path of the exposed frame with every
call event answered by `C`: the body's call events, then the pending tail call's, if any. -/
theorem bodyCallXP_path {C : CallRel H} {s : Store H} {a : Nat} {args : List Val}
    {out : Store H × Flow} (h : bodyCallXP C s a args out) :
    ∃ cs, Answered C cs ∧
      Path (((frameXP a args : M (CallSig H) H (ULift.{1} Flow)).run ⟨s⟩).run) cs (endF out) :=
  Silmaril.Proofs.Wasm.Abstract.ExposeP.bodyCallXP_path h

/-- **The frame, the converse.** Every finished answered path of the exposed frame is a
`bodyCallXP C` outcome, ending as the path does. -/
theorem path_bodyCallXP {C : CallRel H} {s : Store H} {a : Nat} {args : List Val}
    {cs : List (Call (CallSig H))} {e : PathEnd (Except PUnit.{2} (ULift.{1} Flow × St H))}
    (hA : Answered C cs)
    (h : Path (((frameXP a args : M (CallSig H) H (ULift.{1} Flow)).run ⟨s⟩).run) cs e)
    (he : e ≠ .div) : ∃ out, bodyCallXP C s a args out ∧ endF out = e :=
  Silmaril.Proofs.Wasm.Abstract.ExposeP.path_bodyCallXP hA h he

/-- **The frame is exact (values).** A non-trap frame outcome `(s', fl)` of `bodyCallXP C` is
exactly a finished answered path of `frameXP` ending in that store and flow. -/
theorem bodyCallXP_iff {C : CallRel H} {s : Store H} {a : Nat} {args : List Val} {s' : Store H}
    {fl : Flow} (hfl : fl ≠ .trap) :
    bodyCallXP C s a args (s', fl) ↔
      ∃ cs, Answered C cs ∧
        Path (((frameXP a args : M (CallSig H) H (ULift.{1} Flow)).run ⟨s⟩).run) cs
          (.val (.ok (⟨fl⟩, ⟨s'⟩))) :=
  Silmaril.Proofs.Wasm.Abstract.ExposeP.bodyCallXP_iff hfl

/-- **The frame is exact (traps).** `bodyCallXP C` traps exactly when `frameXP` has a finished
answered path to the trap. -/
theorem bodyCallXP_trap_iff {C : CallRel H} {s : Store H} {a : Nat} {args : List Val} :
    (∃ s', bodyCallXP C s a args (s', .trap)) ↔
      ∃ cs, Answered C cs ∧
        Path (((frameXP a args : M (CallSig H) H (ULift.{1} Flow)).run ⟨s⟩).run) cs
          (.val (.error ⟨⟩)) :=
  Silmaril.Proofs.Wasm.Abstract.ExposeP.bodyCallXP_trap_iff

/-- **Legacy coincidence.** On code without the extended call forms, the exposed body with pending
tail calls is `ExposeE`'s, read with body results. -/
theorem denListXP_eq_liftP {es : List BExpr} (h : xFreeL es = true) (f : Frame)
    (stk : List Val) :
    (denListXP (H := H) es f stk : M (CallSig H) H ResP) = liftP (denListXE es f stk) :=
  congrFun (congrFun (Silmaril.Proofs.Wasm.Abstract.ExposeP.denListXP_eq_liftP es h) f) stk

end Silmaril.Wasm.Abstract.ExposeP
