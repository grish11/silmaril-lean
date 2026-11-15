module

public import Silmaril.Wasm.Abstract.HostCall.Defs
import Silmaril.Proofs.Wasm.Abstract.HostCall.Basic

/-!
# Core 3.0 host calls as a relational host: theorems (stage H2, first step)

The single Core step of a host call, read through `coreHostRel`. For any
caller frame, every profile and every host:

* `coreHost_answer_step`: an allowed answer `(s', r)` is the Core step
  `Step.callRefHost` from `vals us ++ [ref.func a, call_ref]` to `r`, with the
  store `s'` the host left;
* `coreHost_diverge`: allowed host divergence makes that configuration diverge
  in Core (`Step.callRefHostDiv` stutters forever);
* `coreHost_functional_iff`: the relational host is functional exactly when
  the Core host semantics is deterministic. Only then does `hostObs_unique`
  apply.

**Not yet proved.** A call the host has no outcome for is stuck in Core: no
host rule applies. That needs the Core inversion of `call_ref` on a host
function. Also not yet proved: the native relation with a host-call log, and
its forward and backward simulation through these steps.
-/

public section

namespace Silmaril.Wasm.Abstract

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation

variable {H : Type} {P : Silmaril.Wasm.Numerics.Profile} {host : HostSemantics H}

/-- **An allowed host answer is one Core step**, any frame. -/
theorem coreHost_answer_step {s s' : Store H} {f : Frame} {a : Nat} {fi : FuncInst H}
    {ps rs : Ty (.list .val)} {h : H} {us : List Val} {r : Result}
    (hf : s.funcs[a]? = some fi) (he : Expand fi.type (.func ps rs)) (hn : us.length = ps.length)
    (hcode : fi.code = .host h) (hans : coreHostRel host ⟨h, s, us⟩ (.answer (s', r))) :
    Step P host ⟨s, f, vals us ++ [.ref (.func a), .callRefType fi.type]⟩ ⟨s', f, r.toAdmin⟩ :=
  Silmaril.Proofs.Wasm.Abstract.HostCall.answer_step hf he hn hcode hans

/-- **Allowed host divergence is Core divergence**, any frame. -/
theorem coreHost_diverge {s : Store H} {f : Frame} {a : Nat} {fi : FuncInst H}
    {ps rs : Ty (.list .val)} {h : H} {us : List Val}
    (hf : s.funcs[a]? = some fi) (he : Expand fi.type (.func ps rs)) (hn : us.length = ps.length)
    (hcode : fi.code = .host h) (hdiv : coreHostRel host ⟨h, s, us⟩ .diverge) :
    Diverges P host ⟨s, f, vals us ++ [.ref (.func a), .callRefType fi.type]⟩ :=
  Silmaril.Proofs.Wasm.Abstract.HostCall.diverge_diverges hf he hn hcode hdiv

/-- The relational host is functional exactly when the host semantics is deterministic. -/
theorem coreHost_functional_iff :
    (coreHostRel host).Functional ↔
      ∀ h s vs (o o' : HostOutcome H), host h s vs o → host h s vs o' → o = o' :=
  Silmaril.Proofs.Wasm.Abstract.HostCall.functional_iff

end Silmaril.Wasm.Abstract
