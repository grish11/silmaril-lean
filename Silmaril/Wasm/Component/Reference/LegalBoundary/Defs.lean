module

public import Silmaril.Wasm.Component.Reference.Defs
public import Silmaril.Wasm.Component.Reference.Core3Sem.Defs

/-!
# The reference boundary of a canon call: exceptions become traps (definitions)

**Scope.** The concrete Core 3.0 engine of the reference machine at an arbitrary profile,
`core3P P`, and the reference machine `Machine.Step` over any engine. This topic states, on the
reference side, what the IR's legal node semantics (`Silmaril.Wasm.Cfg.CfgLegalComp`,
`Silmaril.Wasm.Cfg.CfgLegalOwner`) assumes: **no Core exception crosses a canon call
boundary**. An exception escaping the outermost activation of a canon call is a trap (REF
`call_and_trap_on_throw`, `definitions.py` L2161 at component-model `a25fc0b`).

Where the erasure happens. The reference machine sees a core activation only through the
engine's `status` and resumes it only with an engine `CallResult` (values or a trap; there is
no exception constructor). For `core3P P` the status is `flatStatus (Game.statusP P s t)`, and
`statusP` reports the code `throwing a` (an uncaught exception at the top of the activation) as
`.returned .trap`, the branch it also takes for `[.trap]`. So the exception-to-trap erasure
happens **at the engine/interface boundary**, inside `status`, before the machine looks at the
activation. Handlers inside the activation are unaffected: only code that *is* `throwing a`
(an exception that escaped every handler of the activation) is a boundary result; code with a
pending handler is still running.

Definitions:

* `callAndTrapOnThrow r`: REF `call_and_trap_on_throw` on a raw Core result `r` (values, a trap,
  or an uncaught exception `throw a`): exceptions become traps;
* `crPayload cr`: the IR payload of a boundary result, read as the IR's `answerPayload` reads
  an answer (flat values, or `none` for a trap);
* `statusPayload st`: the IR payload of a reference engine status (returned flat values; any
  other status is `none`);
* `coreCfg m th ct k segs rest`: `m` whose running activation is the core activation `ct` with
  continuation `k`, pending segments `segs` (for an exporter called through a cross-instance
  trampoline these contain the importer's parked core activation) and suspended resumers
  `rest`.

The theorems (`LegalBoundary.Thms`) prove the exact `core3P` status of every raw Core result,
the step-level indistinguishability of an escaped exception from a trap on the reference
machine (same label, including the trap reason `coreTrap`; same successor `trapCfg m`, with
the same core store and `lockdown`), its consequences for runs, top-level calls and resumable
sessions, the agreement of the reference boundary map with the IR's `answerPayload` and
`payloadAnswer`, and the legal injections of `CfgLegalOwner` for `Linked2` and `LinkedG`.

**Not claimed.** A richer interface in which a raw Core exception crosses a component boundary
(an `ssig` with an exception answer) is a different interface. It is not the reference
interface, and nothing here is a statement about it.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Reference.LegalBoundary

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Machine

/-- **REF `call_and_trap_on_throw`** on a raw Core result: values stay values, a trap stays a
trap, and an uncaught exception becomes a trap. -/
def callAndTrapOnThrow :
    Silmaril.Wasm.Execution.Core.Result → Silmaril.Wasm.SingleThreaded.CallResult
  | .values vs => .values vs
  | .trap => .trap
  | .throw _ => .trap

/-- The IR payload of a boundary result, as `answerPayload` reads an answer: flat values, or
`none` for a trap (and for values that are not flat). -/
def crPayload : Silmaril.Wasm.SingleThreaded.CallResult → Option Payload
  | .values vs => (vs.mapM Silmaril.Wasm.SingleThreaded.toFlat?).map .flat
  | .trap => none

/-- The IR payload of a reference engine status: returned flat values; any other status (a
trap, a callout, running, stuck) is `none`. -/
def statusPayload {H : Type} : Status H → Option Payload
  | .returned (.values vs) => some (.flat vs)
  | _ => none

variable {E : CoreEngine} {σ : Type}

/-- `m` with the core activation `ct` (continuation `k`, pending segments `segs`) running on
top of the suspended resumers `rest`. -/
def coreCfg (m : Config E σ) (th : Option Runtime.ThreadId) (ct : E.Thread (Runtime.CanonHost E))
    (k : List FlatValue → Canon.P E σ (Canon.Ret E)) (segs : List (Seg E σ))
    (rest : List (Activation E σ)) : Config E σ :=
  { m with ctl := ⟨th, .core ct k, segs⟩ :: rest }

end Silmaril.Wasm.Component.Reference.LegalBoundary
