module

public import Silmaril.Wasm.Execution.Core.Intrinsic.Call.Defs
public import Silmaril.Wasm.Execution.Core.Instantiation
import Silmaril.Proofs.Wasm.Execution.Core.Intrinsic.Call

public section

namespace Silmaril.Wasm.Execution.Core.Intrinsic

open Validation Numerics

variable {H : Type} {context : Context} {caller : World H context}
  {parameters results locals : List IntType} {profile : Profile} {host : HostSemantics H}

/-- Resolve the `call` then enter the real Core frame and label. -/
theorem DirectCall.entry (call : DirectCall caller parameters results) (frame : LocalFrame caller locals)
    (args : Values parameters) :
    Steps profile host (call.source frame args) (call.suspend frame (call.start args).erase) :=
  Proofs.Wasm.Execution.Core.Intrinsic.Call.entry call frame args

/-- A terminating typed callee produces exactly the values or trap of a Core
reduction, with the identical store and the caller frame restored. -/
theorem DirectCall.run_sound (call : DirectCall caller parameters results) (frame : LocalFrame caller locals)
    (args : Values parameters) (fuel : Nat) {answer : Option (Values results)}
    (returned : call.runFor args fuel = some answer) :
    Steps profile host (call.source frame args)
      ⟨caller.store, frame.erase, (match answer with
        | some values => vals values.erase.reverse
        | none => [.trap])⟩ :=
  Proofs.Wasm.Execution.Core.Intrinsic.Call.run_sound call frame args fuel returned

theorem DirectCall.invoke_sound (call : DirectCall caller parameters results) (args : Values parameters)
    (fuel : Nat) {answer : Option (Values results)} (returned : call.runFor args fuel = some answer) :
    Steps profile host (invoke caller.store call.address args.erase)
      ⟨caller.store, {}, (match answer with
        | some values => vals values.erase.reverse
        | none => [.trap])⟩ :=
  Proofs.Wasm.Execution.Core.Intrinsic.Call.invoke_sound call args fuel returned

end Silmaril.Wasm.Execution.Core.Intrinsic
