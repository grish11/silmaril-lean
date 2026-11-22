module

public import Silmaril.Wasm.Component.Reference.DirectLift.Defs
import Silmaril.Proofs.Wasm.Component.Reference.DirectLift.Readback

public section

namespace Silmaril.Wasm.Component.Reference.DirectLift

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game Silmaril.Wasm.SingleThreaded
open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Wasm.Numerics (Profile)

/-- Read back a stock terminal call of a named direct canonical lift from the
existing one-owner `readyCfg` frame. Both machines use the same current Core
store (renaming the host-code type for the scalar game). The owner must have a
reusable thread slot, the call id must be fresh, and the lift must use default
options. This applies to an already linked Core store with no host imports; it
does not require `Simple.toRef`, a particular Core module layout, or an
instantiation trace. The final Core store is retained even on a trap. -/
theorem terminalReadback {P : Profile} {I : ScalarInstance} {shared : Store (CanonHost (core3P P))}
    {x : SimpleExport} {args : List Silmaril.Wasm.Component.Val} {question : I.F.Op}
    {prof : ProfileKind} {ι : InstState} {garbage : Garb P} {call : Nat}
    {funcs : List (CFuncInst (core3P P))} {exports : List (String × FuncId)}
    {final : Machine.Config (core3P P) Unit} {out : CallOutcome}
    (abi : Boundary I shared x args question) (threads : ThreadsOk ι) (fresh : garbage.Fresh call)
    (named : ∃ func, exports.lookup x.name = some func ∧
      funcs[func.idx]? = some (.lifted (I.addr question.1) (liftedFt x) {} ⟨0⟩) ∧
      Calls prof (refHost P).hr (D P) (readyCfg shared ι funcs garbage) ⟨call⟩ func
        (args.map toRefVal) final out) :
    ∃ (core : Execution.Core.Config Nat) (result : Result) (answer : I.F.Ar question),
      Entry.Finishes P Det.noHost
        (invoke (Store.mapH (fun _ => 0) shared) (I.addr question.1) question.2.val) core result ∧
      answer.toResult = result ∧ Reports x out result ∧
      core.store = Store.mapH (fun _ => 0) final.store.core ∧
      I.Activation P (Store.mapH (fun _ => 0) shared)
        [.inr (.ask question), .inr (.ans question answer)] core.store :=
  Silmaril.Proofs.Wasm.Component.Reference.DirectLift.terminalReadback abi threads fresh named

end Silmaril.Wasm.Component.Reference.DirectLift
