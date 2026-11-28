module

public import Silmaril.Wasm.Component.Reference.Litmus.Defs
import Silmaril.Proofs.Wasm.Component.Reference.SyncImportRunLitmus
import Silmaril.Proofs.Wasm.Component.Reference.LitmusSeqI

public section

namespace Silmaril.Wasm.Component.Reference.SyncImportRun.Fixture

open Silmaril.Wasm.Component.Reference Silmaril.Wasm.Component.Reference.Litmus
open Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.Runtime
open Silmaril.Wasm.SingleThreaded (neverFail profile)

/-- The stock relational machine instantiates `fwdS`, then `f(3)` returns `13`
with the counter host moving from `10` to `11`. -/
theorem fwd_reference_calls :
    let h := answerHostS (profile neverFail) fwdC
    ∃ ready finished exports f,
      Instantiates .deterministic h.hr h.dispatch
        (Config.init (hostFuncs 0 fwdS.imports CStore.empty) 10)
        fwdS.toRef (importArgs fwdS.imports) ready ⟨0⟩ exports ∧
      exports.lookup "f" = some f ∧
      Calls .deterministic h.hr h.dispatch ready ⟨0⟩ f [toRefVal (.u32 3)] finished
        (.resolved (some [toRefVal (.u32 13)])) ∧ finished.host = 11 :=
  Silmaril.Proofs.Wasm.Component.Reference.Litmus.fwd_reference_calls

/-- The litmus counter host returns typed results. -/
theorem fwdC_ok : fwdS.HostOkS fwdC := Silmaril.Proofs.Wasm.Component.Reference.Litmus.fwdC_ok

end Silmaril.Wasm.Component.Reference.SyncImportRun.Fixture
