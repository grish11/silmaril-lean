module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Defs
public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Thms
import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Suite
import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Execution
import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Producer
import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Consumer

public section

namespace Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports

open Functions (Program)
open Lists (State)

/-- The importer compiler uses the declared alias and preserves the producer table. -/
theorem consumer_layout (plan : Consumer) {program : Program} {consumer : ResolvedModule}
    (checked : resolve plan.commands program = .ok consumer) :
    consumer.program = program ∧ consumer.source.commands = plan.code ∧
    consumer.source.globals = plan.globals ∧ consumer.source.fileNames = [plan.alias] :=
  Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.consumer_layout plan checked

/-- Preserving the heap entries transports the exact published callable,
including the original frozen closure record and its captures. -/
theorem cached_publication {exports : Environment} {program : Program} {published : Modules.Published}
    {state next : State} (live : PublishedLive exports program published state)
    (kept : ∀ (address : Nat) cell, state.heap[address]? = some cell → next.heap[address]? = some cell) :
    PublishedLive exports program published next :=
  Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.cached_publication live kept

/-- A finite suite follows the reached environment and stops at the
first error. On success each entry in its final environment still
selects the actual linked closure. -/
theorem run_suite {source : List Command} {seed : Program} {resolved : ResolvedModule}
    (checked : resolve source seed = .ok resolved)
    {manifest : Modules.Loader.Manifest} {active : List Nat} {id : Nat}
    {importName : String} {globals : List String} (separate : importName ∉ globals)
    (steps : List (Step importName globals)) {env : Environment} (admitted : ReadyFor env steps)
    (session : Modules.Loader.Session) (frame : Frame importName globals session.runtime)
    (live : Live importName resolved.program env session.runtime) :
    ∃ out, SuiteRuns session.runtime steps out ∧
      Modules.Loader.Runs resolved.program manifest active (.commands id (steps.map Step.code)) session
        (Modules.Loader.liftResult id session out) ∧
      ∀ reached, out = .ok () reached →
        Frame importName globals reached ∧ Live importName resolved.program (steps.foldl Step.advance env) reached :=
  Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.run_suite
    checked separate steps admitted session frame live

/-- From a cold session, the reached dependency and import derive the
actual callable and exact consumer outcome. -/
theorem cold_agrees {commands : List Command} {linked final : Program}
    {code : List Modules.Command} {producer consumer : ResolvedModule} {exports : Environment}
    (profile : Plan (Trace.names commands) (fun _ => none) commands linked code final exports)
    (producerChecked : resolve commands linked = .ok producer)
    (plan : Consumer) (consumerChecked : resolve plan.commands producer.program = .ok consumer)
    (covered : Covered exports commands plan) (caller : State) :
    Agrees commands producer consumer plan exports ⟨caller, []⟩ :=
  Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.cold_agrees
    profile producerChecked plan consumerChecked covered caller

/-- The first actual producer load establishes the cache evidence.
A later consumer load reuses that publication and its shared cells. -/
theorem preloaded_agrees {commands : List Command} {linked final : Program}
    {code : List Modules.Command} {producer consumer : ResolvedModule} {exports : Environment}
    (profile : Plan (Trace.names commands) (fun _ => none) commands linked code final exports)
    (producerChecked : resolve commands linked = .ok producer)
    (plan : Consumer) (consumerChecked : resolve plan.commands producer.program = .ok consumer)
    (covered : Covered exports commands plan) (caller : State) :
    ∃ preload, Producer commands producer.source ⟨caller, []⟩ preload ∧
      Modules.Loader.load producer.program (graph producer consumer plan) 0 ⟨caller, []⟩ = preload ∧
      ∀ published reached, preload = .ok published reached →
        reached.cache = [(0, published)] ∧ Agrees commands producer consumer plan exports reached :=
  Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.preloaded_agrees
    profile producerChecked plan consumerChecked covered caller

end Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports
