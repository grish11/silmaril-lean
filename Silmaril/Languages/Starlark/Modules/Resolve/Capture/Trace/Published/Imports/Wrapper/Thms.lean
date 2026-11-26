module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Wrapper.Defs
public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Thms
import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Wrapper.Link
import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Wrapper.Loader

public section

namespace Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Wrapper

open Defaults.Nested.Sequence (PreservesDeclarations)
open Functions (Program withoutDeclaration)
open Lists (State)

/-- The wrapper is emitted after the producer and its capture comes from the file-local load binding. -/
theorem layout (wrapper : Wrapper) {producer : Program} {consumer : ResolvedModule}
    (checked : resolve wrapper.commands producer = .ok consumer) :
    consumer.program = producer.push wrapper.site.declaration ∧
    consumer.source.commands = wrapper.moduleCode producer ∧
    consumer.source.globals = [wrapper.name, wrapper.destination] ∧
    consumer.source.fileNames = [wrapper.alias] :=
  Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Wrapper.layout
    wrapper checked

/-- The original declaration lookups survive the append, including under the wrapper’s reduced call guard. -/
theorem linked (wrapper : Wrapper) {producer : Program} {consumer : ResolvedModule}
    (checked : resolve wrapper.commands producer = .ok consumer) :
    PreservesDeclarations producer consumer.program ∧
    consumer.program[producer.size]? = some wrapper.site.declaration ∧
    List.Subset (List.range producer.size)
      (withoutDeclaration (List.range consumer.program.size) producer.size) :=
  Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Wrapper.linked
    wrapper checked

/-- Starting from a cold two-module session, checked source execution derives the wrapper and imported calls from their reached bindings. -/
theorem cold_agrees (wrapper : Wrapper) {commands : List Resolve.Command} {seed final : Program}
    {code : List Modules.Command} {producer consumer : ResolvedModule} {exports : Environment}
    (profile : Plan (Trace.names commands) (fun _ => none) commands seed code final exports)
    (producerChecked : resolve commands seed = .ok producer)
    (consumerChecked : resolve wrapper.commands producer.program = .ok consumer)
    (covered : (∃ callee, exports wrapper.imported = some callee) ∨ wrapper.imported ∉ Trace.names commands)
    (caller : State) :
    wrapper.Agrees producer consumer commands exports ⟨caller, []⟩ :=
  Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Wrapper.cold_agrees
    wrapper profile producerChecked consumerChecked covered caller

/-- A successful preload establishes the actual cache entry and preserved callable cells for the later wrapper call. -/
theorem preloaded_agrees (wrapper : Wrapper) {commands : List Resolve.Command} {seed final : Program}
    {code : List Modules.Command} {producer consumer : ResolvedModule} {exports : Environment}
    (profile : Plan (Trace.names commands) (fun _ => none) commands seed code final exports)
    (producerChecked : resolve commands seed = .ok producer)
    (consumerChecked : resolve wrapper.commands producer.program = .ok consumer)
    (covered : (∃ callee, exports wrapper.imported = some callee) ∨ wrapper.imported ∉ Trace.names commands)
    (caller : State) :
    ∃ preload, Producer commands producer.source ⟨caller, []⟩ preload ∧
      Modules.Loader.load consumer.program (wrapper.graph producer consumer) 0 ⟨caller, []⟩ = preload ∧
      ∀ published reached, preload = .ok published reached →
        reached.cache = [(0, published)] ∧ wrapper.Agrees producer consumer commands exports reached :=
  Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Wrapper.preloaded_agrees
    wrapper profile producerChecked consumerChecked covered caller

end Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Wrapper
