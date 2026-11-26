module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Chain.Defs
import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Chain.Edge
import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Chain.Graph

public section

namespace Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Chain

open Defaults.Nested.Sequence (PreservesDeclarations)
open Functions (Program)
open Lists (State)
open Loader (Manifest ModuleId Session)

/-- One checked import composes with a reached dependency in any manifest. The imported call uses the actual cache entry and address. -/
theorem edge_agrees {origin seed finalSeed : Program} {manifest : Manifest} {exports : ModuleId → Environment}
    {finalCommands : List Resolve.Command} {whole consumer : ResolvedModule}
    (wholeChecked : resolve finalCommands finalSeed = .ok whole)
    (plan : Consumer) (checked : resolve plan.commands seed = .ok consumer)
    (originPrefix : PreservesDeclarations origin seed) (extension : PreservesDeclarations consumer.program whole.program)
    {id dependencyId : ModuleId} (bound : id < manifest.size) (dependencyBound : dependencyId < manifest.size)
    (entry : manifest[id].source = consumer.source)
    (label : Modules.Loader.resolve manifest id plan.label = some dependencyId)
    (demand : Demand plan seed (exports dependencyId) manifest[dependencyId].source (exports id))
    {active : List Nat} (permitted : id ∉ active) (caller : Session) (cold : caller.cache.lookup id = none)
    {dependency : Modules.Loader.Result Modules.Published}
    (nativeDependency : Modules.Loader.Runs whole.program manifest (id :: active) (.initialize dependencyId)
      {caller with runtime := enter consumer.source caller.runtime} dependency)
    (reachedDependency : Reached origin manifest exports dependencyId
      {caller with runtime := enter consumer.source caller.runtime} dependency) :
    ∃ out, Edge plan seed id consumer.source caller.runtime dependency out ∧
      Modules.Loader.Runs whole.program manifest active (.initialize id) caller out ∧
      Reached origin manifest exports id caller out :=
  Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Chain.edge_agrees
    wholeChecked plan checked originPrefix extension bound dependencyBound entry label demand permitted caller cold
    nativeDependency reachedDependency

/-- Independent source execution and loader denotation agree for a checked topological graph with one dependency per importing module. -/
theorem agrees {origin : Program} {manifest : Manifest} (graph : Graph origin manifest)
    (id : ModuleId) (bound : id < manifest.size) (caller : Session)
    (cache : Cache origin manifest graph.exports caller) :
    ∃ out, TraceRun manifest id caller out ∧
      Modules.Loader.Runs graph.linked.program manifest [] (.initialize id) caller out ∧
      Modules.Loader.load graph.linked.program manifest id caller = out ∧
      Reached origin manifest graph.exports id caller out :=
  Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Chain.agrees
    graph id bound caller cache

/-- Actual prior requests establish the cache invariant for later requests, including after a reached failure. -/
theorem requests {origin : Program} {manifest : Manifest} (graph : Graph origin manifest)
    (ids : List ModuleId) (bounded : ∀ id ∈ ids, id < manifest.size)
    (caller : Session) (cache : Cache origin manifest graph.exports caller) :
    ∃ next, Requests graph ids caller next ∧ Cache origin manifest graph.exports next :=
  Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Chain.requests
    graph ids bounded caller cache

/-- A caller with an empty cache needs no runtime provenance premise. -/
theorem cold_agrees {origin : Program} {manifest : Manifest} (graph : Graph origin manifest)
    (id : ModuleId) (bound : id < manifest.size) (caller : State) :
    ∃ out, TraceRun manifest id ⟨caller, []⟩ out ∧
      Loader.Runs graph.linked.program manifest [] (.initialize id) ⟨caller, []⟩ out ∧
      Loader.load graph.linked.program manifest id ⟨caller, []⟩ = out ∧
      Reached origin manifest graph.exports id ⟨caller, []⟩ out :=
  agrees graph id bound ⟨caller, []⟩ (fun _ _ missing => nomatch missing)

end Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Chain
