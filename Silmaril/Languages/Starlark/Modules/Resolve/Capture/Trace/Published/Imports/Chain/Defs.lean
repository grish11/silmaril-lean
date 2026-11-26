module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Defs

public section

namespace Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Chain

open Functions (Program)
open Lists (State)
open Loader (Manifest ModuleId Session)
open Defaults.Nested.Sequence.Recursive.Call (ClosureAt)

/-- Computed exports for a suite with one imported regular callable.
A downstream load can use a re-export or a checked factory result. -/
@[expose] def exportsOf (plan : Consumer) (seed : Program) (imported : Callable) : Environment :=
  let tracked := trackSuite imported seed (initial plan.alias imported) plan.body
  fun name =>
    if name ∈ plan.globals then
      match tracked name with
      | some (.regular callee) => some callee
      | _ => none
    else none

/-- The source analysis either identifies a tracked, public callable or
establishes that the requested name is outside the dependency's globals. -/
inductive Demand (plan : Consumer) (seed : Program)
    (dependencyExports : Environment) (dependencySource : Modules.Source) : Environment → Prop where
  | missing : plan.name ∉ dependencySource.globals → Demand plan seed dependencyExports dependencySource (fun _ => none)
  | found (callee : Callable) : dependencyExports plan.name = some callee →
      ReadyFor callee seed (initial plan.alias callee) plan.body →
      Demand plan seed dependencyExports dependencySource (exportsOf plan seed callee)

/-- Cached publications keep the original function address and defining
environment. Exact frozen flags are part of the operational result. -/
@[expose] def Publication (exports : Environment) (origin : Program)
    (source : Modules.Source) (published : Modules.Published) (state : State) : Prop :=
  (∀ name value, published.exports.lookup name = some value → name ∈ source.globals) ∧
  ∀ name callee, exports name = some callee → Modules.isPublic name = true →
    callee.Linked origin ∧ ∃ address defining,
      published.exports.lookup name = some (.function address) ∧
      Nonempty (ClosureAt callee.site callee.id defining state address)

@[expose] def Cache (origin : Program) (manifest : Manifest)
    (exports : ModuleId → Environment) (session : Session) : Prop :=
  ∀ id published, session.cache.lookup id = some published →
    ∃ bound : id < manifest.size,
      Publication (exports id) origin manifest[id].source published session.runtime

@[expose] def resultSession {α : Type} : Loader.Result α → Session :=
  Imports.reachedSession

/-- The edge observes the actual dependency outcome and stops before the
suite if that outcome or import binding fails. -/
inductive Edge (plan : Consumer) (seed : Program) (id : ModuleId) (source : Modules.Source)
    (caller : State) : Loader.Result Modules.Published → Loader.Result Modules.Published → Prop where
  | dependencyError {error : Loader.Error} {reached : Session} :
      Edge plan seed id source caller (.error error reached)
        (.error error {reached with runtime := Modules.restoreThread caller reached.runtime})
  | missing {published : Modules.Published} {reached : Session} :
      BindsAlias plan published reached.runtime (.error (.missingExport plan.label plan.name) reached.runtime) →
      Edge plan seed id source caller (.ok published reached)
        (observed id source caller reached.cache (.error (.missingExport plan.label plan.name) reached.runtime))
  | suite {published : Modules.Published} {reached : Session} {bound : State}
      (callee : Callable) {out : Modules.Result Unit} :
      BindsAlias plan published reached.runtime (.ok () bound) →
      SuiteRuns callee seed bound plan.body out →
      Edge plan seed id source caller (.ok published reached) (observed id source caller reached.cache out)

/-- Each reached load restores its caller, preserves earlier cells and
maintains the cache relation. A success makes its actual publication available. -/
structure Reached (origin : Program) (manifest : Manifest) (exports : ModuleId → Environment)
    (id : ModuleId) (caller : Session) (out : Loader.Result Modules.Published) : Prop where
  slots : (resultSession out).runtime.slots = caller.runtime.slots
  bindings : (resultSession out).runtime.bindings = caller.runtime.bindings
  iterators : (resultSession out).runtime.iterators = caller.runtime.iterators
  contents : KeepsContents caller.runtime (resultSession out).runtime
  cache : Cache origin manifest exports (resultSession out)
  retained : ∀ id value, caller.cache.lookup id = some value → (resultSession out).cache.lookup id = some value
  published : ∀ value next, out = .ok value next → next.cache.lookup id = some value


open Defaults.Nested.Sequence (PreservesDeclarations)

local notation "Normalized" => Modules.Resolve.Command

/-- Each module has either a checked load-free body or one leading import
of a lower-numbered module, followed by the checked suite. -/
inductive Node (origin final : Program) (manifest : Manifest) (exports : ModuleId → Environment)
    (id : ModuleId) (bound : id < manifest.size) : Prop where
  | root {commands : List Normalized} {seed emitted : Program} {code : List Modules.Command}
      {resolved : ResolvedModule} :
      Plan (Trace.names commands) (fun _ => none) commands seed code emitted (exports id) →
      resolve commands seed = .ok resolved →
      PreservesDeclarations resolved.program origin →
      manifest[id].source = resolved.source →
      Node origin final manifest exports id bound
  | importer {seed : Program} (plan : Consumer) {resolved : ResolvedModule} {dependency : ModuleId}
      (earlier : dependency < id) :
      resolve plan.commands seed = .ok resolved →
      PreservesDeclarations origin seed →
      PreservesDeclarations resolved.program final →
      manifest[id].source = resolved.source →
      Loader.resolve manifest id plan.label = some dependency →
      Demand plan seed (exports dependency) (manifest[dependency]'(Nat.lt_trans earlier bound)).source (exports id) →
      Node origin final manifest exports id bound

/-- The checked final table and each node's source certificate are fixed
for an entire session. The environment contains static callable descriptions. -/
structure Graph (origin : Program) (manifest : Manifest) where
  commands : List Normalized
  seed : Program
  linked : ResolvedModule
  checked : resolve commands seed = .ok linked
  includesOrigin : PreservesDeclarations origin linked.program
  exports : ModuleId → Environment
  nodes : ∀ id (bound : id < manifest.size), Node origin linked.program manifest exports id bound

/-- Independent source traces use the actual cached value or the reached
source execution of the dependency, with no heap-address premise. -/
inductive TraceRun (manifest : Manifest) :
    ModuleId → Session → Loader.Result Modules.Published → Prop where
  | cached {id : ModuleId} {state : Session} {published : Modules.Published} :
      state.cache.lookup id = some published → TraceRun manifest id state (.ok published state)
  | root {id : ModuleId} {state : Session} {source : Modules.Source}
      {commands : List Normalized} {out : Modules.Result Unit} {bound : id < manifest.size} :
      manifest[id].source = source →
      state.cache.lookup id = none →
      ExecutesAll (Trace.names commands) (Modules.enter source state.runtime) commands out →
      TraceRun manifest id state (observed id source state.runtime state.cache out)
  | edge {id dependency : ModuleId} {state : Session} {source : Modules.Source} {plan : Consumer}
      {seed : Program} {loaded out : Loader.Result Modules.Published} {bound : id < manifest.size} :
      manifest[id].source = source →
      state.cache.lookup id = none →
      Loader.resolve manifest id plan.label = some dependency →
      TraceRun manifest dependency {state with runtime := Modules.enter source state.runtime} loaded →
      Edge plan seed id source state.runtime loaded out →
      TraceRun manifest id state out

/-- A sequence of actual top-level requests. A failed request still
provides its residual session to the next caller. -/
inductive Requests {origin : Program} {manifest : Manifest} (graph : Graph origin manifest) :
    List ModuleId → Session → Session → Prop where
  | done (state : Session) : Requests graph [] state state
  | more {id : ModuleId} {ids : List ModuleId} {state next : Session}
      {out : Loader.Result Modules.Published} :
      TraceRun manifest id state out →
      Loader.load graph.linked.program manifest id state = out →
      Requests graph ids (resultSession out) next →
      Requests graph (id :: ids) state next


end Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Chain
