module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Defs

public section

namespace Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Chain

open Functions (Program)
open Lists (State)
open Loader (Manifest ModuleId Session)
open Defaults.Nested.Sequence.Recursive.Call (ClosureAt)

/-- The suite publishes any tracked callable in a declared global. -/
@[expose] def exportsOf (plan : Consumer) (seed : Program) (imported : Callee) : Tracked :=
  let tracked := trackSuite seed (initial plan.alias imported) plan.body
  fun name => if name ∈ plan.globals then tracked name else none

@[expose] def rootExports (env : Environment) : Tracked :=
  fun name => (env name).map Callee.regular

/-- The source analysis either identifies a tracked, public callable or
establishes that the requested name is outside the dependency's globals. -/
inductive Demand (plan : Consumer) (seed : Program)
    (dependencyExports : Tracked) (dependencySource : Modules.Source) : Tracked → Prop where
  | missing : plan.name ∉ dependencySource.globals → Demand plan seed dependencyExports dependencySource (fun _ => none)
  | found (callee : Callee) : dependencyExports plan.name = some callee →
      callee.layout.id < seed.size →
      ReadyFor seed (initial plan.alias callee) plan.body →
      Demand plan seed dependencyExports dependencySource (exportsOf plan seed callee)

/-- Static evidence follows lookup order, which is reverse source order for
a single command. A missing export ends selection without installing aliases. -/
inductive SelectPlan (exports : Tracked) (globals : List String) :
    List ImportBinding → Tracked → Option Tracked → Prop where
  | done (env : Tracked) : SelectPlan exports globals [] env (some env)
  | missing {item : ImportBinding} {rest : List ImportBinding} {env : Tracked} :
      item.name ∉ globals → SelectPlan exports globals (item :: rest) env none
  | found {item : ImportBinding} {rest : List ImportBinding} {env : Tracked} {selected : Option Tracked}
      (callee : Callee) :
      exports item.name = some callee →
      SelectPlan exports globals rest (track env item.alias (some callee)) selected →
      SelectPlan exports globals (item :: rest) env selected

/-- The checked prefix resolves each reached label once. Only successful
selection in a whole command enables the remaining commands. -/
inductive ImportPlan (manifest : Manifest) (exports : ModuleId → Tracked)
    (id : ModuleId) (bound : id < manifest.size) :
    List ImportSite → Tracked → Option Tracked → Prop where
  | done (env : Tracked) : ImportPlan manifest exports id bound [] env (some env)
  | unresolved {site : ImportSite} {tail : List ImportSite} {env : Tracked} :
      Loader.resolve manifest id site.label = none →
      ImportPlan manifest exports id bound (site :: tail) env none
  | load {site : ImportSite} {tail : List ImportSite} {env : Tracked} {dependency : ModuleId}
      {selected final : Option Tracked} (earlier : dependency < id) :
      Loader.resolve manifest id site.label = some dependency →
      SelectPlan (exports dependency) (manifest[dependency]'(Nat.lt_trans earlier bound)).source.globals
        site.bindings.reverse env selected →
      (∀ next, selected = some next → ImportPlan manifest exports id bound tail next final) →
      (selected = none → final = none) →
      ImportPlan manifest exports id bound (site :: tail) env final

/-- Successful prefixes enable the ordinary suite. A statically missing
label or export leaves the body unreachable and supplies no publication. -/
@[expose] def OrderedReady (plan : OrderedConsumer) (seed : Program) (final : Option Tracked)
    (published : Tracked) : Prop :=
  match final with
  | none => published = fun _ => none
  | some env => ReadyFor seed env plan.body ∧
    published = fun name => if name ∈ plan.globals then trackSuite seed env plan.body name else none

/-- Cached publications keep the original function address and defining
environment. Exact frozen flags are part of the operational result. -/
@[expose] def Publication (exports : Tracked) (origin program : Program)
    (source : Modules.Source) (published : Modules.Published) (state : State) : Prop :=
  (∀ name value, published.exports.lookup name = some value → name ∈ source.globals) ∧
  ∀ name callee, exports name = some callee → Modules.isPublic name = true →
    ∃ address, published.exports.lookup name = some (.function address) ∧
      callee.At origin program state address

@[expose] def Cache (origin program : Program) (manifest : Manifest)
    (exports : ModuleId → Tracked) (session : Session) : Prop :=
  ∀ id published, session.cache.lookup id = some published →
    ∃ bound : id < manifest.size,
      Publication (exports id) origin program manifest[id].source published session.runtime

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
      (callee : Callee) {out : Modules.Result Unit} :
      BindsAlias plan published reached.runtime (.ok () bound) →
      SuiteRuns seed bound plan.body out →
      Edge plan seed id source caller (.ok published reached) (observed id source caller reached.cache out)

/-- Each reached load restores its caller, preserves earlier cells and
maintains the cache relation. A success makes its actual publication available. -/
structure Reached (origin program : Program) (manifest : Manifest) (exports : ModuleId → Tracked)
    (id : ModuleId) (caller : Session) (out : Loader.Result Modules.Published) : Prop where
  slots : (resultSession out).runtime.slots = caller.runtime.slots
  bindings : (resultSession out).runtime.bindings = caller.runtime.bindings
  iterators : (resultSession out).runtime.iterators = caller.runtime.iterators
  contents : KeepsContents caller.runtime (resultSession out).runtime
  cache : Cache origin program manifest exports (resultSession out)
  retained : ∀ id value, caller.cache.lookup id = some value → (resultSession out).cache.lookup id = some value
  published : ∀ value next, out = .ok value next → next.cache.lookup id = some value


open Defaults.Nested.Sequence (PreservesDeclarations)

local notation "Normalized" => Modules.Resolve.Command

/-- Each module has a checked load-free body or a leading prefix
of imports from lower-numbered modules, followed by the checked suite. -/
inductive Node (origin final : Program) (manifest : Manifest) (exports : ModuleId → Tracked)
    (id : ModuleId) (bound : id < manifest.size) : Prop where
  | root {commands : List Normalized} {seed emitted : Program} {code : List Modules.Command}
      {resolved : ResolvedModule} {ordinary : Environment} :
      Plan (Trace.names commands) (fun _ => none) commands seed code emitted ordinary →
      exports id = rootExports ordinary →
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

  | ordered {seed : Program} (plan : OrderedConsumer) {resolved : ResolvedModule} {finalEnv : Option Tracked} :
      resolve plan.commands seed = .ok resolved →
      PreservesDeclarations origin seed →
      PreservesDeclarations resolved.program final →
      manifest[id].source = resolved.source →
      ImportPlan manifest exports id bound plan.imports (fun _ => none) finalEnv →
      OrderedReady plan seed finalEnv (exports id) →
      Node origin final manifest exports id bound

/-- The checked final table and each node's source certificate are fixed
for an entire session. The environment contains static callable descriptions. -/
structure Graph (origin : Program) (manifest : Manifest) where
  commands : List Normalized
  seed : Program
  linked : ResolvedModule
  checked : resolve commands seed = .ok linked
  includesOrigin : PreservesDeclarations origin linked.program
  exports : ModuleId → Tracked
  nodes : ∀ id (bound : id < manifest.size), Node origin linked.program manifest exports id bound

/-- Look up all requested exports before writing any aliases. A reached
missing name wins immediately, even if other source items also lack exports. -/
inductive SelectImports (published : Modules.Published) (label : String) :
    List ImportBinding → Except Modules.Error (List (Binding × Lists.Value)) → Prop where
  | done : SelectImports published label [] (.ok [])
  | missing {item : ImportBinding} {tail : List ImportBinding} :
      published.exports.lookup item.name = none →
      SelectImports published label (item :: tail) (.error (.missingExport label item.name))
  | next {item : ImportBinding} {tail : List ImportBinding} {value : Lists.Value}
      {out : Except Modules.Error (List (Binding × Lists.Value))} :
      published.exports.lookup item.name = some value →
      SelectImports published label tail out →
      SelectImports published label (item :: tail) (out.map (List.cons (Modules.fileSlot item.alias, value)))

/-- The selected values are written in lookup order after the full selection succeeds. -/
@[expose] def installImports (state : State) (entries : List (Binding × Lists.Value)) : State :=
  entries.foldl (fun s (slot, value) => s.write slot value) state

mutual
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

  | orderedError {id : ModuleId} {state : Session} {source : Modules.Source}
      {plan : OrderedConsumer} {error : Loader.Error} {reached : Session} {bound : id < manifest.size} :
      manifest[id].source = source →
      state.cache.lookup id = none →
      ImportTrace manifest id plan.imports {state with runtime := Modules.enter source state.runtime}
        (.error error reached) →
      TraceRun manifest id state (.error error {reached with runtime := Modules.restoreThread state.runtime reached.runtime})
  | orderedSuite {id : ModuleId} {state : Session} {source : Modules.Source}
      {plan : OrderedConsumer} {seed : Program} {reached : Session} {out : Modules.Result Unit}
      {bound : id < manifest.size} :
      manifest[id].source = source →
      state.cache.lookup id = none →
      ImportTrace manifest id plan.imports {state with runtime := Modules.enter source state.runtime} (.ok () reached) →
      SuiteRuns seed reached.runtime plan.body out →
      TraceRun manifest id state (observed id source state.runtime reached.cache out)

/-- The source rules evaluate dependencies in order and bind only the
values returned by their actual publication. -/
inductive ImportTrace (manifest : Manifest) :
    ModuleId → List ImportSite → Session → Loader.Result Unit → Prop where
  | done {id : ModuleId} (state : Session) : ImportTrace manifest id [] state (.ok () state)
  | unresolved {id : ModuleId} {site : ImportSite} {tail : List ImportSite} {state : Session} :
      Loader.resolve manifest id site.label = none →
      ImportTrace manifest id (site :: tail) state (.error (.missingLabel id site.label) state)
  | dependencyError {id dependency : ModuleId} {site : ImportSite} {tail : List ImportSite}
      {state reached : Session} {error : Loader.Error} :
      Loader.resolve manifest id site.label = some dependency →
      TraceRun manifest dependency state (.error error reached) →
      ImportTrace manifest id (site :: tail) state (.error error reached)
  | selectionError {id dependency : ModuleId} {site : ImportSite} {tail : List ImportSite}
      {state reached : Session} {published : Modules.Published} {error : Modules.Error} :
      Loader.resolve manifest id site.label = some dependency →
      TraceRun manifest dependency state (.ok published reached) →
      SelectImports published site.label site.bindings.reverse (.error error) →
      ImportTrace manifest id (site :: tail) state (.error (.initialization id error) reached)
  | next {id dependency : ModuleId} {site : ImportSite} {tail : List ImportSite}
      {state reached : Session} {published : Modules.Published}
      {entries : List (Binding × Lists.Value)} {out : Loader.Result Unit} :
      Loader.resolve manifest id site.label = some dependency →
      TraceRun manifest dependency state (.ok published reached) →
      SelectImports published site.label site.bindings.reverse (.ok entries) →
      ImportTrace manifest id tail {reached with runtime := installImports reached.runtime entries} out →
      ImportTrace manifest id (site :: tail) state out
end

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
