module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Defs
public import Silmaril.Languages.Starlark.Modules.Resolve.Thms
import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Execution
import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Frame

public section

namespace Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published

open Functions (Program Actual DeclarationId)
open Defaults.Nested.Sequence (PreservesDeclarations)
open Defaults.Nested.Sequence.Recursive.Call (BodyEntry RunsActual BindingRule PackRule ClosureAt)
open Lists (State Outcome)
open Assignment (LexicalBlock)

/-- A checked load-free plan derives its reached source trace from module
entry. The same trace determines exact initialization and publication. -/
theorem module_agrees {commands : List Resolve.Command}
    {code : List Modules.Command} {linked final : Program} {resolved : ResolvedModule} {exports : Environment}
    (profile : Plan (Trace.names commands) (fun _ => none) commands linked code final exports)
    (checked : resolve commands linked = .ok resolved) (host : Catalog) (caller : State) :
    ∃ reached, ExecutesAll (Trace.names commands) (enter resolved.source caller) commands reached ∧
      Modules.Runs resolved.program host (enter resolved.source caller) resolved.source.commands reached ∧
      Modules.Initializes resolved.program host resolved.source caller (finish resolved.source caller reached) ∧
      runModule commands host caller linked = .ok (finish resolved.source caller reached) ∧
      ∀ published finished, finish resolved.source caller reached = .ok published finished →
        PublishedLive exports resolved.program published finished :=
  Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.module_agrees
    profile checked host caller

/-- A checked producer runs in a larger checked declaration table if its
original declaration lookups remain valid. -/
theorem module_runs_extending {commands : List Resolve.Command}
    {code : List Modules.Command} {linked final : Program} {resolved : ResolvedModule} {exports : Environment}
    (profile : Plan (Trace.names commands) (fun _ => none) commands linked code final exports)
    (checked : resolve commands linked = .ok resolved)
    {other : List Resolve.Command} {seed : Program} {whole : ResolvedModule}
    (wholeChecked : resolve other seed = .ok whole)
    (extension : PreservesDeclarations resolved.program whole.program) (host : Catalog) (caller : State) :
    ∃ reached, ExecutesAll (Trace.names commands) (enter resolved.source caller) commands reached ∧
      Modules.Runs whole.program host (enter resolved.source caller) resolved.source.commands reached ∧
      KeepsContents caller (resultState (finish resolved.source caller reached)) ∧
      ∀ published finished, finish resolved.source caller reached = .ok published finished →
        PublishedLive exports whole.program published finished :=
  Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.module_runs_extending
    profile checked wholeChecked extension host caller

/-- Module execution keeps the caller's original cells, allowing
publication to change only their frozen flags. -/
theorem module_agrees_preserving {commands : List Resolve.Command}
    {code : List Modules.Command} {linked final : Program} {resolved : ResolvedModule} {exports : Environment}
    (profile : Plan (Trace.names commands) (fun _ => none) commands linked code final exports)
    (checked : resolve commands linked = .ok resolved) (host : Catalog) (caller : State) :
    ∃ reached, ExecutesAll (Trace.names commands) (enter resolved.source caller) commands reached ∧
      Modules.Runs resolved.program host (enter resolved.source caller) resolved.source.commands reached ∧
      Modules.Initializes resolved.program host resolved.source caller (finish resolved.source caller reached) ∧
      runModule commands host caller linked = .ok (finish resolved.source caller reached) ∧
      KeepsContents caller (resultState (finish resolved.source caller reached)) ∧
      ∀ published finished, finish resolved.source caller reached = .ok published finished →
        PublishedLive exports resolved.program published finished :=
  Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.module_agrees_preserving
    profile checked host caller

theorem plan_globals {commands : List Resolve.Command}
    {env exports : Environment} {code : List Modules.Command} {linked final : Program} {resolved : ResolvedModule}
    (profile : Plan (Trace.names commands) env commands linked code final exports)
    (checked : resolve commands linked = .ok resolved) :
    resolved.source.globals = Trace.names commands :=
  Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.plan_globals profile checked

theorem plan_code {commands : List Resolve.Command}
    {env exports : Environment} {code : List Modules.Command} {linked final : Program} {resolved : ResolvedModule}
    (profile : Plan (Trace.names commands) env commands linked code final exports)
    (checked : resolve commands linked = .ok resolved) :
    resolved.source.commands = code ∧ resolved.program = final :=
  Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.plan_code profile checked

/-- A linked callable activates its independently checked body using the
reached defaults and installed capture cells. -/
theorem enter_callable {callee : Callable}
    {commands : List Resolve.Command} {linked : Program} {resolved : ResolvedModule}
    (checked : resolve commands linked = .ok resolved) (known : callee.Linked resolved.program) :
    BodyEntry callee.site resolved.program (List.range resolved.program.size) callee.id callee.BodyRuns :=
  Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.enter_callable checked known

/-- A checked ordinary body needs only declaration indices below its own. -/
theorem enter_callable_below {callee : Callable} {prefixTable : Program}
    {commands : List Resolve.Command} {linked : Program} {resolved : ResolvedModule}
    (checked : resolve commands linked = .ok resolved) (known : callee.Linked prefixTable)
    (extension : PreservesDeclarations prefixTable resolved.program) (available : List DeclarationId)
    (retained : List.Subset (List.range callee.id) available) :
    BodyEntry callee.site resolved.program available callee.id callee.BodyRuns :=
  Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.enter_callable_below
    checked known extension available retained

/-- A caller in a later module can use the original callable with a reduced
guard if it retains the producer's declaration IDs. -/
theorem enter_callable_for {callee : Callable} {prefixTable : Program}
    {commands : List Resolve.Command} {linked : Program} {resolved : ResolvedModule}
    (checked : resolve commands linked = .ok resolved) (known : callee.Linked prefixTable)
    (extension : PreservesDeclarations prefixTable resolved.program) (available : List DeclarationId)
    (retained : List.Subset (List.range prefixTable.size) available) :
    BodyEntry callee.site resolved.program available callee.id callee.BodyRuns :=
  Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.enter_callable_for
    checked known extension available retained

/-- Source-declared callable exports link to the producer's original table. -/
theorem plan_exports_linked {commands : List Resolve.Command}
    {code : List Modules.Command} {linked final : Program} {resolved : ResolvedModule} {exports : Environment}
    (profile : Plan (Trace.names commands) (fun _ => none) commands linked code final exports)
    (checked : resolve commands linked = .ok resolved)
    {name : String} {callee : Callable} (tracked : exports name = some callee) :
    callee.Linked resolved.program :=
  Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.plan_exports_linked profile checked tracked

/-- Extending the table preserves the declaration ID and nested body links. -/
theorem linked_extends {callee : Callable} {earlier later : Program}
    (known : callee.Linked earlier) (extendsTable : PreservesDeclarations earlier later) :
    callee.Linked later :=
  Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.linked_extends known extendsTable

/-- The declaration selected by a callable return remains linked. -/
theorem returned_linked {callee : Callable} {program : Program} (known : callee.Linked program) :
    ∀ next, callee.returned.map Callable.nested = some next → next.Linked program :=
  Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.returned_linked known

/-- A successful call retains the actual returned callable in the restored caller heap. -/
theorem returned_record {callee : Callable} {block : LexicalBlock} {name : String} {slot : Binding}
    {Bound : Type} {actuals : State → Outcome Actual → Prop} {binds : BindingRule Bound} {packs : PackRule Bound}
    {state reached : State} {value : Lists.Value}
    (ran : RunsActual callee.site callee.BodyRuns block callee.id name slot actuals binds packs state (.ok value reached)) :
    ∀ next, callee.returned.map Callable.nested = some next → ∃ address defining, value = .function address ∧
      Nonempty (ClosureAt next.site next.id defining reached address) :=
  Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.returned_record ran

theorem write_slots (state : State) (binding : Binding) (value : Lists.Value) :
    (state.write binding value).slots = state.slots :=
  Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.write_slots state binding value

theorem written_cell {state : State} {binding : Binding} {address : Nat} {old : Option Lists.Value}
    {frozen : Bool} (value : Lists.Value) (owned : state.slots binding = some (.owned address))
    (stored : state.heap[address]? = some ⟨.binding old, frozen⟩) :
    (state.write binding value).heap[address]? = some ⟨.binding (some value), frozen⟩ :=
  Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.written_cell value owned stored

theorem published_function {source : Modules.Source} {name : String} {state : State} {address : Nat}
    (member : name ∈ source.globals) (publicName : Modules.isPublic name = true)
    (loaded : state.bindingValue (globalSlot name) = .ok (.function address)) :
    (Modules.publish source state).1.exports.lookup name = some (.function address) :=
  Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.published_function member publicName loaded

theorem publish_record {source : Modules.Source} {callee : Callable} {name : String}
    {state defining : State} {address : Nat} (caller : State) (member : name ∈ source.globals)
    (publicName : Modules.isPublic name = true) (loaded : state.bindingValue (globalSlot name) = .ok (.function address))
    (record : ClosureAt callee.site callee.id defining state address) :
    (Modules.publish source state).1.exports.lookup name = some (.function address) ∧
      ∃ published : ClosureAt callee.site callee.id defining
        (Modules.restoreThread caller (Modules.publish source state).2) address, published.frozen = true :=
  Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.publish_record caller member publicName loaded record

theorem keep_record {callee : Callable} {defining state next : State} {address : Nat}
    (record : ClosureAt callee.site callee.id defining state address)
    (kept : Defaults.Body.Keeps state.heap.size state next) : Nonempty (ClosureAt callee.site callee.id defining next address) :=
  Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.keep_record record kept

theorem write_slot_record {callee : Callable} {defining state : State} {address slot : Nat}
    {target : Binding} {old : Option Lists.Value} {frozen : Bool}
    (record : ClosureAt callee.site callee.id defining state address)
    (owned : state.slots target = some (.owned slot))
    (stored : state.heap[slot]? = some ⟨.binding old, frozen⟩) (value : Lists.Value) :
    Nonempty (ClosureAt callee.site callee.id defining (state.write target value) address) :=
  Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.write_slot_record record owned stored value

end Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published
