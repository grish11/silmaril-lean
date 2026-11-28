module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Escape.Scoped.Defs
public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Body.Thms
import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Escape.Scoped.Frame

public section

namespace Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Escape.Scoped

open Block (ModuleBinders)
open Functions
open Lists (State Capture)

/-- Checked source emits the independently ordered capture list as part
of the child declaration at its actual index in the final program. -/
theorem checked_site {before after : List Command} {globals : List String} {spec : Spec}
    {linked : Program} {resolved : ResolvedModule} (names : Names spec)
    (plan : Plan globals spec) (declared : ModuleBinders (before ++ spec.command :: after) globals)
    (checked : resolve (before ++ spec.command :: after) linked = .ok resolved)
    (suffix : RootCall.Segment globals after) :
    ∃ id, resolved.source.commands[before.length]? = some (.exec (.define spec.wrapper.name (id + 1))) ∧
      resolved.program[id]? = some (plan.childDeclaration) ∧
      resolved.program[id + 1]? = some (plan.frame id).declaration :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Escape.Scoped.checked_site
    names plan declared checked suffix

/-- The prefix activation reads the caller heap at the installed module
addresses. Owned locals use the separate local slot namespace. -/
theorem prefix_frame {globals : List String} {spec : Spec} (plan : Plan globals spec)
    (childId : Nat) (caller : State) (moduleCaptures : List Capture)
    (installed : Installs caller plan.moduleFree moduleCaptures)
    (cells : Defaults.Body.CaptureCells caller moduleCaptures) (assigned : List (Binding × Lists.Value)) :
    Defaults.Body.Frame (spec.block globals) plan.moduleFree caller.heap.size
      (activate caller (plan.frame childId).declaration moduleCaptures assigned) :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Escape.Scoped.prefix_frame
    plan childId caller moduleCaptures installed cells assigned

/-- An installed module reference reads the caller's current binding value.
The equality includes both initialized and uninitialized cells. -/
theorem prefix_module_read {globals : List String} {spec : Spec} (plan : Plan globals spec)
    (childId : Nat) (caller : State) (moduleCaptures : List Capture)
    (installed : Installs caller plan.moduleFree moduleCaptures) (assigned : List (Binding × Lists.Value))
    (name : String) (selected : (⟨globalSlot name, globalSlot name⟩ : FreeName) ∈ plan.moduleFree)
    (address : Nat) (value : Option Lists.Value) (frozen : Bool)
    (owned : caller.slots (globalSlot name) = some (.owned address))
    (cell : caller.heap[address]? = some ⟨.binding value, frozen⟩) :
    let active := activate caller (plan.frame childId).declaration moduleCaptures assigned
    active.slots (globalSlot name) = some (.captured address false) ∧
      active.bindingValue (globalSlot name) = caller.bindingValue (globalSlot name) :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Escape.Scoped.prefix_module_read
    plan childId caller moduleCaptures installed assigned name selected address value frozen owned cell

/-- The reached wrapper activation supplies the capture vector in declaration order. -/
theorem activate_installs {globals : List String} {spec : Spec} (plan : Plan globals spec)
    (childId : Nat) (caller : State) (moduleCaptures : List Capture) (assigned : List (Binding × Lists.Value)) :
    let active := activate caller (plan.frame childId).declaration moduleCaptures assigned
    ∃ captures, Installs active plan.body.free captures ∧ Defaults.Body.CaptureCells active captures :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Escape.Scoped.activate_installs
    plan childId caller moduleCaptures assigned

/-- Defaults run directly at wrapper entry when the prefix is empty.
A reached failure there leaves the update locals unbound and restores the caller. -/
theorem failed_local_unbound {globals : List String} {spec : Spec} (names : Names spec) (plan : Plan globals spec)
    (childId : Nat) (caller : State) (moduleCaptures : List Capture) {values : List Lists.Value} {assigned : List (Binding × Lists.Value)}
    (bound : Entry.Binds spec.parameters values (.ok assigned)) (name : String) (localName : name ∈ spec.updates.map Prod.fst)
    {error : Lists.Error} {next : State}
    (failed : Escape.ReturnsWith spec.wrapper (spec.block globals) plan.defaultItems childId plan.body.free spec.updates caller
      (activate caller (spec.frame childId).declaration moduleCaptures assigned) (.error error next)) :
    let active := activate caller (spec.frame childId).declaration moduleCaptures assigned
    ∃ address, active.slots (fileSlot name) = some (.owned address) ∧
      next.heap[address]? = some ⟨.binding none, false⟩ ∧ next.slots = caller.slots ∧ next.bindings = caller.bindings :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Escape.Scoped.failed_local_unbound
    names plan childId caller moduleCaptures bound name localName failed

/-- Repeated source reads share one installed binding in the closure. -/
theorem capture_order {globals : List String} {spec : Spec} (plan : Plan globals spec)
    {active : State} {captures : List Capture} (installed : Installs active plan.body.free captures) :
    captures.map Capture.binding = (plan.childDeclaration).free.map FreeName.target ∧
      (captures.map Capture.binding).Nodup :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Escape.Scoped.capture_order plan installed

/-- A reached return identifies the prefix state, definition-time default
values, and captured cells. Subsequent writes and caller restoration leave
the escaped child with the compositional frame for a later call. -/
theorem returned_frame {globals : List String} {spec : Spec} (names : Names spec)
    (plan : Plan globals spec) (program : Program) (available : List DeclarationId) (childId : Nat)
    (found : program[childId]? = some (plan.childDeclaration))
    (caller : State) (moduleCaptures : List Capture) (moduleInstalled : Installs caller plan.moduleFree moduleCaptures)
    (moduleCells : Defaults.Body.CaptureCells caller moduleCaptures) (assigned : List (Binding × Lists.Value)) {address : Nat} {next : State}
    (source : Returns plan childId caller moduleCaptures assigned (.ok (.function address) next)) :
    let active := activate caller (plan.frame childId).declaration moduleCaptures assigned
    ∃ reached values captures, values.length = spec.child.parameters.optional.length ∧
      Defaults.Body.RunsPrefix (spec.block globals) active spec.leading plan.leadingCode (.ok () reached) ∧
      (∃ defaultsState, Lexical.Evaluates (spec.block globals) reached plan.defaultItems (.ok values defaultsState)) ∧
      Installs reached plan.body.free captures ∧
      next.heap[address]? = some ⟨.function ⟨childId, captures, spec.wrapper.saved values⟩, false⟩ ∧
      next.slots = caller.slots ∧ next.bindings = caller.bindings ∧
      (∀ parameter before frozen,
        reached.slots (fileSlot spec.wrapper.parameter) = some (.owned parameter) →
        reached.heap[parameter]? = some ⟨.binding before, frozen⟩ →
        next.heap[parameter]? = some ⟨.binding (some (.scalar (.int spec.wrapper.rebound))), frozen⟩) ∧
      ∀ arguments : List (Binding × Lists.Value),
        Defaults.Body.Frame plan.body.block plan.body.free next.heap.size
          (activate next (plan.childDeclaration) captures arguments) :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Escape.Scoped.returned_frame
    names plan program available childId found caller moduleCaptures moduleInstalled moduleCells assigned source

end Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Escape.Scoped
