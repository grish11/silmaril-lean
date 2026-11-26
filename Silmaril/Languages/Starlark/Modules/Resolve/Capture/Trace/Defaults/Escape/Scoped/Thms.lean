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
      resolved.program[id]? = some (plan.body.declaration spec.wrapper.codes) ∧
      resolved.program[id + 1]? = some (spec.frame id).declaration :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Escape.Scoped.checked_site
    names plan declared checked suffix

/-- The reached wrapper activation supplies the capture vector in declaration order. -/
theorem activate_installs {globals : List String} {spec : Spec} (plan : Plan globals spec)
    (childId : Nat) (caller : State) (assigned : List (Binding × Lists.Value)) :
    let active := activate caller (spec.frame childId).declaration [] assigned
    ∃ captures, Installs active plan.body.free captures ∧ Defaults.Body.CaptureCells active captures :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Escape.Scoped.activate_installs
    plan childId caller assigned

/-- Repeated source reads share one installed binding in the closure. -/
theorem capture_order {globals : List String} {spec : Spec} (plan : Plan globals spec)
    {active : State} {captures : List Capture} (installed : Installs active plan.body.free captures) :
    captures.map Capture.binding = (plan.body.declaration spec.wrapper.codes).free.map FreeName.target ∧
      (captures.map Capture.binding).Nodup :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Escape.Scoped.capture_order plan installed

/-- A reached return restores the caller and leaves the saved defaults and
ordered vector in the escaped closure. Rebinding writes the original
wrapper cell, and the vector supplies the compositional child frame. -/
theorem returned_frame {globals : List String} {spec : Spec} (names : Names spec)
    (plan : Plan globals spec) (program : Program) (available : List DeclarationId) (childId : Nat)
    (found : program[childId]? = some (plan.body.declaration spec.wrapper.codes))
    (caller : State) (assigned : List (Binding × Lists.Value)) {address : Nat} {next : State}
    (source : Escape.ReturnsWith spec.wrapper childId plan.body.free caller
      (activate caller (spec.frame childId).declaration [] assigned) (.ok (.function address) next)) :
    let active := activate caller (spec.frame childId).declaration [] assigned
    ∃ values captures, values.length = spec.child.parameters.optional.length ∧
      Installs active plan.body.free captures ∧
      next.heap[address]? = some ⟨.function ⟨childId, captures, spec.wrapper.saved values⟩, false⟩ ∧
      next.slots = caller.slots ∧ next.bindings = caller.bindings ∧
      (∀ parameter before frozen,
        active.slots (fileSlot spec.wrapper.parameter) = some (.owned parameter) →
        active.heap[parameter]? = some ⟨.binding before, frozen⟩ →
        next.heap[parameter]? = some ⟨.binding (some (.scalar (.int spec.wrapper.rebound))), frozen⟩) ∧
      ∀ arguments : List (Binding × Lists.Value),
        Defaults.Body.Frame plan.body.block plan.body.free next.heap.size
          (activate next (plan.body.declaration spec.wrapper.codes) captures arguments) :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Escape.Scoped.returned_frame
    names plan program available childId found caller assigned source

end Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Escape.Scoped
