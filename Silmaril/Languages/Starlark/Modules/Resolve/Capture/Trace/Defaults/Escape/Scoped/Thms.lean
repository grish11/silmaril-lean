module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Escape.Scoped.Defs
public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Body.Thms
import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Escape.Scoped.Frame

public section

namespace Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Escape.Scoped

open Block (ModuleBinders)
open Functions
open Lists (State)

/-- Checked source emits the independently ordered capture list as part
of the child declaration at its actual index in the final program. -/
theorem checked_site {before after : List Command} {globals : List String} {spec : Spec}
    {linked : Program} {resolved : ResolvedModule} (names : Escape.WrapperNames spec.wrapper)
    (plan : Plan globals spec) (declared : ModuleBinders (before ++ spec.command :: after) globals)
    (checked : resolve (before ++ spec.command :: after) linked = .ok resolved)
    (suffix : RootCall.Segment globals after) :
    ∃ id, resolved.source.commands[before.length]? = some (.exec (.define spec.wrapper.name (id + 1))) ∧
      resolved.program[id]? = some (plan.body.declaration spec.wrapper.codes) ∧
      resolved.program[id + 1]? = some (spec.wrapper.frame id).declaration :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Escape.Scoped.checked_site
    names plan declared checked suffix

/-- A reached wrapper return restores the caller and leaves the exact
saved arguments and local-cell capture in the escaped closure. With any
positional binding, child activation supplies the compositional body frame. -/
theorem returned_frame {globals : List String} {spec : Spec} (names : Escape.WrapperNames spec.wrapper)
    (plan : Plan globals spec) (program : Program) (available : List DeclarationId) (childId : Nat)
    (found : program[childId]? = some (plan.body.declaration spec.wrapper.codes))
    (caller : State) (argument : Lists.Value) {address : Nat} {next : State}
    (source : Escape.ReturnsWith spec.wrapper childId plan.body.free caller argument (.ok (.function address) next)) :
    ∃ values, values.length = spec.child.parameters.optional.length ∧
      next.heap[address]? = some ⟨.function ⟨childId, capturesAt spec caller.heap.size, spec.wrapper.saved values⟩, false⟩ ∧
      next.heap[caller.heap.size]? = some ⟨.binding (some (.scalar (.int spec.wrapper.rebound))), false⟩ ∧
      next.slots = caller.slots ∧ next.bindings = caller.bindings ∧
      ∀ assigned : List (Binding × Lists.Value),
        Defaults.Body.Frame plan.body.block plan.body.free next.heap.size
          (activate next (plan.body.declaration spec.wrapper.codes) (capturesAt spec caller.heap.size) assigned) :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Escape.Scoped.returned_frame
    names plan program available childId found caller argument source

end Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Escape.Scoped
