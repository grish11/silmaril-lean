module

public import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Escape.Scoped.Site
public import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Escape.Run
public import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Body.Frame

public section

namespace Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Escape.Scoped

open Silmaril.Languages.Starlark (Binding)
open Silmaril.Languages.Starlark.Modules (fileSlot)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Escape.Scoped
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace
open Silmaril.Languages.Starlark.Functions
open Silmaril.Languages.Starlark.Lists (State Value)

theorem installs_at {globals : List String} {spec : Spec} (plan : Plan globals spec)
    (state : State) (address : Nat)
    (owned : state.slots (fileSlot spec.wrapper.parameter) = some (.owned address)) :
    Installs state plan.body.free (capturesAt spec address) := by
  rw [plan.captured]
  exact .cons (.enclosing owned) .nil

theorem returned_cells (spec : Spec) (next : State) (address : Nat)
    (rebound : next.heap[address]? = some ⟨.binding (some (.scalar (.int spec.wrapper.rebound))), false⟩) :
    Defaults.Body.CaptureCells next (capturesAt spec address) := by
  intro capture member
  have same : capture = ⟨fileSlot spec.wrapper.parameter, address, true⟩ := List.mem_singleton.mp member
  subst capture
  exact ⟨_, _, rebound⟩

theorem returned_frame {globals : List String} {spec : Spec} (names : Defaults.Escape.WrapperNames spec.wrapper)
    (plan : Plan globals spec) (program : Program) (available : List DeclarationId) (childId : Nat)
    (found : program[childId]? = some (plan.body.declaration spec.wrapper.codes))
    (caller : State) (argument : Value) {address : Nat} {next : State}
    (source : Defaults.Escape.ReturnsWith spec.wrapper childId plan.body.free caller argument
      (.ok (.function address) next)) :
    ∃ values, values.length = spec.child.parameters.optional.length ∧
      next.heap[address]? = some ⟨.function ⟨childId, capturesAt spec caller.heap.size, spec.wrapper.saved values⟩, false⟩ ∧
      next.heap[caller.heap.size]? = some ⟨.binding (some (.scalar (.int spec.wrapper.rebound))), false⟩ ∧
      next.slots = caller.slots ∧ next.bindings = caller.bindings ∧
      ∀ assigned : List (Binding × Value),
        Defaults.Body.Frame plan.body.block plan.body.free next.heap.size
          (activate next (plan.body.declaration spec.wrapper.codes) (capturesAt spec caller.heap.size) assigned) := by
  obtain ⟨_, _, independently, _, _, progress⟩ := Defaults.Escape.returns_with_total program available spec.wrapper names
    childId (plan.body.declaration spec.wrapper.codes) found rfl caller argument (capturesAt spec caller.heap.size)
    (fun state owned => installs_at plan state _ owned)
  obtain ⟨actual, values, same, count, cell, rebound, kept, defining, installed⟩ :=
    progress _ _ (Defaults.Escape.returns_with_unique independently source)
  cases same
  refine ⟨values, count, cell, rebound, kept.slots, ?_, ?_⟩
  · cases source
    rfl
  · intro assigned
    exact Defaults.Body.captured_frame plan.body _ (Defaults.Escape.code_length spec.wrapper) next defining _
      installed (returned_cells spec next caller.heap.size rebound) assigned

end Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Escape.Scoped
