module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Escape.Defs
public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Leaf.Thms
import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Escape.Run

public section

namespace Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Escape

open Functions
open Lists (State Outcome)
open Lists.Iteration (Flow)
open Block (ModuleBinders)

/-- The reached wrapper activation allocates distinct fresh cells for its
argument and its unbound child name. -/
theorem frame_layout (wrapper : Spec) (admitted : Admitted wrapper) (childId : Nat)
    (caller : State) (argument : Lists.Value) :
    let frame := activate caller (wrapper.frame childId).declaration [] [(fileSlot wrapper.parameter, argument)]
    frame.slots (fileSlot wrapper.parameter) = some (.owned caller.heap.size) ∧
    frame.heap[caller.heap.size]? = some ⟨.binding (some argument), false⟩ ∧
    frame.slots (fileSlot wrapper.childName) = some (.owned (caller.heap.size + 1)) ∧
    frame.heap[caller.heap.size + 1]? = some ⟨.binding none, false⟩ :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Escape.frame_layout wrapper admitted childId caller argument

/-- A failed nested default leaves its reached wrapper argument and
unbound child cell in the residual heap and restores the caller. -/
theorem failed_child_unbound (wrapper : Spec) (admitted : Admitted wrapper) (childId : Nat)
    (caller : State) (argument : Lists.Value) {error : Lists.Error} {next : State}
    (failed : Returns wrapper childId caller argument (.error error next)) :
    next.heap[caller.heap.size]? = some ⟨.binding (some argument), false⟩ ∧
    next.heap[caller.heap.size + 1]? = some ⟨.binding none, false⟩ ∧
    next.slots = caller.slots ∧ next.bindings = caller.bindings :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Escape.failed_child_unbound
    wrapper admitted childId caller argument failed

/-- Checked source links the child and wrapper at their successive final
declaration indices, even with later supported commands. -/
theorem checked_site {before after : List Command} {globals : List String} {wrapper : Spec}
    {linked : Program} {resolved : ResolvedModule} (admitted : Admitted wrapper)
    (declared : ModuleBinders (before ++ wrapper.command :: after) globals)
    (checked : resolve (before ++ wrapper.command :: after) linked = .ok resolved)
    (suffix : RootCall.Segment globals after) :
    ∃ childId, resolved.source.commands[before.length]? = some (.exec (.define wrapper.name (childId + 1))) ∧
      resolved.program[childId]? = some (wrapper.child.emitted wrapper.codes) ∧
      resolved.program[childId + 1]? = some (wrapper.frame childId).declaration :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Escape.checked_site admitted declared checked suffix

/-- The independent wrapper result gives the exact operational and
denotational body result and its restored caller observation. -/
theorem returns_agree (program : Program) (available : List DeclarationId) (wrapper : Spec)
    (admitted : Admitted wrapper) (childId : Nat) (found : program[childId]? = some (wrapper.child.emitted wrapper.codes))
    (caller : State) (argument : Lists.Value) {out : Outcome Lists.Value} (source : Returns wrapper childId caller argument out) :
    let active := activate caller (wrapper.frame childId).declaration [] [(fileSlot wrapper.parameter, argument)]
    ∃ bodyOut : Outcome Flow, Exec program available active (wrapper.frame childId).code bodyOut ∧
      denoteBody program available (wrapper.frame childId).code active = bodyOut ∧
      Leaf.returnTo caller bodyOut = out := by
  obtain ⟨result, executed, observed⟩ := Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Escape.returns_sound
    program available wrapper admitted childId found caller argument source
  exact ⟨result, executed, (exec_iff_denoteBody _ _ _ _ _).mp executed, observed⟩

/-- The returned address keeps the saved values even after the distinct
parameter cell has been rebound and the caller has been restored. -/
theorem returned_record (program : Program) (available : List DeclarationId) (wrapper : Spec)
    (admitted : Admitted wrapper) (childId : Nat) (found : program[childId]? = some (wrapper.child.emitted wrapper.codes))
    (caller : State) (argument : Lists.Value) {address : Nat} {next : State}
    (source : Returns wrapper childId caller argument (.ok (.function address) next)) :
    ∃ defaults, defaults.length = wrapper.child.parameters.optional.length ∧
      next.heap[address]? = some ⟨.function ⟨childId, [], wrapper.saved defaults⟩, false⟩ ∧
      next.heap[caller.heap.size]? = some ⟨.binding (some (.scalar (.int wrapper.rebound))), false⟩ ∧
      next.slots = caller.slots ∧ next.bindings = caller.bindings :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Escape.returned_record
    program available wrapper admitted childId found caller argument source

end Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Escape
