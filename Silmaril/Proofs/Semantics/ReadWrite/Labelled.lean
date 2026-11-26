module

public import Silmaril.Semantics.ReadWrite.Labelled.Defs

public section
namespace Silmaril.Proofs.Semantics.ReadWrite

open Silmaril.Semantics.ReadWrite Silmaril.Semantics.Operational

universe u v w
variable {Address : Type u} {Value : Type v} {State : Type w}
variable {access : Access Address Value State} {trace : Trace Address Value} {initial final : State}

theorem replays_iff_path :
    trace.Replays access initial final ↔ access.labelled.Path initial trace final := by
  constructor
  · intro run
    induction trace generalizing initial with
    | nil =>
      change initial = final at run
      cases run
      exact .nil _
    | cons event rest ih =>
      cases event with
      | read => exact .visible ⟨run.1, rfl⟩ (ih run.2)
      | write =>
        obtain ⟨target, write, tail⟩ := run
        exact .visible write (ih tail)
  · intro path
    induction path with
    | nil => rfl
    | silent impossible _ _ => exact False.elim impossible
    | visible step path ih =>
      rename_i label
      cases label with
      | read =>
        obtain ⟨read, rfl⟩ := step
        exact ⟨read, ih⟩
      | write => exact ⟨_, step, ih⟩

end Silmaril.Proofs.Semantics.ReadWrite
